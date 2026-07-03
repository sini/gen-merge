# config-thunk DEFERRAL parity oracle (den-hoag prerequisite, #22) — the byte-mode engine must
# carry den's `__configThunk` markers as OPAQUE, UNFORCED data through BOTH the composition merge
# AND a mid-pipeline `route`/`forward`-style re-eval, forcing them ONLY at a terminal that supplies
# the `config`/`osConfig` the thunk depends on — with the SAME result as den's `lib.evalModules`.
#
# ── den's mechanism (the thing this reproduces) ──────────────────────────────────────────────────
# A den quirk (pipe) can carry a value that depends on the FINAL rendered `config`/`osConfig`, which
# isn't known until the terminal `lib.evalModules` fixpoint. den (nix/lib/aspects/fx/assemble-pipes.nix
# `markConfigThunk`, ~:97) wraps such a config-dependent function as a marker:
#     { __configThunk = true; __fn = <fn reading config/osConfig>; __producerClass; __producerName; }
# and carries it UNFORCED through pipe assembly (the merge + the mid-pipeline route/forward evals) —
# the `idFunctor.passthrough = v: v ? __configThunk` (~:255) makes every filter/transform/fold stage
# SKIP markers. It is forced ONLY at the terminal: class-module.nix `wrapFunctionModule`'s wrapper
# (~:253) runs INSIDE `lib.evalModules`, reads `moduleArgs.config` / the owner `osConfig`, and applies
# `__fn` against them (`resolveMarkers`, ~:201), replacing the marker with the resolved value.
#
# ── minimal faithful model (this file) ───────────────────────────────────────────────────────────
# `mkThunk fn` is den's marker; `fn` reads the terminal owner (`config` / `osConfig`). We add a
# `probe = throw "forced too early"` poison payload so ANY premature forcing is directly observable
# (mirrors merge.nix `deferred.test-not-forced`). `resolveMarker` is den's `resolveMarkers`, run at
# the terminal against the fixpoint config. den carries markers in the scope-context; here they ride
# a `lazyAttrsOf raw` option (the same lazy/deferred discipline nixpkgs uses) — the deferral CONTRACT
# is identical: opaque through compose + route, forced at a terminal reading config/osConfig.
#
# ── the oracle (spec §3 style, mirrors oracle.nix) ───────────────────────────────────────────────
# The REFERENCE side runs the identical scenario through den's approach — `lib.evalModules` + real
# `lib.types` — and we assert gen-merge's resolved terminal == nixpkgs' resolved terminal, byte for
# byte. nixpkgs `lib` enters ONLY here on the reference side; the library (../lib) stays lib-free.
{ lib, genMerge, ... }:
let
  gm = genMerge;

  # Parameterized module ctors (like oracle.nix): the SAME fixture source runs on both engines.
  gmP = {
    inherit (gm) mkOption types;
  };
  npP = {
    inherit (lib) mkOption types;
  };

  stripModule = c: builtins.removeAttrs c [ "_module" ];
  gmEval = args: (gm.evalModuleTree args).config;
  npEval = args: stripModule (lib.evalModules args).config;

  # ── minimal faithful model of den's `__configThunk` ────────────────────────────────────────────
  # A config-dependent quirk value carried as an OPAQUE marker. `__fn` is the deferred function
  # reading the TERMINAL owner (config / osConfig); it is applied ONLY at the terminal. `probe` is a
  # poison thunk — forcing it means the marker was touched too early. Resolution REPLACES the marker
  # with `__fn`'s result (dropping `probe`), exactly like den's `resolveMarkers`.
  mkThunk = fn: {
    __configThunk = true;
    __fn = fn;
    probe = throw "forced too early";
  };
  # den class-module.nix `resolveMarkers` (minimal): applied at the terminal with the fixpoint
  # config + owner config. Non-markers pass through untouched. Engine-agnostic plain Nix — the SAME
  # code runs on both the gen-merge and nixpkgs sides, so any output divergence is the ENGINE's.
  resolveMarker = args: v: if v ? __configThunk then v.__fn args else v;

  # ── the fixture modules (parameterized by the engine's `P`) ────────────────────────────────────
  # `host.port` defaults to 0 during composition and is set to 8080 ONLY at the terminal — so a
  # thunk forced early (against the composition config) yields 1, but the DEFERRED terminal value is
  # 8081. That gap is what gives the teeth their bite (deferral is load-bearing, not vacuous).
  decls = P: {
    options.quirk = P.mkOption {
      type = P.types.lazyAttrsOf P.types.raw;
      default = { };
    };
    options.resolved = P.mkOption {
      type = P.types.lazyAttrsOf P.types.raw;
      default = { };
    };
    options.host.port = P.mkOption {
      type = P.types.int;
      default = 0;
    };
  };
  # producer + peer contribute config-thunk markers from TWO SEPARATE modules — so the composition
  # MERGE genuinely combines marker-bearing defs (not a single-module passthrough).
  producer = _P: {
    config.quirk.fromConfig = mkThunk ({ config, ... }: config.host.port + 1);
  };
  # `tag or throw` makes premature forcing a CATCHABLE "forced too early" (a missing-attr error is
  # NOT caught by `tryEval`); at the terminal `osConfig.tag` is present, so it never fires there.
  peer = _P: {
    config.quirk.fromOsConfig = mkThunk (
      { osConfig, ... }: "${osConfig.tag or (throw "forced too early")}-ok"
    );
  };
  # the route/forward transform: a module added during the mid-pipeline re-eval that carries a
  # further marker. It never forces the incoming markers (den's route passes markers through).
  routeModule = _P: {
    config.quirk.fromRoute = mkThunk ({ config, ... }: config.host.port + 100);
  };
  # the terminal owner: supplies the FINAL config (host.port = 8080) the config-thunks depend on.
  terminalOwner = _P: {
    config.host.port = 8080;
  };
  # the terminal resolver: den's `wrapFunctionModule` — runs inside the eval, reads the fixpoint
  # `config` + the owner `osConfig` (a module arg), and resolves each carried marker.
  resolver =
    _P:
    {
      config,
      osConfig,
      ...
    }:
    {
      config.resolved = {
        fromConfig = resolveMarker { inherit config osConfig; } config.quirk.fromConfig;
        fromOsConfig = resolveMarker { inherit config osConfig; } config.quirk.fromOsConfig;
        fromRoute = resolveMarker { inherit config osConfig; } config.quirk.fromRoute;
      };
    };

  # ── the three-stage pipeline, run identically on either engine ─────────────────────────────────
  #   stage1 — COMPOSITION MERGE (producer + peer): two modules' markers combined, carried unforced.
  #   stage2 — ROUTE/FORWARD: a fresh eval re-evaluating modules mid-stream, feeding the carried
  #            markers back in + a route module that adds another. Still nothing forced.
  #   terminal — resolves every carried marker against `config` (host.port = 8080) + `osConfig`.
  runPipeline =
    P: eval:
    let
      stage1 = eval {
        modules = [
          (decls P)
          (producer P)
          (peer P)
        ];
      };
      carried1 = stage1.quirk;

      stage2 = eval {
        modules = [
          (decls P)
          { config.quirk = carried1; }
          (routeModule P)
        ];
      };
      carried2 = stage2.quirk;

      terminal = eval {
        modules = [
          (decls P)
          { config.quirk = carried2; }
          (terminalOwner P)
          (resolver P)
        ];
        specialArgs = {
          osConfig = {
            tag = "host";
          };
        };
      };
    in
    {
      inherit
        stage1
        stage2
        carried1
        carried2
        terminal
        ;
    };

  gmRun = runPipeline gmP gmEval;
  npRun = runPipeline npP npEval;

  # The DEFERRED terminal answer both engines must agree on. fromConfig = host.port(8080)+1;
  # fromRoute = host.port(8080)+100; fromOsConfig = "${osConfig.tag}-ok".
  expectedResolved = {
    fromConfig = 8081;
    fromOsConfig = "host-ok";
    fromRoute = 8180;
  };

  # A marker forced EARLY resolves against the composition config (host.port = 0) → 1, and cannot
  # reach osConfig at all — the anti-vacuity reference points.
  forceEarly = run: key: resolveMarker { config = run.stage1; osConfig = { }; } run.stage1.quirk.${key};

  # Every carried marker's payload is STILL a poison thunk (forcing throws) — proof the composition
  # transported it as opaque data rather than resolving it.
  stillDeferred =
    carried:
    builtins.all (m: (builtins.tryEval (builtins.seq m.probe null)).success == false) (
      builtins.attrValues carried
    );
in
{
  flake.tests.deferral = {
    # AC#1/#2 — the marker survives compose(stage1) + route(stage2) as an OPAQUE marker: tag intact,
    # __fn present, and its poison payload STILL deferred (forcing it throws). Proves it was carried,
    # not coincidentally reconstructed.
    test-carried-unforced-through-composition-and-route = {
      expr =
        let
          m = gmRun.carried2.fromConfig;
        in
        m.__configThunk == true && (m ? __fn) && (builtins.tryEval (builtins.seq m.probe null)).success == false;
      expected = true;
    };

    # AC#2 — the composition MERGE combined markers from producer + peer, and the route re-eval added
    # a third; ALL survive as still-deferred markers (compose + mid-pipeline both non-forcing).
    test-composition-carries-all-markers = {
      expr =
        let
          c = gmRun.carried2;
        in
        (c ? fromConfig)
        && (c ? fromOsConfig)
        && (c ? fromRoute)
        && stillDeferred c;
      expected = true;
    };

    # AC#2 — the whole compose + route pipeline COMPLETES with no throw: deepSeq the markers' spine
    # (tags + __fn-presence, NOT the poison payloads) succeeds.
    test-composition-completes-without-throw = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq (map (m: {
            inherit (m) __configThunk;
            hasFn = m ? __fn;
          }) (builtins.attrValues gmRun.carried2)) null
        )).success;
      expected = true;
    };

    # AC#3 — forced at a terminal reading config + osConfig, every marker resolves to the expected
    # deferred value (gen-merge side).
    test-terminal-resolves-expected-gm = {
      expr = gmRun.terminal.resolved == expectedResolved;
      expected = true;
    };

    # AC#4 BYTE-PARITY — the SAME scenario through den's approach (nixpkgs `lib.evalModules` carrying
    # the marker deferred, forced at the terminal) is the REFERENCE; gen-merge is byte-identical.
    test-terminal-resolves-byte-identical = {
      expr = gmRun.terminal.resolved == npRun.terminal.resolved;
      expected = true;
    };
    test-terminal-byte-identical-and-expected = {
      expr = gmRun.terminal.resolved == npRun.terminal.resolved && npRun.terminal.resolved == expectedResolved;
      expected = true;
    };

    # AC end-to-end — a full deepSeq of the resolved terminal config forces NOTHING poisoned (the
    # terminal replaced every marker, dropping `probe`): if any stage had forced early, this throws.
    test-full-pipeline-no-early-force-gm = {
      expr = (builtins.tryEval (builtins.deepSeq gmRun.terminal.resolved null)).success;
      expected = true;
    };
    test-full-pipeline-no-early-force-np = {
      expr = (builtins.tryEval (builtins.deepSeq npRun.terminal.resolved null)).success;
      expected = true;
    };

    # ── TEETH (anti-vacuity, mirrors oracle.nix test-oracle-has-teeth-*) ──────────────────────────
    # If forcing the marker payload were a no-op, "carried unforced" would be vacuous. It is NOT:
    # forcing the poison probe THROWS.
    test-teeth-probe-forced-throws = {
      expr = (builtins.tryEval (builtins.seq gmRun.carried2.fromConfig.probe null)).success;
      expected = false;
    };

    # The deferral CHANGES the answer: forcing the config-thunk EARLY (composition config,
    # host.port = 0 ⇒ 1) does NOT equal the deferred terminal value (host.port = 8080 ⇒ 8081). So an
    # engine that forced early would be observably wrong — the byte-identical 8081 has content.
    test-teeth-force-early-diverges-from-deferred = {
      expr = (forceEarly gmRun "fromConfig") == gmRun.terminal.resolved.fromConfig;
      expected = false;
    };

    # The osConfig-thunk genuinely CANNOT be resolved mid-pipeline (no osConfig available there) —
    # forcing it early THROWS. Carrying it unforced to the terminal is the only sound behaviour.
    test-teeth-force-early-osconfig-throws = {
      expr = (builtins.tryEval (builtins.seq (forceEarly gmRun "fromOsConfig") null)).success;
      expected = false;
    };

    # The reference (nixpkgs) side has the identical teeth — proof both stacks defer the same way.
    test-teeth-force-early-diverges-np = {
      expr = (forceEarly npRun "fromConfig") == npRun.terminal.resolved.fromConfig;
      expected = false;
    };
  };
}
