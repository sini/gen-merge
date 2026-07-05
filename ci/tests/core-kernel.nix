# Fixed-input core kernel (design spec §2.5) — the opt-in `coreShortCircuit` short-circuit.
#
# Acceptance (plan Task 6): with a CORRECT core, `evalModuleTree { coreShortCircuit = true; }` is
# byte-identical (toJSON eq) to the full merge on rehost-shaped fixtures (nested options, attrsOf,
# priorities); a WRONG core diverges (the comparison has teeth); a core def competing with a real
# def falls through to the full merge; default-off treats the marker as an ordinary attrset (ZERO
# behaviour change — covered engine-wide by the untouched 75-test suite + this file's off-path tests).
#
# FIRING PROOF (deterministic, not perf-only): a leaf type whose `.merge`/`.verify` THROWS. With the
# kernel on, a sole core def returns `values` and the throwing spine never runs; with it off, the
# same modules throw. This proves the discharge/fold/verify spine is genuinely SKIPPED, independent
# of the counter numbers below.
#
# COUNTER EVIDENCE (informational — the perf gate is plan Task 9). Biggest fixture = the `anything`
# leaf whose full definition is an `mkMerge` of N=24 attrset pieces (an expensive recursive
# `mergeAnythingVals` fold); the core variant supplies the pre-merged value, skipping the fold.
# Measured with `NIX_SHOW_STATS=1 nix-instantiate --eval --strict` forcing each whole config:
#   full (coreShortCircuit off) : nrFunctionCalls = 2921   nrThunks = 2947   nrPrimOpCalls = 977
#   core (coreShortCircuit on)  : nrFunctionCalls =  623   nrThunks = 1069   nrPrimOpCalls = 306
# ⇒ 78.7% fewer function calls / 63.7% fewer thunks on THIS fixture — the discharge/fold/verify
# spine is genuinely skipped (the deterministic firing proof below confirms it independent of these).
{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm)
    evalModuleTree
    mkOption
    mkOptionType
    mkCoreValue
    mkMerge
    mkForce
    ;
  t = gm.types;
  toJSON = builtins.toJSON;
  cfg = args: (evalModuleTree args).config;

  # ── rehost-shaped skeleton ────────────────────────────────────────────────
  # nested declared options (a.b.c), an attrsOf collection, a priority-resolved leaf (mkForce over a
  # bare def), AND one `shared` leaf of type `anything`. `sharedDef` is spliced at the `shared` leaf:
  # the FULL variant defines it via `mkMerge` of many pieces (recursive fold); the CORE variant
  # supplies the pre-merged value via `mkCoreValue` (sole def ⇒ the fold is short-circuited). Every
  # other loc is identical, so the whole-config comparison also proves the flag disturbs nothing else.
  N = 24;
  pieces = builtins.genList (i: {
    "k${toString i}" = {
      v = i;
      tag = "t${toString i}";
    };
  }) N;
  sharedMerged = builtins.foldl' (a: b: a // b) { } pieces;

  skeleton = sharedDef: [
    {
      options.a.b.c = mkOption {
        type = t.int;
        default = 1;
      };
      options.coll = mkOption {
        type = t.attrsOf t.str;
        default = { };
      };
      options.p = mkOption { type = t.str; };
      options.shared = mkOption { type = t.anything; };
    }
    { config.a.b.c = 7; }
    {
      config.coll.x = "X";
      config.coll.y = "Y";
    }
    { config.p = mkForce "forced"; }
    { config.p = "bare"; }
    { config.shared = sharedDef; }
  ];

  fullDef = mkMerge pieces;
  coreDef = mkCoreValue {
    digest = "correct";
    values = sharedMerged;
  };
  wrongDef = mkCoreValue {
    digest = "wrong";
    values = sharedMerged // {
      k0 = {
        v = 999;
        tag = "WRONG";
      };
    };
  };

  fullCfg = cfg { modules = skeleton fullDef; }; # coreShortCircuit defaults off
  coreCfg = cfg {
    modules = skeleton coreDef;
    coreShortCircuit = true;
  };
  wrongCfg = cfg {
    modules = skeleton wrongDef;
    coreShortCircuit = true;
  };

  # ── deterministic firing proof — a throwing spine ─────────────────────────
  boomType = mkOptionType {
    name = "boom";
    merge = loc: _defs: throw "SPINE-RAN at ${gm.showOption loc}";
  };
  soleCoreThrow =
    coreSC:
    {
      modules = [
        { options.z = mkOption { type = boomType; }; }
        {
          z = mkCoreValue {
            digest = "d";
            values = "SKIPPED";
          };
        }
      ];
    }
    // (if coreSC then { coreShortCircuit = true; } else { });
  # 2 defs at `z` ⇒ fall-through ⇒ the throwing `.merge` DOES run (fall-through never skips the spine).
  fallThroughThrows = {
    modules = [
      { options.z = mkOption { type = boomType; }; }
      {
        z = mkCoreValue {
          digest = "d";
          values = "A";
        };
      }
      { z = "B"; }
    ];
    coreShortCircuit = true;
  };
  throws = args: (builtins.tryEval (builtins.deepSeq (cfg args) null)).success == false;

  # ── fall-through parity (core marker + competing def == plain values + competing def) ──
  # `anything` leaf `fo` with a core marker and a second real def ⇒ fall-through unwraps the marker to
  # its `values` (plain def) and merges normally; reference supplies `values` directly. Byte-identical.
  fallThroughCfg =
    coreSC: valAtFo:
    cfg (
      {
        modules = [
          { options.fo = mkOption { type = t.anything; }; }
          { fo = valAtFo; }
          {
            fo = {
              b = 2;
            };
          }
        ];
      }
      // (if coreSC then { coreShortCircuit = true; } else { })
    );
  ftCore = fallThroughCfg true (mkCoreValue {
    digest = "d";
    values = {
      a = 1;
    };
  });
  ftRef = fallThroughCfg false { a = 1; };

  # priority fall-through: a core marker (bare prio) loses to a competing mkForce — reference uses the
  # plain values def against the same mkForce. Both resolve to the forced value.
  prioCore = cfg {
    modules = [
      { options.s = mkOption { type = t.str; }; }
      {
        s = mkCoreValue {
          digest = "d";
          values = "lo";
        };
      }
      { s = mkForce "hi"; }
    ];
    coreShortCircuit = true;
  };
  prioRef = cfg {
    modules = [
      { options.s = mkOption { type = t.str; }; }
      { s = "lo"; }
      { s = mkForce "hi"; }
    ];
  };

  # ── default-off: the marker is an ORDINARY value (not interpreted) ─────────
  offCfg = cfg {
    modules = [
      { options.w = mkOption { type = t.anything; }; }
      {
        w = mkCoreValue {
          digest = "d";
          values = {
            real = 1;
          };
        };
      }
    ];
  };
in
{
  flake.tests.core-kernel = {
    # PARITY — with-core == full-merge, byte-identical on the whole rehost-shaped config.
    test-core-byte-identical-to-full-merge = {
      expr = toJSON coreCfg == toJSON fullCfg;
      expected = true;
    };
    # the shared leaf itself reconstructs the designed merged value.
    test-core-shared-leaf-reconstructs = {
      expr = coreCfg.shared == sharedMerged;
      expected = true;
    };
    # untouched locs (nested option, collection, priority winner) survive the flag unchanged.
    test-core-leaves-rest-untouched = {
      expr = {
        inherit (coreCfg) a;
        inherit (coreCfg) coll;
        inherit (coreCfg) p;
      };
      expected = {
        a.b.c = 7;
        coll = {
          x = "X";
          y = "Y";
        };
        p = "forced";
      };
    };

    # TEETH — a WRONG core diverges; the byte comparison catches it (else parity is vacuous).
    test-wrong-core-diverges = {
      expr = toJSON wrongCfg == toJSON fullCfg;
      expected = false;
    };
    # the wrong values are returned VERBATIM (proves short-circuit returned `values`, not a merge).
    test-wrong-core-returns-values-verbatim = {
      expr = wrongCfg.shared.k0;
      expected = {
        v = 999;
        tag = "WRONG";
      };
    };

    # FIRING — the throwing spine is skipped ONLY when the kernel is on (deterministic proof).
    test-sole-core-skips-throwing-spine = {
      expr = (cfg (soleCoreThrow true)).z;
      expected = "SKIPPED";
    };
    test-off-runs-throwing-spine = {
      expr = throws (soleCoreThrow false);
      expected = true;
    };
    test-fall-through-runs-spine = {
      expr = throws fallThroughThrows;
      expected = true;
    };

    # FALL-THROUGH parity — marker + competing def == plain values + competing def.
    test-fall-through-byte-identical = {
      expr = toJSON ftCore == toJSON ftRef;
      expected = true;
    };
    test-fall-through-merges = {
      expr = ftCore.fo;
      expected = {
        a = 1;
        b = 2;
      };
    };
    test-fall-through-priority = {
      expr = prioCore.s == prioRef.s && prioCore.s == "hi";
      expected = true;
    };

    # DEFAULT-OFF — the marker passes through as an ordinary attrset (no interpretation).
    test-default-off-marker-is-plain-value = {
      expr = offCfg.w;
      expected = {
        __coreValue = true;
        digest = "d";
        values = {
          real = 1;
        };
      };
    };
  };
}
