# THE REPLACEMENT BAR, STAGE 4 (ADR-0039; den-hoag-stage4-flake-parts-3qh4l): flake-parts' own tests and
# templates, and two real flakes built on it, evaluated once with nixpkgs' lib and once with gen-merge's
# `evalModuleTree` in its `evalModules` (`modules-sh-lib.nix`), and scored per cell against a committed
# register (`fp-bar-baseline.jsonl`). It is stage 2's machinery (`nixos-bar.bash`, `nixos-bar-compare.jq`, the
# ratchet) with stage 4's evaluation (`fp-bar-eval.nix`) and cells (`fp-bar-cells.bash`). The seam is
# flake-parts' declared entrance for its engine, its `nixpkgs-lib` input: each tree's `flake.nix` is called with
# that input replaced, so nothing upstream is patched. Cells:
#
#   {kind:"unit", path}            one test of flake-parts' nix-unit suite (`dev/tests/nix-unit.nix`, every
#                                  attribute it collects to a test), read to the hash of its `expr`; acceptance
#   {kind:"memo"}                  `dev/tests/perSystem-memoize`, upstream's own test flake: `{result, traces}`,
#                                  `traces` the count of stderr lines carrying the literal upstream's check counts
#                                  (read off `dev/tests/perSystem-memoize.nix` below); acceptance
#   {kind:"template", name}        one of flake-parts' templates, read to its outputs; acceptance
#   {kind:"flake", flake, plane}   a real flake's output names (`plane` "names"); acceptance
#   {kind:"flake-drv", flake, plane}  a real flake's x86_64-linux packages / checks / devShells, each name to its
#                                  drvPath: `"claim":"identity"`, evidence and never acceptance
#
# Every row is a perf row: one process per cell per arm, the cell's own counters.
#
# THE MEMO CELL IS A VALUE CELL, a reversible default of the orchestrator's and not an owner ruling: flake-parts'
# own check asserts the trace fires exactly once, so the consumer's own assertion is the oracle, and the bar scores
# a consumer's own assertion as parity. Its FAIL is den-hoag-module-fn-reapplied-cwege's (one module function
# applied twice). The other arm, the count as perf, is recorded in the spec.
#
# PERF NOT MET. An above-parity row is the bar's perf criterion NOT MET, even where CI stays green because the
# ratchet admitted its rise under ADR-0032's exact bound: admitted is not approved (den-hoag-06toi). The arm
# landing above parity is scheduling only (owner 2026-10-23), never approval.
#
# NOT IN THIS ARM: hercules-ci-effects' `checks` and `devShells`. flake-parts' `partitionedAttrs` puts them in
# its `dev` partition, whose `extraInputsFlake` fetches `dev/flake.lock`'s nodes AT EVALUATION, on a second
# nixpkgs (a 7-7.7 GB heap per process). They carry the one surface no kept cell reaches, partitions with extra
# inputs, and are re-armed under a separate invocation once this arm is green (the spec's guarantee). Also
# not here: release branches, Darwin systems' derivations, builds, further real flakes (the guarantee).
#
# THE INPUTS this arm adds, each `flake = false` and a REFERENCE pin as nixpkgs is (both arms evaluate them,
# none is a gen member or the change under test): `flake-parts-src` (flake-parts' tree, not named
# `flake-parts`, which is gen-harness' tool override), `nix-fast-build`, `hercules-ci-effects`. Every
# real flake is handed this flake-parts and gen-merge's nixpkgs; its every other input is its own lock's
# entry, fetched here by its `narHash`, at build, so no evaluation fetches. The wiring is read off each lock's
# root node, so the build refuses, naming it, a real flake lacking `flake-parts` or `nixpkgs`, and a pin whose
# own inputs do not all follow `nixpkgs`.
#
# COST: the process-plane step's budget is 20 minutes per column (`modules-sh.nix`'s COST header), shared with
# stages 1-3 and the cells. The suite cells run concurrently; the real flakes one at a time.
{ pkgs, inputs }:
let
  inherit (pkgs) lib;
  fpSrc = inputs.flake-parts-src;
  # The literal upstream's memoize check counts on stderr (`grep -c "<literal>" eval-stderr`), read off its text
  # so a change to it moves this arm loudly.
  memoCheck = builtins.readFile "${fpSrc}/dev/tests/perSystem-memoize.nix";
  memoLiteral =
    let
      m = builtins.match ".*grep -c \"([^\"]+)\" eval-stderr.*" memoCheck;
    in
    if m == null then
      throw "fp-bar: no `grep -c \"…\" eval-stderr` in flake-parts' dev/tests/perSystem-memoize.nix"
    else
      builtins.head m;
  real = {
    nfb = inputs.nix-fast-build;
    hce = inputs.hercules-ci-effects;
  };
  # The planes read of each real flake. hercules-ci-effects' `checks` and `devShells` are its `dev` partition's
  # (NOT IN THIS ARM, above).
  planes = {
    nfb = [
      "names"
      "packages"
      "checks"
      "devShells"
    ];
    hce = [
      "names"
      "packages"
    ];
  };
  wire =
    n: src:
    let
      lock = lib.importJSON "${src}/flake.lock";
      root = lock.nodes.${lock.root}.inputs;
      own = removeAttrs root [
        "flake-parts"
        "nixpkgs"
      ];
    in
    if !(root ? flake-parts && root ? nixpkgs) then
      throw "fp-bar: ${n}'s lock root has no `flake-parts' or no `nixpkgs' input (${builtins.toJSON (builtins.attrNames root)})"
    else
      {
        src = "${src}";
        planes = planes.${n};
        pins = builtins.mapAttrs (
          i: k:
          if builtins.isString k then
            pinOf n i lock.nodes.${k}
          else
            throw "fp-bar: ${n}'s input `${i}' is a follows path, not a locked node"
        ) own;
      };
  pinOf =
    n: i: node:
    let
      follows = node.inputs or { };
      bad = lib.filterAttrs (_: t: t != [ "nixpkgs" ]) follows;
    in
    if bad != { } then
      throw "fp-bar: ${n}'s input `${i}' has inputs that do not follow `nixpkgs': ${builtins.toJSON bad}"
    else
      {
        src = "${builtins.fetchTree (removeAttrs node.locked [ "lastModified" ])}";
        inherit follows;
      };
  flakes = builtins.mapAttrs wire real;
  # Strings, as stage 2's: no evaluation reads a path literal of its own.
  srcs = pkgs.writeText "fp-bar-srcs.json" (
    builtins.toJSON {
      nixpkgs = "${inputs.nixpkgs}";
      fp = "${fpSrc}";
      inherit flakes;
      genLibFile = "${./modules-sh-lib.nix}";
      libSrc = "${../lib}";
      genPreludeSrc = "${inputs.gen-prelude}";
      genIdentitySrc = "${inputs.gen-scope.inputs.gen-identity}";
      genGraphSrc = "${inputs.gen-scope.inputs.gen-graph}";
      genTypesSrc = "${inputs.gen-types}";
      genAlgebraSrc = "${inputs.gen-types.inputs.gen-algebra}";
      genMemoSrc = "${inputs.gen-memo}";
      genScopeSrc = "${inputs.gen-scope}";
    }
  );
in
pkgs.writeShellApplication {
  name = "fp-bar";
  # Never an evaluator: every evaluation calls the column's `nix-instantiate`, from PATH.
  runtimeInputs = [
    pkgs.bash
    pkgs.coreutils
    pkgs.findutils
    pkgs.gawk
    pkgs.gnugrep
    pkgs.gnused
    pkgs.jq
  ];
  text = ''
    export BAR_NAME=fp-bar BAR_EVAL=${./fp-bar-eval.nix} BAR_SRCS=${srcs}
    export BAR_COMPARE=${./nixos-bar-compare.jq}
    export BAR_RATCHET=${./modules-sh-ratchet.jq} BAR_BASE=${./fp-bar-baseline.jsonl}
    export BAR_NIXPKGS=${inputs.nixpkgs.rev or inputs.nixpkgs.narHash}
    export BAR_MEMO_LITERAL=${lib.escapeShellArg memoLiteral}
    # Stages 1-3's registers, whose kinds this stage's must not share (the compare's kind lists).
    export BAR_OTHER_REGISTERS="${./modules-sh-baseline.jsonl} ${./nixos-bar-baseline.jsonl} ${./hm-bar-baseline.jsonl}"
    # The subject roots of the shared-throw rule (`nixos-bar-compare.jq`): the code the cells evaluate.
    export BAR_ROOTS=${
      lib.escapeShellArg (
        builtins.toJSON (
          [
            "${inputs.nixpkgs}"
            "${fpSrc}"
          ]
          ++ lib.concatMap (f: [ f.src ] ++ map (p: p.src) (builtins.attrValues f.pins)) (
            builtins.attrValues flakes
          )
        )
      )
    }
    # shellcheck disable=SC1091
    source ${./fp-bar-cells.bash}
    # shellcheck disable=SC1091
    source ${./nixos-bar.bash}
  '';
}
