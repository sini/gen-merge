# THE REPLACEMENT BAR, STAGE 3 (ADR-0039; den-hoag-stage3-home-manager-nk0o6): home-manager's option docs and
# its test suite, evaluated by home-manager's own drivers, once with nixpkgs' lib and once with gen-merge's
# `evalModuleTree` in its `evalModules` (`modules-sh-lib.nix`), and scored per cell against a committed
# register (`hm-bar-baseline.jsonl`). It is stage 2's machinery (`nixos-bar.bash`, `nixos-bar-compare.jq`,
# `nixos-bar-docs.jq`, the ratchet) with stage 3's evaluation (`hm-bar-eval.nix`), walk (`bar-walk.nix`) and
# cells (`hm-bar-cells.bash`). Cells:
#
#   {kind:"test", name}         one test of home-manager's x86_64-linux suite (every attribute of
#                               `tests/default.nix`'s `tests`, the set its own CI chunks), read to what the
#                               generation writes; acceptance
#   {kind:"tests"}              the cost row of the whole suite's evaluations
#   {kind:"doc", set, name, n}  one published node of a docs set's walk (hm, nixos, darwin: the three sets
#                               `docs/default.nix` builds); acceptance
#   {kind:"docs-walk", set}     each walk's cost row
#
# Verdicts, perf, register, fold and ratchet are stage 2's (`nixos-bar.nix` states them). No stage-3 row
# carries `"claim":"identity"`: a test's `act` drvPath rides inside its value as evidence, and a row whose
# files agree while its `act` differs is FAIL. A refusal both arms share in text that is not gen-merge's (a
# nixpkgs alias throw, an IFD refusal) scores FAIL: the class rule that would pass it is
# den-hoag-refusal-class-consumer-throw-ovyos's, one rule for both stages.
#
# PERF NOT MET. An above-parity row is the bar's perf criterion (perf at or under nixpkgs, ADR-0032) NOT MET,
# even where CI stays green because the ratchet admitted its rise: admitted is not approved (den-hoag-06toi).
# At home-manager ec80131 every serving perf row is above parity.
#
# NOT IN THIS ARM: home-manager's NixOS and nix-darwin integration (`tests/integration`, `runTest`, whose
# verdict is a VM run), the darwin arm of the suite, and release branches (den-hoag-1as3r): the guarantee.
#
# THE TWO INPUTS this arm adds. home-manager is a REFERENCE pin (`flake.nix`), so a relock moves it with
# nixpkgs, and a tip pair that does not evaluate together shows as the reference arm refusing a control.
# `hm-bar.patch` is the arm's one change to it, applied to a copy and refused when it does not apply: the test
# driver returns nmt's argument record instead of nmt's derivations, and the docs driver exports each set's
# evaluation (`docsEval`) beside its output. nmt is home-manager's own pin: the `url` and `sha256` its test
# driver hands `fetchTarball`, read off that file's text, fetched here, at build, so no evaluation fetches.
#
# COST: the process-plane step's budget is 20 minutes per column (`modules-sh.nix`'s COST header), shared
# with stages 1 and 2 and the cells. The chunk processes run concurrently (`hm-bar-cells.bash`), which is
# the remedy that header names. The run's deadline is BAR_DEADLINE (seconds, default 3600), each evaluation
# 1200 s.
{ pkgs, inputs }:
let
  hmSrc = inputs.home-manager;
  driver = builtins.readFile "${hmSrc}/tests/default.nix";
  anchor = "nmtSrc = fetchTarball {";
  parts = builtins.split (pkgs.lib.escapeRegex anchor) driver;
  nmtPin =
    let
      m = builtins.match "[[:space:]]*url = \"([^\"]+)\";[[:space:]]*sha256 = \"([^\"]+)\";.*" (
        builtins.substring 0 400 (builtins.elemAt parts 2)
      );
    in
    if builtins.length parts != 3 then
      throw "hm-bar: '${anchor}' occurs ${
        toString ((builtins.length parts - 1) / 2)
      } times in home-manager's tests/default.nix, not once"
    else if m == null then
      throw "hm-bar: no `url` and `sha256` after '${anchor}' in home-manager's tests/default.nix"
    else
      {
        url = builtins.elemAt m 0;
        sha256 = builtins.elemAt m 1;
      };
  nmt = builtins.fetchTarball nmtPin;
  tree = pkgs.runCommand "hm-bar-tree" { } ''
    cp -r ${hmSrc} $out
    chmod -R u+w $out
    patch -d $out -p1 --forward --fuzz=0 --no-backup-if-mismatch <${./hm-bar.patch}
  '';
  # Strings, as stage 2's: no evaluation reads a path literal of its own.
  srcs = pkgs.writeText "hm-bar-srcs.nix" ''
    {
      nixpkgs = "${inputs.nixpkgs}";
      hm = "${tree}";
      nmt = "${nmt}";
      genLibFile = "${./modules-sh-lib.nix}";
      walkFile = "${./bar-walk.nix}";
      libSrc = "${../lib}";
      genPreludeSrc = "${inputs.gen-prelude}";
      genIdentitySrc = "${inputs.gen-scope.inputs.gen-identity}";
      genGraphSrc = "${inputs.gen-scope.inputs.gen-graph}";
      genTypesSrc = "${inputs.gen-types}";
      genAlgebraSrc = "${inputs.gen-types.inputs.gen-algebra}";
      genMemoSrc = "${inputs.gen-memo}";
      genScopeSrc = "${inputs.gen-scope}";
    }
  '';
in
pkgs.writeShellApplication {
  name = "hm-bar";
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
    export BAR_NAME=hm-bar BAR_EVAL=${./hm-bar-eval.nix} BAR_SRCS=${srcs}
    export BAR_COMPARE=${./nixos-bar-compare.jq} BAR_DOCS=${./nixos-bar-docs.jq}
    export BAR_RATCHET=${./modules-sh-ratchet.jq} BAR_BASE=${./hm-bar-baseline.jsonl}
    export BAR_NIXPKGS=${inputs.nixpkgs.rev or inputs.nixpkgs.narHash}
    # shellcheck disable=SC1091
    source ${./hm-bar-cells.bash}
    # shellcheck disable=SC1091
    source ${./nixos-bar.bash}
  '';
}
