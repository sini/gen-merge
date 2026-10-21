# THE REPLACEMENT BAR, STAGE 2 (ADR-0039; den-hoag-fwkzx): NixOS evaluated as NixOS evaluates it, through
# nixpkgs' own `nixos/lib/eval-config.nix`, once with nixpkgs' lib and once with gen-merge's
# `evalModuleTree` in its `evalModules` (`modules-sh-lib.nix`, stage 1's construction verbatim), and scored
# per cell against a committed register (`nixos-bar-baseline.jsonl`). Cells (`nixos-bar-eval.nix`):
#
#   {kind:"toplevel", cfg}    nixos/release.nix's 8 `closures`, read to `toplevel.drvPath`
#   {kind:"options"}          release.nix's `options` job, read to `optionsJSON.drvPath`
#   {kind:"docs-walk"}        the docs walk over the `options` job's evaluation: its cost row
#   {kind:"doc", name, n}     one node of that walk, nixpkgs' own `optionAttrSetToDocList` entry
#
# Verdicts are stage 1's: PASS, PASS-CLASS, FAIL (`nixos-bar-compare.jq`). A toplevel or options PASS is
# the IDENTITY of one derivation, never equivalence of the evaluation (ADR-0039: "drvPath equality is
# evidence and never acceptance"), so those rows carry `"claim":"identity"` and the stage's acceptance is
# counted over `doc` rows only.
#
# PERF. Each perf row (toplevel, options, docs-walk) carries, per evaluator `--version` line, both arms'
# `nrThunks`, attributed bytes (`envs + list + sets + values + symbols` `.bytes`) and wall `ms`, read in
# the process that computed the verdict. The bound is EXACT on gen's thunks and bytes (ADR-0032): above it
# is COST-REGRESSED, below it COST-RATCHET (lower the bound in the same change), a row with no entry for
# this evaluator UNANCHORED; all three are disagreements. `ms` is recorded, never compared. A refused arm
# writes no stats file, so its perf is null. Parity (gen <= ref on both counters) is printed per row as
# at-parity / above-parity. above-parity is the bar's perf criterion (perf <= nixpkgs) NOT MET, even where
# CI stays green because the ratchet admitted the rise under ADR-0032: admitted is not approved.
#
# A PROCESS-PLANE program for the reason `tests-process.nix` gives: each verdict is an exit plus a value,
# evidence only for the evaluator that computed it, so it calls the `nix-instantiate` on PATH and carries
# none in its closure. Every evaluation runs `--readonly-mode`.
#
#   nixos-bar                        run and score; exit 1 on any disagreement with the register
#   nixos-bar --write-baseline F     run and write the register to F, this evaluator's perf merged
#   nixos-bar --fold F LOG...        no evaluation: the register with the `PERF` lines of LOG... (CI's
#                                    three column logs) merged in, written to F
#
# THE REGISTER IS WRITTEN UNDER THE BINARIES THAT JUDGE. CI's evaluators are gen-harness's pins, which
# `engine-pins.nix` holds coherent with its engine inputs; a local build of those differs from CI's only in
# build provenance, which is not measured, so the anchors come from CI itself: a `workflow_dispatch` run
# of the branch prints one `PERF` line per perf row in each column, `--fold` writes them, the fold is
# committed, and the landing run reads 0 disagreements in all three columns.
#
# EVERY gen-merge lib/ change that moves a count reds this arm until the register is rewritten in the
# same change (ADR-0032: "an optimization lowers the bound in the same change"), and a rise is admitted
# only through the ratchet (`modules-sh-ratchet.sh`, trailer `Bar-Perf-Rise:`). Two units in flight on
# the surface this arm reads (`den-hoag-options-checked-wrapper-mly8e` reshapes how an evaluation's
# `.options` is read): the SECOND to land rewrites the register over the first, because the register is
# per-revision exact and only the second lander's tree is the one it describes.
#
# COST: as `modules-sh.nix`'s: the process-plane step's budget is 20 minutes per column; a run over it is
# not a red, and its remedy is sharding inside the process plane. The whole run has a deadline
# (NIXOS_BAR_DEADLINE, seconds, default 3600) and each evaluation 1200 s.
{ pkgs, inputs }:
let
  # Strings, not path literals: a path interpolated into a string is copied to the store, which
  # `--readonly-mode` refuses.
  srcs = pkgs.writeText "nixos-bar-srcs.nix" ''
    {
      nixpkgs = "${inputs.nixpkgs}";
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
  '';
in
pkgs.writeShellApplication {
  name = "nixos-bar";
  # Never an evaluator: every evaluation calls the column's `nix-instantiate`, from PATH.
  runtimeInputs = [
    pkgs.bash
    pkgs.coreutils
    pkgs.gnugrep
    pkgs.gnused
    pkgs.jq
  ];
  text = ''
    export NIXOS_BAR_EVAL=${./nixos-bar-eval.nix} NIXOS_BAR_SRCS=${srcs}
    export NIXOS_BAR_COMPARE=${./nixos-bar-compare.jq} NIXOS_BAR_DOCS=${./nixos-bar-docs.jq}
    export NIXOS_BAR_RATCHET=${./modules-sh-ratchet.jq} NIXOS_BAR_BASE=${./nixos-bar-baseline.jsonl}
    export NIXOS_BAR_NIXPKGS=${inputs.nixpkgs.rev or inputs.nixpkgs.narHash}
    # shellcheck disable=SC1091
    source ${./nixos-bar.bash}
  '';
}
