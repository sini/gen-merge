# A TYPE'S DOCUMENTATION EVALUATION IS NIXPKGS' (den-hoag-docs-check-module-parity-47pw5, ADR-0039). nixpkgs'
# `getSubOptions` evaluates a submodule over `[ placeholder ] ++ modules ++ [ noCheckForDocsModule ]`, the last of
# which is `config._module.check = mkForce false`. gen-merge's documentation evaluation (`substructure.declares`, at
# `mkSubmodule` and at `typeOver`) lists nixpkgs' literal module before its name placeholder, so a module reading
# `_module.check` there reads `false` and the evaluation's `moduleType` lists the module where nixpkgs' does
# (`./_fixtures/docs-evaluation.nix`).
#
# One cell per variant × read, on gen's engine (`gm`) and on the export bridge (`bx`), each expecting nixpkgs' value.
# A read that refuses reads `<error>` on either side. RED before the landing: 32 of 62 cells per arm, every `sm*` and
# `chk*` cell. The names, description, freeform and child cells are guards that the docs module moves nothing else.
#
# Cells the landing moved, 14, read against nixpkgs' twin in the same run:
# - `force/{chk,chk2,chkE,chkOpt}` × gm, bx (8): served `true` where nixpkgs refuses the `_module.check` conflict, now
#   refused by name as nixpkgs refuses it.
# - `force/{sm,sm2,smE}` × gm, bx (6): served a module list where nixpkgs refuses; the documentation evaluation's
#   `options` now read through its refusal, so refused as nixpkgs refuses them.
#
# No cell is excluded: nixpkgs reads an evaluation's `options` and `nestedTypes.freeformType` through its
# unmatched-definition check, and so does gen-merge (`./checked-result-seam.nix`).
{ genMerge, nixpkgsLib, ... }:
let
  fx = import ./_fixtures/docs-evaluation.nix {
    gm = genMerge;
    np = nixpkgsLib;
  };
  cellsOf =
    arm:
    builtins.concatLists (
      builtins.attrValues (
        builtins.mapAttrs (
          variant: arms:
          map (read: {
            name = "test-${arm}-${variant}-${read}";
            value = {
              expr = arms.${arm}.${read};
              expected = arms.np.${read};
            };
          }) (builtins.attrNames arms.np)
        ) fx.table
      )
    );
in
{
  flake.tests.docs-evaluation = builtins.listToAttrs (cellsOf "gm" ++ cellsOf "bx");
}
