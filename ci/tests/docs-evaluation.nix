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
# Cells the landing moves, 14, read against nixpkgs' twin in the same run:
# - `force/{chk,chk2,chkE,chkOpt}` × gm, bx (8): served `true` where nixpkgs refuses the `_module.check` conflict, now
#   refused by name as nixpkgs refuses it. Cells here.
# - `force/{sm,sm2,smE}` × gm, bx (6): served a module list where nixpkgs refuses, now served the list with the docs
#   module, nixpkgs still refusing. Excluded below: served beyond nixpkgs with no stated merge law, an open defect (ADR-0039
#   (b′)(i)) owned by den-hoag-options-checked-wrapper-mly8e, not a cell that works today.
#
# Excluded by name, 8 cells per arm, all owned by den-hoag-options-checked-wrapper-mly8e: nixpkgs reads an evaluation's
# `options` and `nestedTypes.freeformType` through its unmatched-definition check, which refuses `force` (the conflict)
# and `stray` (the undeclared definition) where gen-merge serves. They are `force/{names,desc,descE,ffOpts}` and
# `stray/nested`, which the landing does not move, and `force/{sm,sm2,smE}` above. They retire when that row lands.
{ genMerge, nixpkgsLib, ... }:
let
  fx = import ./_fixtures/docs-evaluation.nix {
    gm = genMerge;
    np = nixpkgsLib;
  };
  excluded =
    variant: read:
    variant == "force"
    && builtins.elem read [
      "names"
      "desc"
      "descE"
      "ffOpts"
      "sm"
      "sm2"
      "smE"
    ]
    || variant == "stray" && read == "nested";
  cellsOf =
    arm:
    builtins.concatLists (
      builtins.attrValues (
        builtins.mapAttrs (
          variant: arms:
          builtins.concatMap (
            read:
            if excluded variant read then
              [ ]
            else
              [
                {
                  name = "test-${arm}-${variant}-${read}";
                  value = {
                    expr = arms.${arm}.${read};
                    expected = arms.np.${read};
                  };
                }
              ]
          ) (builtins.attrNames arms.np)
        ) fx.table
      )
    );
in
{
  flake.tests.docs-evaluation = builtins.listToAttrs (cellsOf "gm" ++ cellsOf "bx");
}
