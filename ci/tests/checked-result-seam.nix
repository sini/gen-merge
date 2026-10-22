# AN EVALUATION'S `options` AND `_module` ARE READ THROUGH THE REFUSAL ITS `config` CARRIES (ADR-0039). nixpkgs'
# `evalModules` returns `options`, `config` and `_module` through one forcing seam (`checked = seq checkUnmatched`),
# and `submoduleWith` reads its base evaluation's `_module.freeformType` (`nestedTypes`) and its documentation
# evaluation's (`description`, `getSubOptions`) through the same seam. gen-merge reads all of them through
# `_orphanCheck` (`../_fixtures/checked-result-seam.nix`).
#
# One cell per table × state × read, on gen's engine, each expecting nixpkgs' value. A refusal reads `<error>`, a
# missing attribute `<absent>`. RED before the landing: 97 of 242 `result` cells (the undeclared definition served
# through `options`, `_module` absent, an own `.type`'s freeform read past its base's refusal) and 6 of 49 `nested`.
{ genMerge, nixpkgsLib, ... }:
let
  fx = import ./_fixtures/checked-result-seam.nix {
    gm = genMerge;
    np = nixpkgsLib;
  };
  cellsOf =
    table:
    builtins.concatLists (
      builtins.attrValues (
        builtins.mapAttrs (
          state: reads:
          map (read: {
            name = "test-${table}-${state}-${read}";
            value = {
              expr = fx.${table}.gm.${state}.${read};
              expected = reads.${read};
            };
          }) (builtins.attrNames reads)
        ) fx.${table}.np
      )
    );
  # nixpkgs' `attrsOf` over a gen `submodule`, declared three times, the middle declaration's module only DEFINING a
  # sub-option another declares. nixpkgs' fold never evaluates that module alone, and neither may gen's: comparing the
  # declarations as type values forces no base evaluation's refusal. One module list, read by both engines. RED
  # before: gen refused ``The option `base' does not exist``.
  declaredThrice =
    let
      inherit (nixpkgsLib) mkOption types;
      sub = n: {
        options.${n} = mkOption {
          type = types.int;
          default = 0;
        };
      };
      at = extra: m: {
        options.accts = mkOption ({ type = types.attrsOf (genMerge.types.submodule m); } // extra);
      };
    in
    [
      (at { default = { }; } (sub "base"))
      (at { } { config.base = nixpkgsLib.mkDefault 5; })
      (at { } (sub "b"))
      { accts.x = { }; }
    ];
in
{
  flake.tests.checked-result-seam = builtins.listToAttrs (cellsOf "result" ++ cellsOf "nested") // {
    test-a-declaration-compared-as-a-type-forces-no-base-refusal = {
      expr = (genMerge.evalModuleTree { } declaredThrice).config.accts.x.base;
      expected = (nixpkgsLib.evalModules { modules = declaredThrice; }).config.accts.x.base;
    };
  };
}
