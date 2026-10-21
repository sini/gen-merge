# A NESTED EVALUATION PUBLISHES NIXPKGS' MODULE SET (den-hoag-1k5mi, ADR-0039). nixpkgs' `submoduleWith`
# builds a positioned child over `[ placeholder ] ++ setDefaultModuleLocation typeModules ++
# [ { _module.args.name = last loc; } ] ++ definitions` and publishes that list as the child's `moduleType`
# and as the base of its `extendModules`; over no definitions it is `[ placeholder ] ++ located typeModules`.
# gen-merge publishes the same list (`typeOver`'s `moduleSet`), so every read of it agrees with nixpkgs':
# the `name` a module sees, the `_module.args` record and the `getSubModules` labels, at each site that
# re-evaluates the set (`../_fixtures/published-module-set.nix`).
#
# One cell per variant × site × read, on gen's engine (`gm`) and on the export bridge (`bx`), each expecting
# nixpkgs' value. A read that refuses reads `<error>` on either side. RED before the landing: 53 of 108 cells
# per arm on gm and 54 on bx, the `again` record and the position after the definitions, among others.
#
# Excluded by name: the `docs` site's `getSubModules` (6 cells per arm). nixpkgs' `getSubOptions` evaluation
# lists its `noCheckForDocsModule`, which gen states nowhere; that is its own open defect
# (den-hoag-docs-check-module-parity-47pw5), and this exclusion retires when it lands.
{ genMerge, nixpkgsLib, ... }:
let
  fx = import ./_fixtures/published-module-set.nix {
    gm = genMerge;
    np = nixpkgsLib;
  };
  excluded = site: read: site == "docs" && read == "sm";
  cellsOf =
    arm:
    builtins.concatLists (
      builtins.attrValues (
        builtins.mapAttrs (
          variant: arms:
          builtins.concatLists (
            builtins.attrValues (
              builtins.mapAttrs (
                site: reads:
                builtins.concatMap (
                  read:
                  if excluded site read then
                    [ ]
                  else
                    [
                      {
                        name = "test-${arm}-${variant}-${site}-${read}";
                        value = {
                          expr = arms.${arm}.${site}.${read};
                          expected = reads.${read};
                        };
                      }
                    ]
                ) (builtins.attrNames reads)
              ) arms.np
            )
          )
        ) fx.table
      )
    );
  # A child's own `extendModules` re-evaluates over the published set, whose own modules are located, so an
  # order-reading merge reads the type's module before the definitions there too, as nixpkgs does. RED before
  # the landing: `[ "def" "def2" "q" ]`, the re-evaluation holding no root.
  extendedOrder =
    gen:
    let
      L = if gen then genMerge else nixpkgsLib;
      tm =
        { extendModules, ... }:
        {
          options.l = L.mkOption { type = L.types.listOf L.types.str; };
          options.e = L.mkOption { default = (extendModules { modules = [ ]; }).config.l; };
          config.l = [ "q" ];
        };
      mods = [
        { options.s = L.mkOption { type = L.types.submodule tm; }; }
        { s.l = [ "def" ]; }
        { s.l = [ "def2" ]; }
      ];
    in
    (if gen then genMerge.evalModuleTree { } mods else nixpkgsLib.evalModules { modules = mods; })
    .config.s.e;
in
{
  flake.tests.published-module-set = builtins.listToAttrs (cellsOf "gm" ++ cellsOf "bx") // {
    test-extendModules-reads-the-own-module-before-the-definitions = {
      expr = extendedOrder true;
      expected = extendedOrder false;
    };
    test-extendModules-reads-the-own-module-before-the-definitions-nixpkgs = {
      expr = extendedOrder false;
      expected = [
        "q"
        "def"
        "def2"
      ];
    };
  };
}
