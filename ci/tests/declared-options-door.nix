# THE STRATUM-1 DOOR PUBLISHES THE EVALUATION'S OWN DECLARATIONS (den-hoag-qqywn, ADR-0033 as amended,
# ADR-0039). `declaredOptions` reads the value path's declarations (`evalModuleTreeWith`'s declaring knot), so
# a nixpkgs-grammar declaration that reads `options`, a module argument or `config` is served there as
# nixpkgs' fold serves it, and each record carries nixpkgs' `fixupOptionType` type (`servedType`).
# Every cell reads one fixture through the door, the value path and nixpkgs, and every read is catchable
# (`? type` before `.type`), so a door record with no type reads `<none>` and never aborts the suite.
#
# RED: the door's previous body, the stratum-1 fold alone (`declarationsOf`), refuses the rename, argument,
# presence and descriptor arms and reads `<none>` on the untyped and `_module.specialArgs` arms; dropping
# `servedType`'s module-set arm (the declaration's own `v.type`) reads `<nofile>` on the two submodule arms.
# The gen-typed presence read stays refused on the door (`ci/tests-error.nix`, `declared-options-door`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  sa = {
    lib = nl;
  };
  three = ms: rd: [
    (rd (gm.declaredOptions { specialArgs = sa; } ms))
    (rd (gm.evalModuleTree { specialArgs = sa; } ms).options)
    (rd
      (nl.evalModules {
        modules = ms;
        specialArgs = sa;
      }).options
    )
  ];
  tyName = o: if o ? type then o.type.name else "<none>";
  subFiles = o: map (m: m._file or "<nofile>") o.type.getSubModules;
  int = nl.mkOption {
    type = nl.types.int;
    default = 1;
  };
  untyped = [ { options.u = nl.mkOption { }; } ];
in
{
  flake.tests.declared-options-door = {
    # door, value path, nixpkgs
    test-an-untyped-declaration-reads-unspecified = {
      expr = three untyped (o: tyName o.u);
      expected = [
        "unspecified"
        "unspecified"
        "unspecified"
      ];
    };
    test-module-specialArgs-reads-unspecified = {
      expr = three untyped (o: tyName o._module.specialArgs);
      expected = [
        "unspecified"
        "unspecified"
        "unspecified"
      ];
    };
    # an alias leaf copies its target's type: a declaration reading `options`
    test-a-renamed-option-reads-its-target-type = {
      expr = three [
        (nl.mkRenamedOptionModule [ "a" ] [ "b" ])
        { options.b = int; }
      ] (o: tyName o.a);
      expected = [
        "int"
        "int"
        "int"
      ];
    };
    # `with utils;`: a declaration built from a module argument the configuration defines
    test-a-declaration-from-a-module-argument-is-served = {
      expr = three [
        { _module.args.u.mk = int; }
        ({ u, ... }: { options.c = u.mk; })
      ] (o: tyName o.c);
      expected = [
        "int"
        "int"
        "int"
      ];
    };
    # a nixpkgs-grammar declaration whose presence reads `config`
    test-a-declaration-whose-presence-reads-config-is-served = {
      expr = three [
        {
          options.b = nl.mkOption {
            type = nl.types.bool;
            default = true;
          };
        }
        ({ config, ... }: { options.c = if config.b then { d = int; } else { }; })
      ] (o: builtins.attrNames o.c);
      expected = [
        [ "d" ]
        [ "d" ]
        [ "d" ]
      ];
    };
    # a descriptor field reading `config`
    test-a-default-reading-config-is-served = {
      expr = three [
        {
          options.b = nl.mkOption {
            type = nl.types.str;
            default = "x";
          };
        }
        (
          { config, ... }:
          {
            options.c = nl.mkOption {
              type = nl.types.str;
              default = config.b;
            };
          }
        )
      ] (o: o.c.default);
      expected = [
        "x"
        "x"
        "x"
      ];
    };
    # one typed declaration's module set is located at its declaring file (nixpkgs' `fixupModuleSets`)
    test-a-nixpkgs-submodule-locates-its-modules = {
      expr = three [
        {
          _file = "/real/S.nix";
          options.s = nl.mkOption {
            type = nl.types.submodule { options.x = int; };
            default = { };
          };
        }
      ] (o: subFiles o.s);
      expected = [
        [ "/real/S.nix" ]
        [ "/real/S.nix" ]
        [ "/real/S.nix" ]
      ];
    };
    test-a-gen-submodule-locates-its-modules = {
      expr = three [
        {
          _file = "/real/S.nix";
          options.s = gm.mkOption {
            type = gm.types.submodule {
              options.x = gm.mkOption {
                type = gm.types.int;
                default = 1;
              };
            };
            default = { };
          };
        }
      ] (o: subFiles o.s);
      expected = [
        [ "/real/S.nix" ]
        [ "/real/S.nix" ]
        [ "/real/S.nix" ]
      ];
    };
  };
}
