# THE BASE MODULE ARGUMENT `specialArgs` (den-hoag-specialargs-module-arg-b01wy, ADR-0039
# parity-defect rule (1)). nixpkgs' `doCollect` applies every module to
# `{ inherit lib options specialArgs; … } // specialArgs`, so a module reads the set its evaluation
# was called with, a submodule its type's, an extended evaluation the union; a caller's own
# `specialArgs.specialArgs` outranks it, and `_module.args.specialArgs` never does.
#
# Each cell is one request read on three engines: `expected` is nixpkgs' own `lib.evalModules`; `expr`
# is gen-merge's `evalModuleTree` (`gen`, built with no `lib`) and the replacement bar's bridge
# (`bridge`, `modules-sh-lib.nix`, built with nixpkgs' `lib`). The bridge's column is the one that
# tells how the bar's engine gets its `lib`: routed through `specialArgs`, it would serve a `lib` key
# nixpkgs' set never holds.
{
  genMerge,
  modulesShLib,
  nixpkgsLib,
  ...
}:
let
  N = nixpkgsLib;
  engines = {
    np = {
      ev = N.evalModules;
      L = N;
      sub =
        mods: args:
        N.types.submoduleWith {
          modules = mods;
          specialArgs = args;
        };
    };
    gen = {
      ev = r: genMerge.evalModuleTree (removeAttrs r [ "modules" ]) r.modules;
      L = genMerge;
      sub = mods: args: (genMerge.types.submodule mods).withArgs args;
    };
    bridge = {
      ev = modulesShLib.evalModules;
      L = modulesShLib;
      sub =
        mods: args:
        modulesShLib.types.submoduleWith {
          modules = mods;
          specialArgs = args;
        };
    };
  };
  names = builtins.attrNames;

  cells =
    E:
    let
      opt = E.L.mkOption { };
      reads = { specialArgs, ... }: { config.r = names specialArgs; };
      keysFrom =
        { specialArgs, ... }:
        {
          options = builtins.listToAttrs (
            map (k: {
              name = "k_" + k;
              value = opt;
            }) (names specialArgs)
          );
        };
      # every value the declaration stratum's `specialArgs` holds is an int; any key the engine adds aborts
      intsOnly =
        { specialArgs, ... }:
        {
          options = builtins.mapAttrs (
            _: v:
            assert builtins.isInt v;
            opt
          ) specialArgs;
        };
      child = { specialArgs, ... }: {
        options.k = opt;
        config.k = names specialArgs;
      };
      at =
        r:
        let
          res = E.ev (
            removeAttrs r [
              "read"
              "post"
            ]
          );
        in
        (r.read or (c: c.r)) ((r.post or (x: x)) res).config;
    in
    builtins.mapAttrs (_: at) {
      formal = {
        specialArgs.a = 1;
        modules = [
          { options.r = opt; }
          reads
        ];
      };
      formalEmpty.modules = [
        { options.r = opt; }
        reads
      ];
      atBound = {
        specialArgs.a = 1;
        modules = [
          { options.r = opt; }
          (
            args@{ ... }:
            {
              config.r = names args.specialArgs;
            }
          )
        ];
      };
      callerKey = {
        specialArgs.specialArgs = "CALLER";
        modules = [
          { options.r = opt; }
          ({ specialArgs, ... }: { config.r = specialArgs; })
        ];
      };
      value = {
        specialArgs.a = 7;
        modules = [
          { options.r = opt; }
          ({ specialArgs, ... }: { config.r = specialArgs.a; })
        ];
      };
      imports = {
        specialArgs.a = 1;
        modules = [
          { options.r = opt; }
          ({ specialArgs, ... }: {
            imports = if specialArgs ? a then [ { config.r = "imported"; } ] else [ ];
          })
        ];
      };
      declOpt = {
        specialArgs.a = 1;
        modules = [
          (
            { specialArgs, ... }:
            {
              options.r = opt;
              options.${builtins.head (names specialArgs)} = opt;
              config.r = names specialArgs;
            }
          )
        ];
      };
      declKeys = {
        specialArgs.a = 1;
        modules = [ keysFrom ];
        read = names;
      };
      declAssert = {
        specialArgs.a = 1;
        modules = [ intsOnly ];
        read = names;
      };
      classValue = {
        class = "nixos";
        specialArgs.a = 1;
        modules = [
          { options.r = opt; }
          reads
        ];
      };
      classImports = {
        class = "nixos";
        specialArgs.a = 1;
        modules = [
          { options.r = opt; }
          ({ specialArgs, ... }: { imports = [ { config.r = names specialArgs; } ]; })
        ];
      };
      classDeclKeys = {
        class = "nixos";
        specialArgs.a = 1;
        modules = [ keysFrom ];
        read = names;
      };
      # the declaration stratum's own set under a stated class: only a declaration-time force sees it
      classDeclAssert = {
        class = "nixos";
        specialArgs.a = 1;
        modules = [ intsOnly ];
        read = names;
      };
      moduleArgs = {
        specialArgs.a = 1;
        modules = [
          {
            options.r = opt;
            config._module.args.specialArgs = "MODULE";
          }
          reads
        ];
      };
      moduleArgsSet = {
        specialArgs.a = 1;
        modules = [
          {
            options.r = opt;
            config._module.args.specialArgs.m = 1;
          }
          reads
        ];
      };
      subDefault = {
        specialArgs.a = 1;
        modules = [
          {
            options.r = E.L.mkOption { type = E.sub [ child ] { }; };
            config.r = { };
          }
        ];
        read = c: c.r.k;
      };
      subWith = {
        specialArgs.a = 1;
        modules = [
          {
            options.r = E.L.mkOption { type = E.sub [ child ] { b = 2; }; };
            config.r = { };
          }
        ];
        read = c: c.r.k;
      };
      positioned = {
        specialArgs.a = 1;
        modules = [
          {
            options.r = E.L.mkOption {
              type = E.L.types.attrsOf (
                E.sub [
                  (
                    { specialArgs, name, ... }:
                    {
                      options.k = opt;
                      config.k = [ name ] ++ names specialArgs;
                    }
                  )
                ] { b = 2; }
              );
            };
            config.r.x = { };
          }
        ];
        read = c: c.r.x.k;
      };
      extend = {
        specialArgs.a = 1;
        modules = [
          { options.r = opt; }
          reads
        ];
        post = r: r.extendModules { specialArgs.b = 2; };
      };
      extendOwn = {
        specialArgs = {
          a = 1;
          specialArgs.w = 1;
        };
        modules = [
          { options.r = opt; }
          reads
        ];
        post = r: r.extendModules { specialArgs.b = 2; };
      };
    };

  expected = cells engines.np;
  column =
    engine:
    builtins.listToAttrs (
      map (cell: {
        name = "test-${engine}-${cell}";
        value = {
          expr = (cells engines.${engine}).${cell};
          expected = expected.${cell};
        };
      }) (names expected)
    );
in
{
  flake.tests.specialargs-module-arg =
    column "gen"
    // column "bridge"
    // {
      # Live control: a name nothing supplies is still refused, by name and catchably.
      test-an-argument-nothing-supplies-is-still-refused-control = {
        expr =
          (builtins.tryEval
            (engines.gen.ev {
              modules = [
                { options.r = genMerge.mkOption { }; }
                ({ noSuchArgument, ... }: { config.r = noSuchArgument; })
              ];
            }).config.r
          ).success;
        expected = false;
      };
    };
}
