# THE ENGINE'S `lib` IS AN INSTANTIATION PARAMETER (den-hoag-61r97, owner-ruled S4), as nixpkgs'
# `lib/modules.nix` is `{ lib }:`. gen-merge built with a `lib` hands it to every module of every
# evaluation it makes, nested ones included; built with none (`genMerge`), it hands none.
#
# Each cell reads ONE expression on both engines: `expr` is gen-merge instantiated with nixpkgs' `lib`,
# `expected` is nixpkgs' own `lib.evalModules`, whose instance is that same `lib`. The reads name which
# `lib` arrived (`tag`), so a cell tells the instance's from a caller's from gen's own.
{
  genMerge,
  genMergeWithLib,
  nixpkgsLib,
  ...
}:
let
  N = nixpkgsLib;
  G = genMergeWithLib N;
  tag =
    l:
    if l ? marker then
      l.marker
    else if l ? evalModuleTree then
      "gen"
    else if l ? evalModules then
      "instance"
    else
      "other";
  mark = m: N // { marker = m; };
  eval =
    E: r:
    if E ? evalModuleTree then
      E.evalModuleTree (removeAttrs r [ "modules" ]) r.modules
    else
      E.evalModules r;

  # den's schema-import form: options declared through the `lib` the module receives.
  schemaImport =
    { lib, ... }:
    {
      options.weft = lib.mkOption {
        type = lib.types.str;
        default = tag lib;
      };
    };
  # the same read in the value stratum, beside a closed declaration
  valueRead = E: [
    { options.weft = E.mkOption { type = E.types.str; }; }
    ({ lib, ... }: { config.weft = tag lib; })
  ];
  sub = E: mods: {
    options.s = E.mkOption {
      type = E.types.submodule mods;
      default = { };
    };
  };
  at =
    E: specialArgs: mods:
    (eval E {
      inherit specialArgs;
      class = "nixos";
      modules = mods;
    }).config;
  doors = E: {
    root = (at E { } [ schemaImport ]).weft;
    rootValue = (at E { } (valueRead E)).weft;
    submodule = (at E { } [ (sub E [ schemaImport ]) ]).s.weft;
    attrsOfSubmodule =
      (at E { } [
        {
          options.s = E.mkOption {
            type = E.types.attrsOf (E.types.submodule [ schemaImport ]);
            default = { };
          };
        }
        { s.a = { }; }
      ]).s.a.weft;
    extendModules =
      (
        (eval E {
          class = "nixos";
          modules = [ ];
        }).extendModules
          { modules = [ schemaImport ]; }
      ).config.weft;
    # nixpkgs' `evalModules` mounting the engine's `submodule`
    bridge =
      (N.evalModules {
        modules = [ (sub E [ schemaImport ]) ];
      }).config.s.weft;
  };
  # a caller's `lib` through each inlet: it wins where nixpkgs lets it, and only there
  inlets = E: {
    specialArgsAtRoot = (at E { lib = mark "caller"; } [ schemaImport ]).weft;
    specialArgsNotInSubmodule = (at E { lib = mark "caller"; } [ (sub E [ schemaImport ]) ]).s.weft;
    moduleArgsShadowed =
      (at E { } ([ { config._module.args.lib = mark "module-args"; } ] ++ valueRead E)).weft;
    submoduleOwnArgs =
      (at E { } [
        {
          options.s = E.mkOption {
            type =
              if E ? evalModuleTree then
                (E.types.submodule [ schemaImport ]).withArgs { lib = mark "inlet"; }
              else
                E.types.submoduleWith {
                  modules = [ schemaImport ];
                  specialArgs.lib = mark "inlet";
                };
            default = { };
          };
        }
      ]).s.weft;
  };
  # `_class` and `_prefix`, as a formal and through an unlisted `@`-binder
  keys =
    E:
    let
      read =
        f:
        (at E { } [
          { options.k = E.mkOption { type = E.types.str; }; }
          f
        ]).k;
    in
    {
      classFormal = read ({ _class, ... }: { config.k = _class; });
      classUnlisted = read (
        { ... }@a:
        {
          config.k = a._class or "ABSENT";
        }
      );
      prefixFormal =
        (at E { } [ (sub E [ ({ _prefix, ... }: { options.p = E.mkOption { default = _prefix; }; }) ]) ])
        .s.p;
      prefixUnlisted =
        (at E { } [
          (sub E [
            (
              { ... }@a:
              {
                options.p = E.mkOption { default = a._prefix or "ABSENT"; };
              }
            )
          ])
        ]).s.p;
    };
  # a name only nixpkgs' `lib` carries, read through the received `lib`
  nixpkgsName =
    E:
    (at E { } [
      (sub E [
        { options.x = E.mkOption { default = "d"; }; }
        ({ lib, ... }: { config.x = lib.optionalString true "served"; })
      ])
    ]).s.x;
in
{
  flake.tests.lib-instantiation = {
    test-every-door-hands-the-instantiating-lib = {
      expr = doors G;
      expected = doors N;
    };
    test-a-caller-lib-wins-only-where-nixpkgs-lets-it = {
      expr = inlets G;
      expected = inlets N;
    };
    test-class-and-prefix-are-base-arguments = {
      expr = keys G;
      expected = keys N;
    };
    test-a-nixpkgs-only-name-reads-through-the-instantiating-lib = {
      expr = nixpkgsName G;
      expected = nixpkgsName N;
    };

    # ── BUILT WITH NO `lib`, NOTHING MOVES ──────────────────────────────────────────────────────
    # A caller's `_module.args.lib` still reaches a `{ lib, ... }:` module (no injected `lib`
    # shadows it), and a `lib` read with no inlet is still refused by name, catchably.
    test-with-no-lib-module-args-lib-still-serves = {
      expr =
        (at genMerge { } [
          { config._module.args.lib = N; }
          { options.x = genMerge.mkOption { type = genMerge.types.str; }; }
          ({ lib, ... }: { config.x = lib.optionalString true "served"; })
        ]).x;
      expected = "served";
    };
    test-with-no-lib-a-lib-read-is-still-refused = {
      expr = (builtins.tryEval (at genMerge { } [ (sub genMerge [ schemaImport ]) ]).s.weft).success;
      expected = false;
    };
    # Live control: a name nothing supplies is refused on the instantiated engine too.
    test-an-argument-nothing-supplies-is-still-refused-control = {
      expr =
        (builtins.tryEval
          (at G { } [
            { options.x = G.mkOption { type = G.types.str; }; }
            ({ noSuchArgument, ... }: { config.x = noSuchArgument; })
          ]).x
        ).success;
      expected = false;
    };
  };
}
