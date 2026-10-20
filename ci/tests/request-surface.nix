# THE REQUEST / RESULT SURFACE nixpkgs' `evalModules` serves (den-hoag-l23bt, den-hoag-d2o0g): the
# `class` request field and the `_class` argument, `extendModules` as an argument and a result field,
# and the result's `_type`, `class` and `graph`. Every cell is one expression read on both engines:
# `expr` is gen-merge's reading and `expected` is nixpkgs' reading of the same expression. A refusal
# reads as `"refused"` on either side, so a cell compares whether each side serves, and what.
#
# `extendModules` as an argument is the engine's own definition beside a module's (nixpkgs'
# `internalModule`): `mkForce` wins, `mkDefault` yields, a plain definition refuses as defined twice.
# It is read through `config._module.args` and as a formal, in each of the three `_module` views (a
# module declares `options._module`, the evaluation is positioned, or neither).
{
  evalRequest,
  genMerge,
  nixpkgsLib,
  ...
}:
let
  sides = {
    gen = {
      L = genMerge;
      ev = evalRequest;
      sub = ms: genMerge.types.submodule ms;
      emptyOf = t: { value = t.whenEmpty.value; };
    };
    nixpkgs = {
      L = nixpkgsLib;
      ev = nixpkgsLib.evalModules;
      sub = ms: nixpkgsLib.types.submoduleWith { modules = ms; };
      emptyOf = t: t.emptyValue;
    };
  };
  read =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then r.value else "refused";
  fx = ./_fixtures;

  cells =
    {
      L,
      ev,
      sub,
      emptyOf,
    }:
    let
      TY = L.types;
      opt = d: L.mkOption { default = d; };
      forces = x: (builtins.tryEval (builtins.deepSeq x true)).success;
      base = {
        options.a = opt 1;
        options.l = L.mkOption {
          type = TY.listOf TY.str;
          default = [ ];
        };
      };
      # a submodule element whose modules read their own `name`, and the name of their extension
      posMod =
        { name, ... }:
        {
          options.nm = opt name;
          options.x = opt "x0";
        };
      host = ms: {
        options.n = L.mkOption {
          type = TY.attrsOf (sub ms);
          default = { };
        };
        config.n.foo = { };
      };
      sa = ev {
        modules = [
          base
          ({ s, ... }: { options.q = opt s; })
        ];
        specialArgs = {
          s = 1;
          t = 2;
        };
      };
      saExt = sa.extendModules {
        specialArgs.s = 3;
        modules = [ ({ t, ... }: { options.u = opt t; }) ];
      };
      # a module defining the engine's `extendModules` argument at `def`, read through `config` or as
      # the formal, in the unpositioned view, the positioned view and the `options._module` view
      viaCfg = f: { config, ... }: { options.r = opt (f config._module.args.extendModules); };
      viaFormal = f: { extendModules, ... }: { options.r = opt (f extendModules); };
      ext =
        def: via:
        read
          (ev {
            modules = [
              base
              { _module.args.extendModules = def; }
              via
            ];
          }).config.r;
      extPos =
        def: via:
        read
          (ev {
            modules = [
              (host [
                { _module.args.extendModules = def; }
                via
              ])
            ];
          }).config.n.foo.r;
      extOwn =
        def: via:
        read
          (ev {
            modules = [
              base
              { options._module.foo = opt 1; }
              { _module.args.extendModules = def; }
              via
            ];
          }).config.r;
      id = x: x;
    in
    {
      # `extendModules`: a stated prefix replaces, an unstated one is kept
      extPrefixLoc =
        read
          ((ev { modules = [ base ]; }).extendModules { prefix = [ "p" ]; }).options.l.loc;
      extKeepPrefixLoc =
        read
          (
            (ev {
              modules = [ base ];
              prefix = [ "q" ];
            }).extendModules
              { }
          ).options.l.loc;
      # specialArgs merge by `//`: one the extension does not restate stays
      extSAu = read saExt.config.u;
      extSA = read (removeAttrs saExt.config [ "_module" ]);
      extendSpecialSpec =
        read
          (
            (ev {
              modules = [ ({ s, ... }: { options.v = L.mkOption { default = s; }; }) ];
              specialArgs.s = 1;
            }).extendModules
              { specialArgs.s = 2; }
          ).config.v;
      extCheck =
        read
          (
            (ev {
              modules = [ base ];
              check = false;
            }).extendModules
              { modules = [ { zz = 1; } ]; }
          ).config.a;
      # an extension inside a submodule keeps the position's `name`, at its own prefix and at a stated one
      posExtName =
        read
          (ev {
            modules = [
              (host [
                posMod
                (
                  { extendModules, ... }:
                  {
                    options.extNm = opt (extendModules { modules = [ { x = "y"; } ]; }).config.nm;
                  }
                )
              ])
            ];
          }).config.n.foo.extNm;
      posExtPrefixName =
        read
          (ev {
            modules = [
              (host [
                posMod
                ({ extendModules, ... }: { options.extNmP = opt (extendModules { prefix = [ "z" ]; }).config.nm; })
              ])
            ];
          }).config.n.foo.extNmP;
      isFnExt = builtins.isFunction (ev { modules = [ base ]; }).extendModules;
      fnArgsExt = builtins.functionArgs (ev { modules = [ base ]; }).extendModules;
      # the engine's argument beside a module's definition of it
      extDefCfg = ext 5 (viaCfg id);
      extDefFormal = ext 5 (viaFormal id);
      extForceCfg = ext (L.mkForce 5) (viaCfg id);
      extForceFormal = ext (L.mkForce 5) (viaFormal id);
      extDefaultCfg = ext (L.mkDefault 5) (viaCfg builtins.isFunction);
      extDefaultFormal = ext (L.mkDefault 5) (viaFormal builtins.isFunction);
      extForceCfgPositioned = extPos (L.mkForce 5) (viaCfg id);
      extDefaultCfgPositioned = extPos (L.mkDefault 5) (viaCfg builtins.isFunction);
      extDefCfgPositioned = extPos 5 (viaCfg id);
      extForceCfgOwnOptions = extOwn (L.mkForce 5) (viaCfg id);
      extDefaultCfgOwnOptions = extOwn (L.mkDefault 5) (viaCfg builtins.isFunction);
      extDefCfgOwnOptions = extOwn 5 (viaCfg id);
      # a module defining it leaves every other argument served
      extDefPkgs =
        read
          (ev {
            modules = [
              base
              {
                _module.args.extendModules = 5;
                _module.args.pkgs = 7;
              }
              ({ pkgs, ... }: { options.r = opt pkgs; })
            ];
          }).config.r;
      # `class`: the request, the `_class` argument, its check on a nested evaluation of the tree's own type
      classArgNull =
        read
          (ev {
            modules = [
              base
              ({ _class, ... }: { options.k = opt _class; })
            ];
          }).config.k;
      classArgReq =
        read
          (ev {
            modules = [
              base
              ({ _class, ... }: { options.k = opt _class; })
            ];
            class = "nixos";
          }).config.k;
      extClass =
        read
          (
            (ev {
              modules = [
                base
                ({ _class, ... }: { options.k = opt _class; })
              ];
              class = "nixos";
            }).extendModules
              { }
          ).config.k;
      classNestedGen =
        read
          (ev {
            modules = [
              {
                options.s = L.mkOption {
                  type =
                    TY.attrsOf
                      (ev {
                        class = "nixos";
                        modules = [ base ];
                      }).type;
                  default = { };
                };
              }
              { s.a._class = "darwin"; }
            ];
          }).config.s.a.a;
      # the result fields
      resClass = (ev { modules = [ base ]; }).class;
      typeOfResult = (ev { modules = [ base ]; })._type;
      graph =
        read
          (ev {
            modules = [
              { }
              (args: { })
              (fx + "/request-surface-graph-a.nix")
              (fx + "/request-surface-graph-b.nix")
              {
                _file = "named.nix";
                imports = [
                  (fx + "/request-surface-graph-b.nix")
                  { key = "k2"; }
                ];
              }
            ];
          }).graph;
      # the whole argument set deep-forces, read inside a module and off the published option record
      dsArgsIn =
        read
          (ev {
            modules = [
              base
              ({ config, ... }: {
                options.r = opt (builtins.tryEval (builtins.deepSeq config._module.args true)).success;
              })
            ];
          }).config.r;
      dsPubArgs =
        (builtins.tryEval (builtins.deepSeq (ev { modules = [ base ]; }).options._module.args.value true))
        .success;
      # a free-standing type deep-forces through its empty value: alone, as a container element, and
      # read off the options tree; a throwing default still fails the force
      dsSubType = forces (sub [ base ]);
      dsSubTypeThrow = forces (sub [ { options.t = opt (throw "T-default"); } ]);
      dsSubInAttrs = forces (TY.attrsOf (sub [ base ]));
      dsOptType =
        forces
          (ev {
            modules = [
              {
                options.x = L.mkOption {
                  type = sub [ base ];
                  default = { };
                };
              }
            ];
          }).options.x.type;
      # a hand-built composite whose empty case is its element's own empty value, inside an evaluation
      handA =
        let
          S = sub [ base ];
        in
        read
          (ev {
            modules = [
              {
                options.x = L.mkOption {
                  type = TY.mkOptionType {
                    name = "hand";
                    merge = loc: defs: S.merge loc defs;
                    emptyValue = emptyOf S;
                    check = _: true;
                  };
                };
              }
            ];
          }).config.x.a;
      # an evaluation's own type deep-forces through its empty value, the module set over no
      # definitions: alone, with a throwing default, as a container element, and read for a value
      dsMTTop = forces (ev { modules = [ base ]; }).type;
      dsMTTopThrow = forces (ev { modules = [ { options.t = opt (throw "T-default"); } ]; }).type;
      dsTreeInAttrs = forces (TY.attrsOf (ev { modules = [ base ]; }).type);
      mtTopEmptyA =
        read
          (emptyOf
            (ev {
              modules = [
                base
                { a = 7; }
              ];
            }).type
          ).value.a;
    };
  gen = cells sides.gen;
  nixpkgs = cells sides.nixpkgs;
in
{
  flake.tests.request-surface = builtins.listToAttrs (
    map (name: {
      name = "test-${name}-equals-nixpkgs";
      value = {
        expr = gen.${name};
        expected = nixpkgs.${name};
      };
    }) (builtins.attrNames gen)
  );
}
