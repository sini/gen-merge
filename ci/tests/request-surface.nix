# THE REQUEST / RESULT SURFACE nixpkgs' `evalModules` serves (den-hoag-l23bt, den-hoag-d2o0g): the
# `class` request field and the `_class` argument, `extendModules` and `moduleType` as arguments,
# `extendModules` as a result field, and the result's `_type`, `class` and `graph`. Every cell is one expression read on both engines:
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
      # `moduleType` held by an option as it is (`grab`), and behind a function (`fnGrab`), so a deep
      # force of the held type meets no copy of itself
      grab =
        { moduleType, ... }:
        {
          options.mt = L.mkOption { default = moduleType; };
        };
      fnGrab =
        { moduleType, ... }:
        {
          options.mt = L.mkOption { default = _: moduleType; };
        };
      # k hops down the regress: each empty value's own `moduleType`, as nixpkgs' each fresh `base`
      hops = k: t: if k == 0 then t else hops (k - 1) (emptyOf t).value.mt;
      gb = [
        base
        grab
        posMod
      ];
      chainA = k: read (emptyOf (hops k (ev { modules = gb ++ [ { a = 7; } ]; }).type)).value.a;
      viaMT = f: { moduleType, ... }: { options.r = opt (f moduleType); };
      mtArg =
        def: via:
        read
          (ev {
            modules = [
              base
              { a = 4; }
              { _module.args.moduleType = def; }
              via
            ];
          }).config.r;
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
      # `moduleType`: the evaluation's own type, as an argument; its regress serves every finite read
      # however deep (den-hoag-8qenh C17), and a positioned evaluation's carries its position's `name`
      argNames =
        read
          (ev {
            modules = [
              base
              ({ config, ... }: { options.r = opt (builtins.attrNames config._module.args); })
            ];
          }).config.r;
      pubArgNames = builtins.attrNames (ev { modules = [ base ]; }).options._module.args.value;
      mtFormalA =
        read
          (ev {
            modules = [
              base
              { a = 4; }
              (viaMT (t: (emptyOf t).value.a))
            ];
          }).config.r;
      mtCfgA =
        read
          (ev {
            modules = [
              base
              { a = 4; }
              ({ config, ... }: { options.r = opt (emptyOf config._module.args.moduleType).value.a; })
            ];
          }).config.r;
      mtForce = mtArg (L.mkForce 5) (viaMT id);
      mtDefault = mtArg (L.mkDefault 5) (viaMT (t: (emptyOf t).value.a));
      mtHeldForces = forces (
        (ev {
          modules = [
            base
            fnGrab
          ];
        }).config.mt
          null
      );
      mtHeldName =
        read
          (
            (ev {
              modules = [
                base
                fnGrab
              ];
            }).config.mt
              null
          ).name;
      depth2 =
        read
          (ev {
            modules = [
              (
                { moduleType, ... }:
                {
                  options.y = opt 5;
                  options.x = opt (emptyOf moduleType).value.y;
                  options.r = opt (emptyOf moduleType).value.x;
                }
              )
            ];
          }).config.r;
      depth3 =
        read
          (ev {
            modules = [
              (
                { moduleType, ... }:
                {
                  options.z = opt 9;
                  options.y = opt (emptyOf moduleType).value.z;
                  options.x = opt (emptyOf moduleType).value.y;
                  options.r = opt (emptyOf moduleType).value.x;
                }
              )
            ];
          }).config.r;
      chain31A = chainA 31;
      chain33A = chainA 33;
      chain40A = chainA 40;
      chain100A = chainA 100;
      # an option's own empty-seed run inside a 33-hop chain: a type hop is no step of its fuel
      chain33Sub =
        read
          (emptyOf (
            hops 33
              (ev {
                modules = gb ++ [
                  {
                    options.s = L.mkOption {
                      type = sub [ base ];
                      default = { };
                    };
                  }
                ];
              }).type
          )).value.s.a;
      chain33U =
        read
          (emptyOf (
            hops 33 (ev { modules = gb ++ [ { options.s = L.mkOption { type = sub [ base ]; }; } ]; }).type
          )).value.a;
      # two hops down an unpositioned evaluation, two placeholders name it: refused on both
      name3 = read (emptyOf (hops 2 (ev { modules = gb; }).type)).value.nm;
      posMTEmptyNm =
        read
          (emptyOf
            (ev {
              modules = [
                (host [
                  posMod
                  grab
                ])
              ];
            }).config.n.foo.mt
          ).value.nm;
      posChain40 =
        read
          (emptyOf (
            hops 40
              (ev {
                modules = [
                  (host [
                    posMod
                    grab
                  ])
                ];
              }).config.n.foo.mt
          )).value.nm;
      posHeldForces = forces (
        (ev {
          modules = [
            (host [
              posMod
              fnGrab
            ])
          ];
        }).config.n.foo.mt
          null
      );
      # the position's `name` it carries meets another position's: refused on both
      posMTElsewhere =
        read
          (ev {
            modules = [
              {
                options.o = L.mkOption {
                  type =
                    TY.attrsOf
                      (ev {
                        modules = [
                          (host [
                            posMod
                            grab
                          ])
                        ];
                      }).config.n.foo.mt;
                  default = { };
                };
                config.o.bar = { };
              }
            ];
          }).config.o.bar.nm;
      # an unpositioned evaluation's, placed at a position, takes that position's
      mtAtPos =
        read
          (ev {
            modules = [
              {
                options.o = L.mkOption {
                  type = TY.attrsOf (ev { modules = gb; }).config.mt;
                  default = { };
                };
                config.o.bar = { };
              }
            ];
          }).config.o.bar.nm;
      # the RESULT's `extendModules` is the engine's own, whatever a module defines as the argument
      resExtForce =
        builtins.isFunction
          (ev {
            modules = [
              base
              { _module.args.extendModules = L.mkForce 5; }
            ];
          }).extendModules;
      resExtForceA =
        read
          (
            (ev {
              modules = [
                base
                { _module.args.extendModules = L.mkForce 5; }
              ];
            }).extendModules
              { modules = [ { a = 3; } ]; }
          ).config.a;
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
