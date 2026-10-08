# THE EVALUATED OPTION RECORD ANSWERS nixpkgs' KEYS (den-hoag-ixcxl, ADR-0039's serve half). nixpkgs'
# `evalOptionValue` puts nine keys beside a declaration — `value`, `isDefined`, `definitions`,
# `definitionsWithLocations`, `files`, `highestPrio`, `declarationPositions`, `options` and `valueMeta` —
# and gen-merge's record (`lib/modules.nix` `serveOptions`) answers each of them where it publishes one:
#   top  : `(evalModuleTree …).options.<o>`         grp  : `….options.g.<o>`
#   arg  : a module's own `options` argument         sub  : the same inside a submodule
#   gatt : the same under `attrsOf (submodule …)`    gso  : `….options.s.type.getSubOptions [ ]`
# Every cell runs ONE fixture through both engines and compares. `valueMeta` is the one key refused by
# name (`ci/tests-error.nix`, `option-record-keys`); `loc` and `declarations` are same-read controls. A key
# is read through `o ? k`, so an ABSENT key is a failed cell and never an abort.
#
# `options._module.*` at the module argument is outside this record (den-hoag-a67l3).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  nl = nixpkgsLib;
  evalWith =
    M: mods:
    if M ? evalModuleTree then gm.evalModuleTree { } mods else nl.evalModules { modules = mods; };
  keys = [
    "definitions"
    "definitionsWithLocations"
    "files"
    "value"
    "isDefined"
    "highestPrio"
    "declarationPositions"
    "options"
    "declarations"
    "loc"
  ];
  # A key's value made comparable across engines: a type object reads as its name, a function as a tag.
  rend =
    d: v:
    if builtins.isFunction v then
      "<lambda>"
    else if builtins.isString v then
      v
    else if d <= 0 then
      "<deep:${builtins.typeOf v}>"
    else if builtins.isList v then
      map (rend (d - 1)) v
    else if builtins.isAttrs v then
      if (v._type or null) == "option-type" then
        "<type:${v.name or "?"}>"
      else
        builtins.mapAttrs (_: rend (d - 1)) (removeAttrs v [ "__toString" ])
    else
      v;
  readOpt =
    o:
    builtins.listToAttrs (
      map (k: {
        name = k;
        value =
          if !(o ? ${k}) then
            "ABSENT"
          else
            let
              r = builtins.tryEval (builtins.deepSeq (rend 6 o.${k}) (rend 6 o.${k}));
            in
            if r.success then r.value else "REFUSED";
      }) keys
    );

  # ── the fixtures: `pop`, one option per priority/order shape, and `ord`/`ord2`, the ordering ones ──
  fixture =
    M: fx:
    let
      T = M.types;
      ls = T.listOf T.str;
      pop = fx == "pop";
      decls =
        if pop then
          {
            x = M.mkOption {
              type = ls;
              default = [ "dflt" ];
            };
            d = M.mkOption {
              type = ls;
              default = [ "dd" ];
            };
            u = M.mkOption { type = ls; };
            i0 = M.mkOption { type = ls; };
            i1 = M.mkOption { type = ls; };
            df = M.mkOption {
              type = ls;
              default = [ "dd" ];
            };
            fo = M.mkOption { type = ls; };
            o1 = M.mkOption { type = ls; };
            ap = M.mkOption {
              type = ls;
              apply = map (s: s + "!");
            };
            sm = M.mkOption {
              type = T.submodule {
                options.a = M.mkOption {
                  type = T.int;
                  default = 0;
                };
              };
              default = { };
            };
            rd = M.mkOption { type = ls; };
          }
          // builtins.listToAttrs [
            {
              name = "dyn";
              value = M.mkOption {
                type = ls;
                default = [ "dy" ];
              };
            }
          ]
        else
          {
            x = M.mkOption {
              type = ls;
              default = [ "dflt" ];
            };
          };
      # `rd` is redeclared, the default on its second declaration: nixpkgs' `<default>` file is the
      # FIRST declaring file of its reversed module list.
      decls2 = if pop then { rd = M.mkOption { default = [ "r2" ]; }; } else { };
      defsOrd = [
        {
          _file = "A";
          imports = [
            {
              _file = "A1";
              config.x = M.mkMerge [
                [ "a1" ]
                (M.mkBefore [ "a1b" ])
              ];
            }
          ];
          config.x = M.mkMerge [
            [ "a0" ]
            (M.mkOrder 1000 [ "a2" ])
          ];
        }
        {
          _file = "C";
          config.x = M.mkOrder 1000 [ "c" ];
        }
        {
          _file = "F1";
          config.x = M.mkForce [ "f1" ];
        }
        {
          _file = "F2";
          imports = [
            {
              _file = "F2i";
              config.x = M.mkForce (M.mkAfter [ "f2i" ]);
            }
          ];
          config.x = M.mkForce [ "f2" ];
        }
        {
          _file = "P";
          config.x = [ "p" ];
        }
      ];
      defs =
        if pop then
          [
            {
              _file = "zz";
              config.x = M.mkMerge [
                [ "z1" ]
                (M.mkIf false [ "zf" ])
              ];
            }
            {
              _file = "aa";
              config.x = M.mkBefore [ "a1" ];
            }
            {
              _file = "dd";
              config.x = M.mkDefault [ "d1" ];
            }
            {
              _file = "bb";
              config.x = M.mkAfter [ "b1" ];
            }
            {
              _file = "nn";
              config.x = [ "n1" ];
            }
            {
              _file = "I0";
              config.i0 = M.mkIf false [ "no" ];
            }
            {
              _file = "I1";
              config.i1 = M.mkIf true [ "yes" ];
            }
            {
              _file = "DF";
              config.df = M.mkDefault [ "md" ];
            }
            {
              _file = "FO";
              config.fo = M.mkMerge [
                (M.mkForce [ "f" ])
                [ "plain" ]
              ];
            }
            {
              _file = "FD";
              config.fo = M.mkDefault [ "fd" ];
            }
            {
              _file = "O1";
              config.o1 = M.mkMerge [
                (M.mkOrder 1000 [ "o1000" ])
                [ "plain" ]
                (M.mkBefore [ "b" ])
              ];
            }
            {
              _file = "AP";
              config.ap = [
                "a"
                "b"
              ];
            }
            {
              _file = "SM";
              config.sm.a = 3;
            }
          ]
        else if fx == "ord" then
          defsOrd
        else
          builtins.filter (
            m:
            !(builtins.elem m._file [
              "F1"
              "F2"
            ])
          ) defsOrd;
    in
    {
      inherit decls decls2 defs;
    };

  # The record of every fixture option at one position, read on one engine.
  recordAt =
    M: fx: pos:
    let
      T = M.types;
      inherit (fixture M fx) decls decls2 defs;
      names = builtins.attrNames decls;
      readSet =
        os:
        builtins.listToAttrs (
          map (n: {
            name = n;
            value = readOpt os.${n};
          }) names
        );
      dmod = {
        _file = "decl";
        options = decls;
      };
      dmod2 = {
        _file = "decl2";
        options = decls2;
      };
      out = {
        _file = "outdecl";
        options.out = M.mkOption { type = T.raw; };
      };
      reader = {
        _file = "reader";
        imports = [ ({ options, ... }: { config.out = readSet options; }) ];
      };
      inner = [
        dmod
        dmod2
        out
        reader
      ]
      ++ defs;
      inGroup =
        m:
        m
        // {
          config.g = m.config;
        }
        // (if m ? imports then { imports = map inGroup m.imports; } else { });
      modsAt = {
        top = [
          dmod
          dmod2
        ]
        ++ defs;
        grp = [
          {
            _file = "decl";
            options.g = decls;
          }
          {
            _file = "decl2";
            options.g = decls2;
          }
        ]
        ++ map inGroup defs;
        arg = inner;
        sub = [
          {
            _file = "outer";
            options.s = M.mkOption {
              type = T.submodule inner;
              default = { };
            };
          }
        ];
        gatt = [
          {
            _file = "outer";
            options.s = M.mkOption { type = T.attrsOf (T.submodule inner); };
          }
          {
            _file = "outer2";
            config.s.k = { };
          }
        ];
      };
      ev = evalWith M (modsAt.${pos} or modsAt.sub);
    in
    {
      top = readSet ev.options;
      grp = readSet ev.options.g;
      arg = ev.config.out;
      sub = ev.config.s.out;
      gatt = ev.config.s.k.out;
      gso = readSet (ev.options.s.type.getSubOptions [ ]);
    }
    .${pos};
  recordCell = fx: pos: {
    expr = recordAt gm fx pos;
    expected = recordAt nl fx pos;
  };

  # ── a module reading its own `options` argument: one probe module beside a fixed base ───────────
  argCell =
    M: cell:
    let
      T = M.types;
      ls = T.listOf T.str;
      base = {
        _file = "base";
        options.x = M.mkOption { type = ls; };
        options.u = M.mkOption { type = ls; };
        options.y = M.mkOption {
          type = ls;
          default = [ ];
        };
        options.out = M.mkOption {
          type = T.raw;
          default = null;
        };
        options.flag = M.mkOption {
          type = T.bool;
          default = false;
        };
      };
      def = {
        _file = "zz";
        config.x = [ "z1" ];
      };
      probe =
        {
          argDefs = { options, ... }: { config.out = options.x.definitions; };
          argIsDef = { options, ... }: { config.flag = M.mkIf options.x.isDefined true; };
          rootIsDef = { options, ... }: { config = M.mkIf options.x.isDefined { flag = true; }; };
          argVal = { options, ... }: { config.out = options.x.value; };
          argUndefVal = { options, ... }: { config.out = options.u.value; };
          siblingIsDef = { options, ... }: { config.y = M.mkIf options.x.isDefined [ "y" ]; };
          declIsDef =
            { options, ... }:
            {
              options.w = M.mkOption {
                type = T.bool;
                default = options.x.isDefined;
              };
            };
        }
        .${cell};
      ev = evalWith M [
        base
        def
        probe
      ];
      read =
        {
          argDefs = ev.config.out;
          argIsDef = ev.config.flag;
          rootIsDef = ev.config.flag;
          argVal = ev.config.out;
          argUndefVal = ev.config.out;
          siblingIsDef = ev.config.y;
          declIsDef = ev.config.w;
        }
        .${cell};
      r = builtins.tryEval (builtins.deepSeq read read);
    in
    if r.success then { v = r.value; } else { refused = true; };

  # ── a FREEFORM module gated on a declared option's `value` (C1): the record's `value` is the option's
  # own merged value, as nixpkgs' is, and never the module config, whose freeform layer the gate is in ──
  freeformCell =
    M: cell:
    let
      T = M.types;
      ff = {
        freeformType = T.attrsOf T.int;
        options.x = M.mkOption { type = T.int; };
      };
      c =
        {
          ffVal = {
            mods = [
              (
                { options, ... }:
                ff
                // {
                  config = {
                    x = 1;
                    foo = M.mkIf (options.x.value == 1) 2;
                  };
                }
              )
            ];
            read = e: e.config.foo;
          };
          ffValGrp = {
            mods = [
              (
                { options, ... }:
                {
                  freeformType = T.attrsOf T.int;
                  options.g.x = M.mkOption { type = T.int; };
                  config = {
                    g.x = 1;
                    foo = M.mkIf (options.g.x.value == 1) 2;
                  };
                }
              )
            ];
            read = e: e.config.foo;
          };
          ffSub = {
            mods = [
              {
                options.s = M.mkOption {
                  type = T.submodule (
                    { options, ... }:
                    ff
                    // {
                      config.foo = M.mkIf options.x.isDefined 2;
                      config.bar = M.mkIf (options.x.value == 1) 3;
                    }
                  );
                  default = { };
                };
              }
              { config.s.x = 1; }
            ];
            read = e: { inherit (e.config.s) foo bar; };
          };
          # The same module, the declared option read from OUTSIDE on the published record.
          ffValPub = {
            mods = [
              (
                { options, ... }:
                ff
                // {
                  config = {
                    x = 1;
                    foo = M.mkIf (options.x.value == 1) 2;
                  };
                }
              )
            ];
            read = e: e.options.x.value;
          };
          # Control: the same gate with no `freeformType`, `foo` declared.
          ffValNoFreeform = {
            mods = [
              (
                { options, ... }:
                {
                  options.x = M.mkOption { type = T.int; };
                  options.foo = M.mkOption { type = T.int; };
                  config = {
                    x = 1;
                    foo = M.mkIf (options.x.value == 1) 2;
                  };
                }
              )
            ];
            read = e: e.config.foo;
          };
        }
        .${cell};
      read = c.read (evalWith M c.mods);
    in
    builtins.deepSeq read read;

  bothArg = cell: {
    expr = argCell gm cell;
    expected = argCell nl cell;
  };
  bothFreeform = cell: {
    expr = freeformCell gm cell;
    expected = freeformCell nl cell;
  };

  # nixpkgs' own reader of the record: `lib.mkDerivedConfig` reads `highestPrio` and `value`.
  derived =
    M:
    let
      ev = evalWith M [
        {
          options.src = M.mkOption { type = M.types.str; };
          options.dst = M.mkOption { type = M.types.str; };
        }
        { config.src = M.mkDefault "s"; }
        ({ options, ... }: { config.dst = nl.mkDerivedConfig options.src (s: s + "!"); })
      ];
    in
    {
      inherit (ev.config) dst;
      prio = ev.options.dst.highestPrio;
    };

  # The docs position: a NESTING option's value read on `getSubOptions`.
  innerSm = M: [
    {
      options.sm = M.mkOption {
        type = M.types.submodule {
          options.a = M.mkOption {
            type = M.types.int;
            default = 0;
          };
        };
        default = { };
      };
    }
    { config.sm.a = 3; }
  ];
  docsValue =
    M: type:
    (
      (evalWith M [
        {
          options.s = M.mkOption {
            inherit type;
            default = { };
          };
        }
      ]).options.s.type.getSubOptions
        [ ]
    ).sm.value;

  # Warm: an edit adding a module that defines `b` only, so `a` is reused; its record is the cold one's.
  warmRecords =
    let
      ls = gm.types.listOf gm.types.str;
      decl = {
        _file = "decl";
        options.a = gm.mkOption {
          type = ls;
          default = [ "da" ];
        };
        options.b = gm.mkOption { type = ls; };
      };
      base = [
        decl
        {
          _file = "A";
          config.a = gm.mkBefore [ "a1" ];
        }
        {
          _file = "A2";
          config.a = [ "a2" ];
        }
      ];
      edited = [
        {
          _file = "E";
          config.b = [ "e" ];
        }
      ];
      cold = gm.evalModuleTree { } (base ++ edited);
      warm = gm.evalModuleTree {
        warmFrom = gm.evalModuleTree { } base;
        editedModules = edited;
      } (base ++ edited);
      records = ev: builtins.mapAttrs (_: readOpt) { inherit (ev.options) a b; };
    in
    {
      inherit (warm.warmDecision) mode;
      equal = records cold == records warm;
    };

  # A module DECLARING `options._module.<k>`: its record's `value` is read off the declared-only tree,
  # which carries the declared `_module` subtree and none of the engine's own `_module` overlay.
  declaredModuleOption =
    M:
    let
      ev = evalWith M [
        {
          options._module.extra = M.mkOption {
            type = M.types.str;
            default = "e";
          };
          options.out = M.mkOption {
            type = M.types.raw;
            default = null;
          };
        }
        { config._module.extra = "set"; }
        (
          { options, ... }:
          {
            config.out = {
              inherit (options._module.extra) value isDefined;
            };
          }
        )
      ];
    in
    {
      published = ev.options._module.extra.value;
      argument = ev.config.out;
    };

  # The `<default>` definition beside a priority-1500 one survives the filter, and nixpkgs puts it
  # FIRST (`defs' = optional (opt ? default) … ++ defs`) where gen-merge's fold puts it last.
  dflt1500 =
    M:
    let
      ev = evalWith M [
        (
          { options, ... }:
          {
            _file = "o";
            options.l = M.mkOption {
              type = M.types.listOf M.types.int;
              default = [ 1 ];
            };
            options.o = M.mkOption {
              type = M.types.raw;
              default = null;
            };
            config.l = M.mkOptionDefault [ 9 ];
            config.o = options.l.definitions;
          }
        )
        {
          _file = "p";
          config.l = M.mkOverride 1500 [ 5 ];
        }
      ];
    in
    {
      inherit (ev.config) l;
      definitions = ev.config.o;
    };
in
{
  flake.tests.option-record-keys = {
    # ── the nine keys (less `valueMeta`) and the two controls, every fixture option, six positions ──
    test-pop-top = recordCell "pop" "top";
    test-pop-grp = recordCell "pop" "grp";
    test-pop-arg = recordCell "pop" "arg";
    test-pop-sub = recordCell "pop" "sub";
    test-pop-gatt = recordCell "pop" "gatt";
    test-pop-gso = recordCell "pop" "gso";
    test-ord-top = recordCell "ord" "top";
    test-ord-grp = recordCell "ord" "grp";
    test-ord-arg = recordCell "ord" "arg";
    test-ord-sub = recordCell "ord" "sub";
    test-ord-gatt = recordCell "ord" "gatt";
    test-ord-gso = recordCell "ord" "gso";
    test-ord2-top = recordCell "ord2" "top";
    test-ord2-grp = recordCell "ord2" "grp";
    test-ord2-arg = recordCell "ord2" "arg";
    test-ord2-sub = recordCell "ord2" "sub";
    test-ord2-gatt = recordCell "ord2" "gatt";
    test-ord2-gso = recordCell "ord2" "gso";

    # The successor of the retired refusal (`tree-type` in `ci/tests-error.nix`): the same read on the
    # same `getSubOptions` record now answers.
    test-an-evaluated-option-key-answers-on-the-docs-record = {
      expr =
        (
          (gm.evalModuleTree { } [ { options.a = gm.mkOption { type = gm.types.str; }; } ]).type.getSubOptions
            [
              "x"
            ]
        ).a.definitions;
      expected = [ ];
    };

    # ── the module-argument idiom, each = nixpkgs ─────────────────────────────────────────────────
    test-arg-definitions = bothArg "argDefs";
    test-arg-isDefined-under-mkIf = bothArg "argIsDef";
    test-arg-isDefined-gates-the-config-root = bothArg "rootIsDef";
    test-arg-value = bothArg "argVal";
    test-arg-value-of-an-undefined-option-refuses = bothArg "argUndefVal";
    test-arg-isDefined-gates-a-sibling = bothArg "siblingIsDef";
    test-arg-isDefined-in-a-declaration-default = bothArg "declIsDef";

    # ── a freeform module gated on `value` (C1), and the control with no freeform layer ──────────
    test-freeform-gated-on-value = bothFreeform "ffVal";
    test-freeform-gated-on-a-group-value = bothFreeform "ffValGrp";
    test-freeform-submodule-gated-on-value = bothFreeform "ffSub";
    test-freeform-value-on-the-published-record = bothFreeform "ffValPub";
    test-value-gate-without-freeform-control = bothFreeform "ffValNoFreeform";

    test-mkDerivedConfig-reads-the-record = {
      expr = derived gm;
      expected = derived nl;
    };

    test-docs-position-value-under-submodule = {
      expr = docsValue gm (gm.types.submodule (innerSm gm));
      expected = docsValue nl (nl.types.submodule (innerSm nl));
    };
    test-docs-position-value-under-the-tree-type = {
      expr = docsValue gm (gm.evalModuleTree { } (innerSm gm)).type;
      expected = docsValue nl (nl.types.submodule (innerSm nl));
    };

    test-a-declared-module-option-serves-its-value = {
      expr = declaredModuleOption gm;
      expected = declaredModuleOption nl;
    };

    test-a-warm-reused-option-serves-the-cold-record = {
      expr = warmRecords;
      expected = {
        mode = "warm";
        equal = true;
      };
    };

    # PINNED, a known divergence (den-hoag-12e7r): the record projects gen-merge's fold, whose
    # `<default>` comes last where nixpkgs' comes first (`l = [ 1 5 9 ]`,
    # `definitions = [ [ 1 ] [ 5 ] [ 9 ] ]`). The row's fix moves this cell to nixpkgs' value.
    test-default-beside-priority-1500-folds-last-pinned = {
      expr = dflt1500 gm;
      expected = {
        l = [
          5
          9
          1
        ];
        definitions = [
          [ 5 ]
          [ 9 ]
          [ 1 ]
        ];
      };
    };
  };
}
