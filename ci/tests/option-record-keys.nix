# THE EVALUATED OPTION RECORD ANSWERS nixpkgs' KEYS (den-hoag-ixcxl, ADR-0039's serve half). nixpkgs'
# `evalOptionValue` puts nine keys beside a declaration — `value`, `isDefined`, `definitions`,
# `definitionsWithLocations`, `files`, `highestPrio`, `declarationPositions`, `options` and `valueMeta` —
# and gen-merge's record (`lib/modules.nix` `serveOptions`) answers each of them where it publishes one:
#   top  : `(evalModuleTree …).options.<o>`         grp  : `….options.g.<o>`
#   arg  : a module's own `options` argument         sub  : the same inside a submodule
#   gatt : the same under `attrsOf (submodule …)`    gso  : `….options.s.type.getSubOptions [ ]`
# Every cell runs ONE fixture through both engines and compares. `valueMeta` answers only at a foreign type
# (its cells below) and is refused by name at a gen type (`ci/tests-error.nix`, `option-record-keys`); `loc`
# and `declarations` are same-read controls. A key
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
          selfDecls =
            { options, ... }:
            {
              options.d = M.mkOption {
                type = T.int;
                default = builtins.length options.d.declarations;
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
          selfDecls = ev.config.d;
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
  # FIRST (`defs' = optional (opt ? default) … ++ defs`), as gen-merge's fold does (den-hoag-12e7r).
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

  # ── `valueMeta`: nixpkgs' v2-merge metadata at a foreign type, a projection of the fold (den-hoag-xroc7) ──
  # The modules declare nixpkgs' own types and run through both engines; `expr` is gen-merge's read,
  # `expected` nixpkgs'. A refusal reads as "REFUSED".
  T = nl.types;
  vmTry =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then r.value else "REFUSED";
  vmBoth = mods: rd: {
    expr = vmTry (rd (gm.evalModuleTree { } mods));
    expected = vmTry (rd (nl.evalModules { modules = mods; }));
  };
  vmOne = ty: v: [
    {
      options.x = nl.mkOption { type = ty; };
      config.x = v;
    }
  ];
  vmTwo = a: b: v: [
    { options.x = nl.mkOption { type = a; }; }
    {
      options.x = nl.mkOption { type = b; };
      config.x = v;
    }
  ];
  vmMeta = e: rend 6 e.options.x.valueMeta;
  vmSub = T.submodule {
    options.bar = nl.mkOption {
      type = T.int;
      default = 1;
    };
  };
  vmPos = T.addCheck T.int (v: v > 0);
  # the same foreign declaration inside a submodule's own evaluation, read through its module argument
  vmNested =
    evalM: subT: mkO:
    (evalM {
      modules = [
        {
          options.s = mkO {
            type = subT {
              imports = [
                { options.x = nl.mkOption { type = T.attrsOf T.int; }; }
                (
                  { options, ... }:
                  {
                    options.out = nl.mkOption { type = T.raw; };
                    config.out = rend 6 options.x.valueMeta;
                  }
                )
              ];
            };
          };
          config.s.x.k = 2;
        }
      ];
    }).config.s.out;
  # THE PLANTED VIOLATIONS: gen-merge's `config` refuses each by a declared check (a met foreign check, a
  # foreign `addCheck` over a module set, a gen `verify` copy, a `verify` overlay), and nixpkgs' metadata
  # carries the value it refuses. The metadata's value-bearing read refuses beside it. An `apply` is not a
  # check: the metadata is pre-`apply`, as nixpkgs'.
  vmGuard = mods: rd: {
    expr = {
      value = vmTry (gm.evalModuleTree { } mods).config.x;
      meta = vmTry (rd (gm.evalModuleTree { } mods));
    };
    expected = {
      value = "REFUSED";
      meta = "REFUSED";
    };
  };
  vmChecked = T.addCheck vmSub (v: v.bar > 0);
  # a gen `verify` copy rejecting 7, and a foreign v2 record carrying a `verify` overlay
  vmCopy = gm.types.int // {
    verify = v: if v == 7 then "copy rejects" else gm.types.int.verify v;
  };
  vmOverlay = T.attrListOf T.int // {
    verify = v: if v == [ { a = 7; } ] then "overlay rejects" else null;
  };
  vmInEither =
    ty:
    T.either T.str (
      T.submodule {
        options.y = nl.mkOption { type = ty; };
      }
    );
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
    test-arg-declarations-of-its-own-option = bothArg "selfDecls";

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

    test-default-beside-priority-1500-folds-first = {
      expr = dflt1500 gm;
      expected = dflt1500 nl;
    };

    # ── `valueMeta` at a foreign type folded by its own merge, equal to nixpkgs' ─────────────────
    # a merge stating no `v2`: `{ }`, whatever the type holds
    test-valueMeta-str-undefined = vmBoth [ { options.x = nl.mkOption { type = T.str; }; } ] vmMeta;
    test-valueMeta-str = vmBoth (vmOne T.str "s") vmMeta;
    test-valueMeta-int = vmBoth (vmOne T.int 3) vmMeta;
    test-valueMeta-uniq = vmBoth (vmOne (T.uniq (T.listOf T.int)) [
      1
      2
    ]) vmMeta;
    test-valueMeta-attrTag = vmBoth (vmOne (T.attrTag {
      a = nl.mkOption { type = vmSub; };
      b = nl.mkOption { type = T.int; };
    }) { a.bar = 2; }) vmMeta;
    test-valueMeta-deferredModule = vmBoth (vmOne T.deferredModule { }) vmMeta;
    test-valueMeta-anything = vmBoth (vmOne T.anything { k = 1; }) vmMeta;
    test-valueMeta-untyped = vmBoth [
      {
        options.x = nl.mkOption { };
        config.x = 1;
      }
    ] vmMeta;
    # a v2 merge: its own metadata, `_internal.type` beside it
    test-valueMeta-attrsOf = vmBoth (vmOne (T.attrsOf T.str) {
      foo = "a";
      bar = "b";
    }) vmMeta;
    test-valueMeta-listOf = vmBoth (vmOne (T.listOf T.str) [
      "a"
      "b"
    ]) vmMeta;
    test-valueMeta-attrsOf-attrsOf = vmBoth (vmOne (T.attrsOf (T.attrsOf T.int)) { x.y = 1; }) vmMeta;
    test-valueMeta-internal-type-is-the-record-type = vmBoth (vmOne (T.attrsOf T.str) { a = "a"; }) (
      e: e.options.x.valueMeta._internal.type == e.options.x.type
    );
    test-valueMeta-group = vmBoth [
      {
        options.g.x = nl.mkOption { type = T.attrsOf T.int; };
        config.g.x.a = 1;
      }
    ] (e: rend 6 e.options.g.x.valueMeta);
    test-valueMeta-in-a-gen-submodule-module-argument = {
      expr = vmTry (vmNested (r: gm.evalModuleTree { } r.modules) gm.types.submodule gm.mkOption);
      expected = vmTry (vmNested nl.evalModules T.submodule nl.mkOption);
    };
    # a headError: the metadata nixpkgs serves beside it, and an ad-hoc `check`, refused at both
    test-valueMeta-headError = vmBoth (vmOne (T.either T.int (T.attrsOf T.int)) "s") (
      e: builtins.attrNames e.options.x.valueMeta
    );
    test-valueMeta-ad-hoc-check = vmBoth (vmOne (T.attrsOf T.int // { check = builtins.isAttrs; }) {
      a = 1;
    }) vmMeta;
    # the values beside it, unmoved: a met foreign check passing
    test-valueMeta-value-control = vmBoth (vmTwo (T.attrsOf vmPos) (T.attrsOf T.int) { a = 1; }) (
      e: e.config.x
    );

    # ── no value gen-merge's `config` refuses by a declared check is served through `valueMeta` ──
    test-valueMeta-guard-meet = vmGuard (vmTwo (T.attrsOf vmPos) (T.attrsOf T.int) { a = -1; }) (
      e: builtins.attrNames e.options.x.valueMeta.attrs
    );
    test-valueMeta-guard-checked-submodule = vmGuard (vmTwo (T.attrsOf vmChecked) (T.attrsOf vmSub) {
      a.bar = -1;
    }) (e: e.options.x.valueMeta.attrs.a.configuration.config);
    test-valueMeta-guard-mapAttrsOfSubmodule = vmGuard (vmTwo (T.attrsOf vmChecked) (T.attrsOf vmSub) {
      a.bar = -1;
    }) (e: nl.modules.mapAttrsOfSubmodule (_: { cfg, ... }: cfg) e.options.x);
    test-valueMeta-guard-checked-submodule-top = vmGuard (vmTwo vmChecked vmSub { bar = -1; }) (
      e: e.options.x.valueMeta.configuration.config
    );
    test-valueMeta-guard-nullOr = vmGuard (vmOne (T.nullOr vmChecked) { bar = -1; }) (
      e: e.options.x.valueMeta.configuration.config
    );
    test-valueMeta-guard-copy-in-either = vmGuard (vmOne (vmInEither vmCopy) { y = 7; }) (
      e: e.options.x.valueMeta.configuration.config
    );
    test-valueMeta-guard-copy-in-either-option = vmGuard (vmOne (vmInEither vmCopy) { y = 7; }) (
      e: e.options.x.valueMeta.configuration.options.y.value
    );
    test-valueMeta-guard-copy-below-attrListOf = vmGuard (vmOne (T.attrListOf vmCopy) [ { a = 7; } ]) (
      e: e.options.x.valueMeta.attrListValue
    );
    test-valueMeta-guard-verify-overlay = vmGuard (vmOne vmOverlay [ { a = 7; } ]) (
      e: e.options.x.valueMeta.attrListValue
    );
  };
}
