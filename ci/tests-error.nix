# THE SECOND TEST OUTPUT — cells whose subject is an ERROR, and the runner that reads them.
#
# The engine refuses several shapes BY NAME: an undeclared key names the option path it could not
# place, a leaf/group collision names the colliding option. That each refuses is a boolean and
# `builtins.tryEval` can assert it — the suites under ./tests do exactly that in a dozen places.
# WHICH option a refusal named is a claim about the message, and `tryEval` discards the message
# (`{ success = false; value = false; }`). The only assertion available for it is nix-unit's
# `expectedError`.
#
# ★ WHY A SECOND OUTPUT RATHER THAN A SECOND SUITE. `gen-harness.lib.mkCi` builds `checks.default`
# from a homegrown asserter that evaluates `t.expr == t.expected` UNCONDITIONALLY, and it
# quantifies over `config.flake.tests` and nothing else (`gen-harness/flakeModule.nix`). A cell
# with no `expected` and a throwing `expr` therefore CRASHES that batch gate rather than failing
# it — measured here, not adopted: with the first cell below moved into `flake.tests`,
# `nix flake check ./ci` died carrying this file's own refusal message rather than reporting a
# failed cell. Hosting these cells on `flake.testsError` puts them outside the asserter's
# quantifier while keeping them live on the nix-unit path.
#
# ★ AND THE SPLIT IS STRUCTURAL, NOT CONVENTIONAL. This file is NOT under `./tests`, which is the
# whole of `testModules`, so which cells land in which output depends on no filter predicate and
# no ignore convention that a dependency bump could redefine. It reaches the flake through
# `mkCi`'s `extraModules`.
#
# BOTH OUTPUTS NEED RUNNING, so both get a hook — and `gen-harness`'s shared flake module wires
# both, beside each other, off the same read-roots guard. The wrapper its `ci` hook builds bakes
# `./ci#tests` into its own text and cannot be pointed at this one; `ci-error` is its counterpart,
# under a distinct id so the two merge rather than collide, and this file supplies only its cells.
#
#   nix-unit --flake ./ci#tests        # the suites
#   nix-unit --flake ./ci#testsError   # these cells
{
  lib,
  genMerge,
  genMergeCore,
  nixpkgsLib,
  interface,
  genMergeVocab,
  genMergeWith,
  genMergeWithScope,
  genTypes,
  genTypesFlake,
  genLinkset,
  genScope,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  cfg = args: (gm.evalModuleTree args).config;
  # `deepSeq` is the forcing idiom the ./tests suites use: the refusals below fire while the
  # config tree is realized, so a shallow force would not reach them.
  realize = args: builtins.deepSeq (cfg args) null;
  # `lint` and `mkCoreValue` carry no unrelated eagerly-computed sibling field the way the module
  # tree's `.type.description` does (door-checks.nix), so a plain `deepSeq` of their result reads
  # the door-check refusal directly.
  force = v: builtins.deepSeq v null;
  # `lazyAttrsOf` under another name, for the S1 class (a) refusals (den-hoag-9d80v): the key walk
  # reads an over-approximating container by its name, so this one stands for every one but
  # `lazyAttrsOf`, whose positions are container nodes.
  overRoot = e: t.lazyAttrsOf e // { name = "overRoot"; };

  # ── the refusal pair and its control share one skeleton ────────────────────────────────────
  # `rack.slot` is declared; `rack.stray` is not. The three fixtures differ in exactly one module,
  # so what separates refusal from absorption is that module and nothing else.
  skeleton = {
    options.rack.slot = gm.mkOption {
      type = t.str;
      default = "s";
    };
  };
  stray = {
    rack.stray = 1;
  };
  # ── the sub-protocol refusal and its control share one skeleton ─────────────────────────────
  # A type carrying an ELEMENT TYPE owes the three sub-protocol answers. These three fixtures are
  # the same hand-built type differing in exactly which of them it supplies, so what separates
  # refusal from construction is that and nothing else — not the hand-building, which the control
  # below does identically and which succeeds.
  rackOf =
    extra:
    gm.mkOptionType (
      {
        name = "rackOf";
        elemType = t.str;
        getSubOptions = _prefix: { };
        getSubModules = null;
      }
      // extra
    );

  # ── the functor refusal's subject: a SYNTHETIC foreign-relation container ──────────────────
  # A container written in the nixpkgs convention, whose `functor.payload` is the element type BARE
  # rather than a `{ elemType = …; }` row, and whose `binOp` defers to the two elements' OWN foreign
  # `typeMerge` rather than to gen-merge's `mergeTypes`. gen-aspects no longer ships this shape:
  # it was lifted field for field from gen-aspects' container as it stood when the defect this
  # refusal converts was measured, and gen-aspects has since bound its `binOp` to `mergeTypes`. It
  # stays because any consumer may still write a `binOp` that asks the elements' own relation, and
  # gen-merge's protocol owes that shape an answer; the fixture holds the protocol to it. Its type
  # `name` is kept verbatim from the lifted original so the cells' expected values are unchanged.
  foreignElemRelation = a: b: if a ? typeMerge && b ? functor then a.typeMerge b.functor else null;
  foreignRelationRootWith =
    elemType:
    gm.mkOptionType {
      name = "aspectsRoot";
      inherit elemType;
      nestedTypes = { inherit elemType; };
      functor = {
        name = "aspectsRoot";
        payload = elemType;
        binOp = a: b: if b == null then null else foreignElemRelation a b;
        type = foreignRelationRootWith;
      };
      getSubOptions = prefix: elemType.getSubOptions (prefix ++ [ "<name>" ]);
      getSubModules = elemType.getSubModules or null;
      substSubModules =
        m:
        foreignRelationRootWith (
          if elemType ? substSubModules then elemType.substSubModules m else elemType
        );
      merge = _loc: defs: (builtins.head defs).value;
    };

  # ── the declaration-merge refusal and its control share one skeleton ────────────────────────
  # One option, declared in two named files, each declaration carrying a type and nothing else.
  # The three fixtures below differ in exactly which types those are, so what separates refusal
  # from merge is the type algebra's answer about the pair and nothing else.
  declaredTwice =
    aType: bType:
    (gm.evalModuleTree {
      modules = [
        {
          _file = "a.nix";
          options.x = gm.mkOption { type = aType; };
        }
        {
          _file = "b.nix";
          options.x = gm.mkOption { type = bType; };
        }
      ];
    }).options.x.type.name;

  # gen-types' `attrs`, PROTOCOL-COMPLETED by the library's own export path rather than hand-built,
  # and reached under a non-colliding key so the linkset does not shadow it with the strategy that
  # now wins at `attrs`. Its `.name` is still `attrs`, which is exactly the hazard the relation this
  # file's `attrs-container` group reads was stated for.
  attrsCompletedLeaf = (genMergeWith (genTypes // { attrsLeaf = genTypes.attrs; })).types.attrsLeaf;

  # The same redeclaration one level down, inside a `submodule` — the nested eval carries a
  # non-empty `prefix`. `sub-a.nix` always declares `str`; the second type and its default are the
  # only things that vary between the refusal and its control.
  subHost = bType: bDefault: {
    modules = [
      {
        _file = "outer.nix";
        options.host = gm.mkOption {
          type = t.submodule [
            {
              _file = "sub-a.nix";
              options.inner = gm.mkOption {
                type = t.str;
                default = "A";
              };
            }
            {
              _file = "sub-b.nix";
              options.inner = gm.mkOption {
                type = bType;
                default = bDefault;
              };
            }
          ];
          default = { };
        };
      }
    ];
  };

  # ── the union refusal and its controls share one skeleton ───────────────────────────────────
  # `x` is `either (listOf str) str`, whose two members accept exactly what the other rejects, and
  # every fixture below declares it in `decl.nix` and defines it from named files. They differ in
  # the DEFINITIONS and in nothing else, so what separates a refusal from a merge is the definition
  # set — not the type, not the declaration, and not which file declared it.
  unionOf =
    loc: defs:
    (gm.evalModuleTree {
      modules = [
        {
          _file = "decl.nix";
          options = lib.setAttrByPath loc (gm.mkOption { type = t.either (t.listOf t.str) t.str; });
        }
      ]
      ++ map (d: {
        _file = d.file;
        config = lib.setAttrByPath loc d.value;
      }) defs;
    }).config;

  # Declaring `thing` as a leaf in one module and as an option-group in another: the decl merge
  # cannot `//` these together without emitting wrong bytes, so it refuses.
  collision = {
    modules = [
      {
        options.thing = gm.mkOption {
          type = t.str;
          default = "x";
        };
      }
      {
        options.thing.sub = gm.mkOption {
          type = t.str;
          default = "y";
        };
      }
    ];
  };

  # ── the freeform refusal's fixtures (den-hoag-5r1a7) ────────────────────────────────────────
  # Two contributions of the SAME container over element types that do not merge, plus a mergeable
  # third for the N > 2 cell. `_file` is what the refusal names, so it is the only field that
  # distinguishes `ffStrA` from `ffIntB` beyond the element type. The `_module`-routed twins are
  # the second feeder: identical contributions arriving as `config._module.freeformType` rather
  # than top-level, which the engine collects per module so N of them stay N defs.
  ffSubA = {
    _file = "A";
    freeformType = t.attrsOf (
      t.submodule {
        options.a = gm.mkOption {
          type = t.str;
          default = "a";
        };
      }
    );
  };
  ffStrA = {
    _file = "A";
    freeformType = t.attrsOf t.str;
  };
  ffIntB = {
    _file = "B";
    freeformType = t.attrsOf t.int;
  };
  ffModStrA = {
    _file = "A";
    config._module.freeformType = t.attrsOf t.str;
  };
  ffModIntB = {
    _file = "B";
    config._module.freeformType = t.attrsOf t.int;
  };
  ffUseK = {
    _file = "Z";
    config.k = { };
  };
  ffUseX = {
    _file = "Z";
    config.x = "s";
  };

  # ── the `anything` scalar tie's fixtures (den-hoag-1fu0a) ───────────────────────────────────
  # One declaration and two definitions of it differing in exactly the value, so what separates
  # refusal from a merge is the pair and nothing else. `_file` distinguishes them, and `mergeLeaf`
  # names each file in its refusal (den-hoag-ur0nr), so every message here lists `A' and `B'.
  anyDecl = {
    options.o = gm.mkOption { type = t.anything; };
  };
  anyStrA = {
    _file = "A";
    o = "x";
  };
  anyStrB = {
    _file = "B";
    o = "y";
  };
  # Two functions that AGREE pointwise, and a third that does not. Nix's `==` answers `false` for
  # any two lambdas — even for the same one — so the agreement is unobservable to the fold and the
  # pair is here to say exactly that.
  anyFnA = {
    _file = "A";
    o = _: "v";
  };
  anyFnAgreeB = {
    _file = "B";
    o = _: "v";
  };
  anyFnDisagreeB = {
    _file = "B";
    o = _: "w";
  };

  # ── declaration-plane misuse: one fixture skeleton, one message per DIAGNOSIS ───────────────
  # Every cell in the group below declares the SAME option path `a` and differs in exactly the tag
  # it misplaces there, so what separates the cells is the tag and nothing else.
  misdeclare = v: realize { modules = [ { options.a = v; } ]; };
  declLeaf = gm.mkOption {
    type = t.str;
    default = "x";
  };
  # The four combinators share ONE message shape parameterized by their path and tag — which is the
  # claim being asserted (same remedy, different tag), not a shortcut. The `option-type` cell below
  # spells its own regex out in full precisely because it must NOT match this one.
  combinatorRefusal =
    loc: tag:
    "^gen-merge: option `${loc}' is declared as the `${tag}' combinator "
    + "\\(mkMerge/mkIf/mkOrder/mkBefore/mkAfter/mkForce/mkOverride build DEFINITIONS, not "
    + "DECLARATIONS\\); move it under `config'/`imports', or write one plain attrset here$";

  # ── the SECOND call site's fixture: a DECLARED-ONLY misuse on the warm path ─────────────────
  # `footOf`'s `declPaths` reads a module's own raw `options`, not `allOptions`, so the fold's guard
  # never reaches it. `moduleDefFootprint` is DEFINITION-driven, so a key that is declared and never
  # defined is not visited by it either — which is why this fixture defines nothing for `misuse`.
  # Read through `.warmDecision.remerged` ONLY: never `.config`, never `.reused`, never `.options`,
  # each of which is already reached by the fold's guard and would make the cell pass for the wrong
  # reason.
  # A lax nested tree (`check = false`) and a definition of it that carries a key it does not declare.
  laxNest =
    (gm.evalModuleTree {
      check = false;
      modules = [ { options.a = gm.mkOption { type = t.str; }; } ];
    }).type;
  laxNestDef = {
    _file = "C";
    config.nest = {
      a = "declared";
      z = "dropped";
    };
  };
  coldOf = mods: gm.evalModuleTree { modules = mods; };
  warmOf =
    base: edited:
    gm.evalModuleTree {
      modules = base ++ edited;
      warmFrom = coldOf base;
      editedModules = edited;
    };
  warmBase = [
    {
      _file = "base";
      options.clean = declLeaf;
      config.clean = "c";
    }
  ];
  remergedKeys = edited: builtins.attrNames (warmOf warmBase edited).warmDecision.remerged;

  # ── the module reader: module syntax refused by name, through every reader path ─────────────
  # `readerDecl` declares `a` and `foo`; `readerBad` is a structured module carrying a surplus key.
  # Each refusal cell first forces its LIVE CONTROL through the same path — C0 `{ config.a = 2; }`
  # must read 2, or C1 `{ foo = 1; }` must read 1 for the `disabledModules` shapes — and throws a
  # different message when it does not, so a reader that refused everything fails the match.
  readerDecl = {
    options.a = gm.mkOption {
      type = t.int;
      default = 0;
    };
    options.foo = gm.mkOption {
      type = t.int;
      default = 0;
    };
  };
  readerBad = {
    bogus = 1;
    config.a = 2;
  };
  readerC0 = {
    config.a = 2;
  };
  withControl =
    ctl: want: v:
    if ctl == want then v else throw "reader control failed: ${builtins.toJSON ctl}";
  viaTop =
    m:
    cfg {
      modules = [
        readerDecl
        {
          _file = "/real/M.nix";
          imports = [ m ];
        }
      ];
    };
  viaTopLax =
    m:
    map (u: u.path)
      (gm.evalModuleTree {
        modules = [
          readerDecl
          m
        ];
        check = false;
      }).undeclared;
  viaSubmodule =
    m:
    (cfg {
      modules = [
        { options.s = gm.mkOption { type = t.submodule readerDecl; }; }
        {
          _file = "/real/S.nix";
          config.s = m;
        }
      ];
    }).s;
  viaDeferred =
    m:
    cfg {
      modules = [
        readerDecl
        (cfg {
          modules = [
            { options.d = gm.mkOption { type = t.deferredModule; }; }
            {
              _file = "/real/D.nix";
              config.d = m;
            }
          ];
        }).d
      ];
    };
  viaLint =
    m:
    gm.lint {
      modules = [
        readerDecl
        ({ _file = "/real/L.nix"; } // m)
      ];
    };
  surplusKeyMsg =
    file: key:
    "^gen-merge: module `${file}' has an unsupported attribute `${key}'\\. A module carrying a top-level `config' or `options' reads only the module keys; move ${key} into its explicit `config', or drop `config'/`options' and write every configuration key at the top level\\.$";
  surplusMsg = file: surplusKeyMsg file "bogus";
  readerInt0 = gm.mkOption {
    type = t.int;
    default = 0;
  };
  # The typo `option.c` (for `options.c`), and its spelled-right twin, for the declaration-only reads.
  readerTypo = {
    _file = "/real/T.nix";
    options.b = readerInt0;
    option.c = readerInt0;
  };
  readerRight = {
    _file = "/real/R.nix";
    options.b = readerInt0;
    options.c = readerInt0;
  };
  readerDeclares = m: builtins.attrNames ((t.submodule m).substructure.declares [ "s" ]);
  # Module B declares `x`, keyed so a `disabledModules` entry can name it.
  readerKeyed = {
    key = "B";
    options.x = readerInt0;
  };
  # A module function whose result is itself: the reference's `does not look like a module` shape.
  readerSelfFn = { lib, ... }: readerSelfFn;
  readerOptionNames =
    m:
    builtins.attrNames
      (gm.evalModuleTree {
        modules = [
          readerDecl
          m
        ];
      }).options;
  readerDeclaredNames =
    m:
    builtins.attrNames (
      gm.declaredOptions {
        modules = [
          readerDecl
          m
        ];
      }
    );
  readerPathA =
    p:
    (cfg {
      modules = [
        readerDecl
        p
      ];
    }).a;
  fnResultMsg =
    file: type:
    "^gen-merge: module `${file}' is a function whose result is ${type}, not an attribute set\\. A module function is applied once, to the module arguments, and must return the module itself; .* is not a module\\.$";
  disabledMsg =
    file:
    "^gen-merge: module `${file}' sets `disabledModules'\\. gen-merge does not implement module removal \\(it is deferred work\\): the modules it names would stay enabled here, where the reference module system removes them\\. Remove the key; it is refused by presence, an empty list included\\.$";
  # A module reading the `pkgs` argument into `x`, and a module defining it from `file`.
  moduleArgsReader = [
    (
      { pkgs, ... }:
      {
        options.x = gm.mkOption { type = t.str; };
        config.x = pkgs;
      }
    )
  ];
  argAt = file: v: {
    _file = file;
    config._module.args.pkgs = v;
  };
  moduleArgsDupMsg =
    files:
    "^gen-merge: module argument `pkgs' \\(`_module\\.args\\.pkgs'\\) is defined multiple times, and a module argument must be unique; defined in ${files}$";
  # `_module.<x>`: one declared option beside the module under test.
  moduleKey = file: m: [
    { options.x = gm.mkOption { default = "dflt"; }; }
    ({ _file = file; } // m)
  ];
  orphanMsg = p: "^gen-merge: option `${p}' does not exist \\(no freeformType to absorb it\\)$";
  checkMsg =
    file:
    "^gen-merge: `_module\\.check' is not read from a module: pass it as `evalModuleTree \\{ check = …; }'; defined in ${file}$";
  specialArgsMsg =
    file:
    "^gen-merge: `_module\\.specialArgs' is set by the caller, never by a module: pass it as `evalModuleTree \\{ specialArgs = …; }'; defined in ${file}$";
  nonAttrModuleMsg =
    file: "^gen-merge: `_module' must be an attribute set, and this one is int; defined in ${file}$";
in
{
  config = {
    flake.testsError.refusal-messages = {
      # The message NAMES THE FULL PATH of the key it could not place — `rack.stray`, not `rack`
      # and not a count. A refusal that only said "undeclared key" would leave the caller to
      # re-derive which one, over a tree the engine has already walked.
      test-undeclared-key-refusal-names-the-full-path = {
        expr = realize {
          modules = [
            skeleton
            stray
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `rack\\.stray' does not exist \\(no freeformType to absorb it\\)$";
        };
      };
      # The collision refusal names the option that collided, which is the one piece of the
      # module set the author has to go edit.
      test-leaf-group-collision-refusal-names-the-option = {
        expr = realize collision;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `thing' is declared both as an option and as an option-group \\(leaf/group collision\\)$";
        };
      };
      # LIVE CONTROL, same run: the same skeleton and the same stray key, plus a `freeformType`
      # to absorb it, evaluates — and the declared sibling survives alongside the absorbed key.
      # Without it the two cells above are consistent with a surface that refuses everything. It
      # is an `expected` cell in an `expectedError` output on purpose: a control has to run in
      # the same invocation as the thing it controls, or it controls nothing.
      test-freeform-absorbs-the-same-key-control = {
        expr = cfg {
          modules = [
            skeleton
            stray
            { freeformType = t.lazyAttrsOf t.raw; }
          ];
        };
        expected = {
          rack = {
            slot = "s";
            stray = 1;
          };
        };
      };
      # A LEAF `freeformType` REFUSES CONFLICTING UNDECLARED DEFS BY NAME, CATCHABLY. The leaf folds
      # the plane as one value by the engine's leaf fold, so two files defining different keys are a
      # conflict, named with both files, as nixpkgs names it; the fold was once `null`, and applying it
      # aborted uncatchably with no name at all. The accepting arm is `../tests/undeclared.nix` cell 20.
      test-leaf-freeformtype-conflict-names-both-files = {
        expr = realize {
          modules = [
            { freeformType = t.raw; }
            {
              _file = "/demo/a.nix";
              q = "a";
            }
            {
              _file = "/demo/b.nix";
              r = "b";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `' has conflicting definitions:\n- In `/demo/b\\.nix': <a set>\n- In `/demo/a\\.nix': <a set>$";
        };
      };
      # TWO MODULES DEFINING ONE `_module.args` ENTRY REFUSE BY NAME, in either order, naming the
      # argument and both files, as nixpkgs' `lazyAttrsOf raw` does. The fold here was a last-wins
      # `recursiveUpdate`, so the pair read "b" and, reversed, "a", at rc 0. Identical values refuse
      # too (`raw` merges with `mergeOneOption`). The accepting arms are `./tests/merge.nix`
      # `moduleArgs` (one definition, two distinct names, `mkForce` deciding a pair).
      test-module-args-same-name-pair-names-the-arg-and-both-files = {
        expr = realize {
          modules = moduleArgsReader ++ [
            (argAt "/demo/a.nix" "a")
            (argAt "/demo/b.nix" "b")
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = moduleArgsDupMsg "/demo/a\\.nix, /demo/b\\.nix";
        };
      };
      test-module-args-same-name-pair-reversed-names-the-arg-and-both-files = {
        expr = realize {
          modules = moduleArgsReader ++ [
            (argAt "/demo/b.nix" "b")
            (argAt "/demo/a.nix" "a")
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = moduleArgsDupMsg "/demo/b\\.nix, /demo/a\\.nix";
        };
      };
      test-module-args-identical-pair-refuses-by-name = {
        expr = realize {
          modules = moduleArgsReader ++ [
            (argAt "/demo/a.nix" "a")
            (argAt "/demo/b.nix" "a")
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = moduleArgsDupMsg "/demo/a\\.nix, /demo/b\\.nix";
        };
      };
      # An `mkMerge` inside ONE module carrying both definitions names that file once, with the
      # count, rather than twice as if two modules defined it.
      test-module-args-same-name-pair-in-one-module-names-the-file-once = {
        expr = realize {
          modules = moduleArgsReader ++ [
            {
              _file = "/demo/m.nix";
              config = gm.mkMerge [
                { _module.args.pkgs = "a"; }
                { _module.args.pkgs = "b"; }
              ];
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = moduleArgsDupMsg "/demo/m\\.nix \\(2 definitions\\)";
        };
      };
      # A TOP-LEVEL `_module` BESIDE `config`/`options` IS REFUSED BY NAME, naming the module file,
      # as nixpkgs' `unifyModuleSyntax` refuses it: `_module` is not one of its `attrsToRemove`.
      # Two sites in one module are two definitions with no order between them; the trigger is the
      # top-level key, whatever either site holds. Control: the same definition at one site resolves
      # (`./tests/merge.nix` `moduleArgs`).
      test-module-args-both-sites-of-one-module-refuse-by-name = {
        expr = realize {
          modules = moduleArgsReader ++ [
            {
              _file = "/demo/both.nix";
              _module.args.pkgs = "a";
              config._module.args.pkgs = "b";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = surplusKeyMsg "/demo/both\\.nix" "_module";
        };
      };
      # A property at either site changes nothing: the config-site argument was dropped silently
      # when the top-level site was an `mkIf`.
      test-module-args-mkif-top-beside-config-refuses-by-name = {
        expr = realize {
          modules = [
            (
              { qq, ... }:
              {
                options.x = gm.mkOption { type = t.str; };
                config.x = qq;
              }
            )
            {
              _file = "/demo/both.nix";
              _module = gm.mkIf true { args.pkgs = "a"; };
              config._module.args.qq = "q";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = surplusKeyMsg "/demo/both\\.nix" "_module";
        };
      };
      test-module-args-top-beside-options-only-refuses-by-name = {
        expr = realize {
          modules = moduleArgsReader ++ [
            {
              _file = "/demo/top.nix";
              _module.args.pkgs = "a";
              options.y = gm.mkOption { default = 1; };
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = surplusKeyMsg "/demo/top\\.nix" "_module";
        };
      };
      test-module-freeformtype-both-sites-of-one-module-refuse-by-name = {
        expr = realize {
          modules = [
            {
              _file = "/demo/both.nix";
              options.x = gm.mkOption { default = 1; };
              _module.freeformType = t.attrsOf t.int;
              config._module.freeformType = t.lazyAttrsOf t.raw;
              config.y = "s";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = surplusKeyMsg "/demo/both\\.nix" "_module";
        };
      };
      # A `_module.<x>` THE ENGINE DOES NOT OWN IS AN ORDINARY CONFIG PATH (den-hoag-lnleu). nixpkgs
      # refuses it as an option that does not exist; it was dropped here with nothing said. Every
      # spelling meets the same orphan refusal: `config.`, the shorthand, a misspelt `args`, an
      # `mkIf false` (captured undischarged, as `.undeclared` states), one beside a read `args`, and
      # one inside a submodule value, refused at the tree that owns it.
      test-module-unknown-key-refused-by-name = {
        expr = realize { modules = moduleKey "/g/B.nix" { config._module.bogus = 1; }; };
        expectedError = {
          type = "ThrownError";
          msg = orphanMsg "_module\\.bogus";
        };
      };
      test-module-unknown-key-shorthand-refused-by-name = {
        expr = realize { modules = moduleKey "/g/B.nix" { _module.bogus = 1; }; };
        expectedError = {
          type = "ThrownError";
          msg = orphanMsg "_module\\.bogus";
        };
      };
      test-module-misspelt-args-refused-by-name = {
        expr = realize { modules = moduleKey "/g/A.nix" { config._module.arg.pkgs = 1; }; };
        expectedError = {
          type = "ThrownError";
          msg = orphanMsg "_module\\.arg";
        };
      };
      test-module-unknown-key-under-mkif-false-refused-by-name = {
        expr = realize {
          modules = moduleKey "/g/B.nix" { config._module = gm.mkIf false { bogus = 1; }; };
        };
        expectedError = {
          type = "ThrownError";
          msg = orphanMsg "_module\\.bogus";
        };
      };
      test-module-unknown-key-beside-args-refused-by-name = {
        expr = realize {
          modules = moduleKey "/g/A.nix" {
            config._module = {
              args.pkgs = "P";
              bogus = 1;
            };
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = orphanMsg "_module\\.bogus";
        };
      };
      test-module-unknown-key-in-a-submodule-refused-by-name = {
        expr = realize {
          modules = moduleKey "/g/N.nix" {
            options.n = gm.mkOption { type = t.submodule { options.a = gm.mkOption { default = 1; }; }; };
            config.n._module.bogus = 1;
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = orphanMsg "n\\._module\\.bogus";
        };
      };
      # Under a `_module.freeformType` the key is absorbed (`./tests/module-key.nix`), so a pair
      # defining it twice refuses through the freeform type's own merge, naming both files. The text
      # is gen-merge's `lazyAttrsOf raw`; nixpkgs' says `is defined multiple times`.
      test-module-unknown-key-pair-under-a-freeformtype-names-both-files = {
        expr = realize {
          modules = [
            { options.x = gm.mkOption { default = "dflt"; }; }
            { config._module.freeformType = t.lazyAttrsOf t.raw; }
            {
              _file = "/g/B1.nix";
              config._module.bogus = 1;
            }
            {
              _file = "/g/B2.nix";
              config._module.bogus = 2;
            }
            (
              { config, ... }:
              {
                options.r = gm.mkOption { };
                config.r = config._module.bogus or "ABSENT";
              }
            )
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `_module' has conflicting definitions:\n- In `/g/B2\\.nix': <a set>\n- In `/g/B1\\.nix': <a set>$";
        };
      };
      # THE ENGINE'S OWN `_module` INPUTS A MODULE MAY NOT SET, refused by presence naming the file.
      # `specialArgs` and `check` come through `evalModuleTree`'s door; nixpkgs is silent on a module's
      # `specialArgs` and honours its `check`, which this engine does not read (Q1 decides). The
      # `check` refusal fires before the realizer, so it is what an undeclared sibling meets first, and
      # it fires under `mkIf false` too, as `disabledModules` does.
      test-module-special-args-refused-by-name = {
        expr = realize { modules = moduleKey "/g/S.nix" { config._module.specialArgs.z = 1; }; };
        expectedError = {
          type = "ThrownError";
          msg = specialArgsMsg "/g/S\\.nix";
        };
      };
      test-module-non-attrset-refused-by-name = {
        expr = realize { modules = moduleKey "/g/N.nix" { config._module = 5; }; };
        expectedError = {
          type = "ThrownError";
          msg = nonAttrModuleMsg "/g/N\\.nix";
        };
      };
      test-module-check-refused-by-presence = {
        expr = realize { modules = moduleKey "/g/C.nix" { config._module.check = false; }; };
        expectedError = {
          type = "ThrownError";
          msg = checkMsg "/g/C\\.nix";
        };
      };
      test-module-check-refused-before-an-undeclared-sibling = {
        expr = realize {
          modules = moduleKey "/g/C.nix" { config._module.check = false; } ++ [ { y = 1; } ];
        };
        expectedError = {
          type = "ThrownError";
          msg = checkMsg "/g/C\\.nix";
        };
      };
      test-module-check-under-mkif-false-refused-by-presence = {
        expr = realize {
          modules = moduleKey "/g/C.nix" { config._module = gm.mkIf false { check = false; }; };
        };
        expectedError = {
          type = "ThrownError";
          msg = checkMsg "/g/C\\.nix";
        };
      };
      # `_module` DECLARED AS ONE OPTION would swallow every `_module.<x>` and see the engine's own
      # keys taken out of it. nixpkgs refuses the declaration (it would be a parent of its own
      # `_module` options); so does this engine, naming the declaring file.
      test-module-declared-as-a-single-option-refused-by-name = {
        expr = realize {
          modules = moduleKey "/g/L.nix" {
            options._module = gm.mkOption {
              type = t.attrsOf t.anything;
              default = { };
            };
            config._module.bogus = 1;
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `_module' is declared as a single option, but the engine owns its sub-keys `args', `freeformType', `check' and `specialArgs': declare `options\\._module\\.<name>' instead; declared in /g/L\\.nix$";
        };
      };
      # A `submodule`-TYPED `_module` is the exception: nixpkgs merges its own `_module` options into
      # the submodule and reads `_module.foo` and `_module.args.pkgs` alike. This engine has no
      # `moduleOwnKeys` declared as options to merge into it, so it refuses the declaration by name.
      test-module-declared-as-a-submodule-option-refused-by-name = {
        expr = realize {
          modules = moduleKey "/g/S.nix" {
            options._module = gm.mkOption {
              type = t.submodule { options.foo = gm.mkOption { default = 1; }; };
              default = { };
            };
            config._module.foo = 2;
            config._module.args.pkgs = "P";
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `_module' is declared as a single option, but the engine owns its sub-keys `args', `freeformType', `check' and `specialArgs': declare `options\\._module\\.<name>' instead; declared in /g/S\\.nix$";
        };
      };
      # The lint refuses what the engine refuses before merging. An unknown `_module.<x>` is no lint
      # finding (`./tests/module-key.nix`): both engines refuse or absorb it alike.
      test-module-special-args-refused-by-lint = {
        expr = withControl (viaLint readerC0) [ ] (viaLint {
          config._module.specialArgs.z = 1;
        });
        expectedError = {
          type = "ThrownError";
          msg = specialArgsMsg "/real/L\\.nix";
        };
      };
      test-module-non-attrset-refused-by-lint = {
        expr = withControl (viaLint readerC0) [ ] (viaLint {
          config._module = 5;
        });
        expectedError = {
          type = "ThrownError";
          msg = nonAttrModuleMsg "/real/L\\.nix";
        };
      };
      test-module-check-refused-by-lint = {
        expr = withControl (viaLint readerC0) [ ] (viaLint {
          config._module.check = false;
        });
        expectedError = {
          type = "ThrownError";
          msg = checkMsg "/real/L\\.nix";
        };
      };
      # A NESTED TREE'S FINDING IS REFUSED BY NAME UNDER A `freeformType` TOO. `nest.z` has an
      # associated option (`nest`, whose declared type is a lax moduleTree that drops `z`), so it is
      # outside the freeform type's domain: it can be neither absorbed nor dropped silently, and at
      # `check = true` it is refused, naming the finding's own absolute path.
      test-nested-finding-refused-under-a-freeformtype-names-its-path = {
        expr = realize {
          check = true;
          modules = [
            {
              config._module.freeformType = t.lazyAttrsOf t.anything;
              options.nest = gm.mkOption { type = laxNest; };
            }
            laxNestDef
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `nest\\.z' is not declared by the nested tree that owns it$";
        };
      };
      # THE FRAME OF THAT PATH. A finding is ABSOLUTE (the nested eval ran at `prefix = abs`), so the
      # refusal names it as is: at `prefix = [ "sub" ]` the message reads `sub.nest.z`, never
      # `sub.sub.nest.z`. At `prefix = [ ]` the two frames coincide, which is why the cell above
      # cannot see a message that prepends `prefix` a second time and this one can.
      test-nested-finding-refusal-is-not-prefixed-twice = {
        expr = realize {
          check = true;
          prefix = [ "sub" ];
          modules = [
            { options.nest = gm.mkOption { type = laxNest; }; }
            laxNestDef
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `sub\\.nest\\.z' is not declared by the nested tree that owns it$";
        };
      };
    };

    # A redeclared option whose two types do not merge is refused BY NAME. The message is the whole
    # of what the author gets — there is no bad intermediate to inspect, because the point of the
    # rule is that one is never built.
    #
    # ★ EVERY PATTERN HERE IS ANCHORED `^…$`, for the reason stated below the sub-protocol cells.
    # These messages DO carry ERE metacharacters — the parenthesised type pair, and the `.` in every
    # file name — so each is escaped and the anchors are left to carry only the ends.
    flake.testsError.declaration-merge = {
      # The message names the option, the two types that could not be combined, and the files that
      # declared them: an author who is told only "types do not merge" still has to find both.
      test-unmergeable-redeclaration-refused-by-name = {
        expr = declaredTwice t.str t.int;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`string' and `int'\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # THE PARAMETRIC ARM. A gen-types parametric leaf's `typeMergeRel` decides by MINTED
      # CONSTRUCTION, not by name, and two same-named `enum`s over different value sets now merge to
      # their union (the value cells are in ./tests/decl-merge.nix). What still refuses says WHICH of
      # two things is missing: a law for the two constructions, though both payloads are readable, or
      # a readable payload at all. The messages show the names matching while the pair does not merge,
      # which is what distinguishes this arm from the one above.
      test-parametric-redeclaration-without-a-law-names-the-constructor = {
        expr = declaredTwice (t.struct "s" { a = t.str; }) (t.struct "s" { a = t.int; });
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`s' and `s', which mint to different constructions, and gen-merge has no reconciliation law for `struct'\\); declared in a\\.nix, b\\.nix$";
        };
      };
      test-parametric-redeclaration-across-constructors-names-both = {
        expr = declaredTwice (t.enum "e" [ "a" ]) (t.struct "e" { a = t.str; });
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`e' and `e', which mint to different constructions, and gen-merge has no reconciliation law between `enum' and `struct'\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # Two names still refuse: the union is a law over ONE enum, as nixpkgs' functor-name clause has it.
      test-enum-redeclaration-under-two-names-refused = {
        expr = declaredTwice (t.enum "e" [ "a" ]) (t.enum "f" [ "b" ]);
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`e' and `f', which mint to different constructions, and gen-merge reconciles two `enum's only under one name\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # ★ THE READ IS TOTAL. A sealed partner has no payload `payloadOf` can certify, and the reader
      # refuses it by `throw`; the refusal a declarer sees must still be THIS library's, naming the
      # pair, and never the reader's. RED against a relation calling `payloadOf` unguarded, whose
      # message is gen-types' "has no readable construction payload".
      test-enum-against-a-sealed-partner-keeps-this-librarys-refusal = {
        expr = declaredTwice (t.enum "e" [ "a" ]) (t.typedef' "e" (_: null));
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`e' and `e', which mint to different constructions and carry no readable component values to reconcile\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # The path is the FULL option path, and the file list is EVERY declaring file rather than the
      # two the merge happened to be holding: the list folds from the last declaration back, so
      # `c.nix` against `b.nix` refuses first and `a.nix` is party to no refusing step, and a message
      # naming only the pair at the point of refusal would send the author to two of the three
      # modules they have to reconcile.
      test-refusal-names-the-full-path-and-every-declaring-file = {
        expr =
          (gm.evalModuleTree {
            modules = [
              {
                _file = "a.nix";
                options.rack.slot = gm.mkOption { type = t.str; };
              }
              {
                _file = "b.nix";
                options.rack.slot = gm.mkOption { type = t.str; };
              }
              {
                _file = "c.nix";
                options.rack.slot = gm.mkOption { type = t.int; };
              }
            ];
          }).options.rack.slot.type.name;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `rack\\.slot' is declared with types that do not merge \\(`string' and `int'\\); declared in a\\.nix, b\\.nix, c\\.nix$";
        };
      };
      # INSIDE A SUBMODULE the engine runs with a non-empty `prefix`, so the loc the merge reports
      # is prefixed while the modules it is looking the declaration up in are not. The message has
      # to name the OUTER path and the INNER files: `host.inner`, declared in the submodule's own
      # two modules and not in the one that declared `host`. Mismatch the two and the path survives
      # while the file list comes back empty, which is a refusal that names half of what it needs.
      test-refusal-inside-a-submodule-names-outer-path-and-inner-files = {
        expr = realize (subHost t.int 7);
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `host\\.inner' is declared with types that do not merge \\(`string' and `int'\\); declared in sub-a\\.nix, sub-b\\.nix$";
        };
      };
      # LIVE CONTROLS, same run, same skeletons: a pair the algebra DOES merge is not refused — at
      # the root, where the merged declaration answers with the algebra's type, and inside the
      # submodule, where it evaluates to a value. Without them the cells above are consistent with a
      # declaration path that refuses every redeclaration.
      test-mergeable-redeclaration-is-not-refused-control = {
        expr = declaredTwice t.str t.str;
        expected = "string";
      };
      test-mergeable-redeclaration-in-a-submodule-control = {
        expr = cfg (subHost t.str "B");
        expected = {
          host = {
            inner = "B";
          };
        };
      };
    };

    # `attrs` — THE NULLARY CONTAINER'S TWO REFUSALS AND ITS NAME COLLISION.
    #
    # ★★ EVERY CELL HERE READS THE MESSAGE BECAUSE THE BIT DOES NOT DISCRIMINATE. Before the type
    # was constructed the engine refused all three of these inputs too — a rejected definition, a
    # same-key collision and a redeclaration against the other spelling — and two of the three threw
    # `has conflicting definitions`, which a `tryEval` failure bit cannot tell from the refusals
    # below. A cell asserting only that it threw passes on the unrepaired tree.
    flake.testsError.attrs-container = {
      # A DEFINITION THE TYPE CANNOT CONSUME IS REFUSED BEFORE THE FOLD, and the refusal names the
      # FILE. That last conjunct is the whole cell: the pre-construction refusal was catchable and
      # named both the option and `attrs`, and named no file, so every other conjunct here was
      # already satisfied by the state this cell exists to exclude.
      test-attrs-rejected-definition-refuses-naming-the-file = {
        expr = realize {
          modules = [
            { options.x = gm.mkOption { type = t.attrs; }; }
            {
              _file = "a.nix";
              x = "not-an-attrset";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' has definitions `attrs' cannot consume \\(a\\.nix\\)$";
        };
      };
      # THE SAME INPUT ONE TYPE OVER REFUSES THE SAME WAY. `attrsOf` once indexed the definition by
      # key without asking its domain first, so the interpreter answered with a raw `TypeError`
      # naming neither the option nor the file. Every structural container now checks its domain
      # through the one binding `attrs` uses (`refusingOutside`), so the two refusals differ only in
      # the type they name; the per-member cells are the `structural-domain` group.
      test-attrsOf-on-the-same-input-refuses-naming-the-file = {
        expr = realize {
          modules = [
            { options.x = gm.mkOption { type = t.attrsOf t.int; }; }
            {
              _file = "a.nix";
              x = "not-an-attrset";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' has definitions `attrsOf' cannot consume \\(a\\.nix\\)$";
        };
      };
      # A SURVIVING SAME-KEY COLLISION IS AN UNRESOLVED AMBIGUITY, NOT AN OVERRIDE (ADR-0029): the
      # priority pass has already resolved every intended override by the time this fold runs. The
      # message names the KEY, which is the part the author has to go and reconcile and the part the
      # engine's own `has conflicting definitions` never carried.
      test-attrs-same-key-collision-refuses-naming-the-key = {
        expr = realize {
          modules = [
            { options.x = gm.mkOption { type = t.attrs; }; }
            {
              _file = "a.nix";
              x.a = 1;
            }
            {
              _file = "b.nix";
              x.a = 2;
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' has `attrs' definitions that collide at `a' \\(b\\.nix, a\\.nix\\)$";
        };
      };
      # THE NAME COLLISION, END TO END, IN BOTH ORDERS. A redeclaration step asks the EARLIER
      # declaration's gen-native relation first (a veto no later relation overrules) and otherwise
      # lets the LATER one decide, so gen's `attrs` refuses its foldless partner whichever module
      # declares it: first (the veto) or second (it decides). The reverse-order cells below pin
      # the second.
      #
      # The reason names the DISCRIMINATING FACT rather than the pair, because the pair is the same
      # name twice and would tell the reader nothing: both partners below really are called `attrs`.
      test-attrs-redeclared-against-the-shadowed-predicate-refuses = {
        expr = declaredTwice t.attrs attrsCompletedLeaf;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`attrs' and a partner named `attrs' that states no fold of its own\\); declared in a\\.nix, b\\.nix$";
        };
      };
      test-attrs-redeclared-against-the-foreign-spelling-refuses = {
        expr = declaredTwice t.attrs nixpkgsLib.types.attrs;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`attrs' and a partner named `attrs' that states no fold of its own\\); declared in a\\.nix, b\\.nix$";
        };
      };
      test-attrs-redeclared-after-the-foreign-spelling-refuses = {
        expr = declaredTwice nixpkgsLib.types.attrs t.attrs;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`attrs' and a partner named `attrs' that states no fold of its own\\); declared in a\\.nix, b\\.nix$";
        };
      };
      test-attrs-redeclared-after-the-shadowed-predicate-refuses = {
        expr = declaredTwice attrsCompletedLeaf t.attrs;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`attrs' and a partner named `attrs' that states no fold of its own\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # e07bf: a refusal the DECIDING relation words is that relation's text, deciding type first.
      test-a-relation-worded-refusal-names-the-deciding-type-first = {
        expr =
          declaredTwice
            (gm.evalModuleTree {
              check = false;
              modules = [ { options.known = gm.mkOption { type = t.str; }; } ];
            }).type
            (t.submodule { options.known = gm.mkOption { type = t.str; }; });
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`submodule' and `moduleTree'\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # LIVE CONTROL, same run and same helper — an `expected` cell in an `expectedError` output on
      # purpose, exactly as the `declaration-merge` group's controls are. `attrs` against ITSELF
      # merges, so the two cells above read the partner's foldlessness rather than the shared name.
      # A relation refusing every same-named partner passes both of them and breaks the ordinary
      # redeclaration every consumer hits.
      test-attrs-redeclared-against-itself-merges-control = {
        expr = declaredTwice t.attrs t.attrs;
        expected = "attrs";
      };
    };

    # A STRUCTURAL CONTAINER REFUSES A DEFINITION OUTSIDE ITS DOMAIN BY NAME, BEFORE ITS FOLD RUNS
    # (`refusingOutside`, lib/types.nix). Before it did, `listOf`/`attrsOf`/`lazyAttrsOf` aborted in
    # the interpreter (`TypeError`, escaping `tryEval`, naming neither option nor file),
    # `deferredModule` accepted the value silently, and `submodule` refused with the module
    # reader's text, which names neither. Every pattern is anchored `^…$`, so each cell reads the
    # option, the type and the file, and the reader's text cannot pass it.
    flake.testsError.structural-domain =
      let
        defined =
          ty: defs:
          realize {
            modules = [ { options.o = gm.mkOption { type = ty; }; } ] ++ defs;
          };
        at = file: v: {
          _file = file;
          o = v;
        };
        refuses = o: ty: file: {
          type = "ThrownError";
          msg = "^gen-merge: option `${o}' has definitions `${ty}' cannot consume \\(${file}\\)$";
        };
        sub = t.submodule {
          options.a = gm.mkOption {
            type = t.int;
            default = 0;
          };
        };
      in
      {
        test-listOf-refuses-a-non-list-definition = {
          expr = defined (t.listOf t.int) [ (at "/p/F.nix" 5) ];
          expectedError = refuses "o" "listOf" "/p/F\\.nix";
        };
        test-attrsOf-refuses-a-non-attrset-definition = {
          expr = defined (t.attrsOf t.int) [ (at "/p/F.nix" 5) ];
          expectedError = refuses "o" "attrsOf" "/p/F\\.nix";
        };
        test-lazyAttrsOf-refuses-a-non-attrset-definition = {
          expr = defined (t.lazyAttrsOf t.int) [ (at "/p/F.nix" [ 1 ]) ];
          expectedError = refuses "o" "lazyAttrsOf" "/p/F\\.nix";
        };
        test-deferredModule-refuses-a-non-module-definition = {
          expr = defined t.deferredModule [ (at "/p/F.nix" 5) ];
          expectedError = refuses "o" "deferredModule" "/p/F\\.nix";
        };
        test-submodule-refuses-a-non-module-definition-naming-option-and-file = {
          expr = defined sub [ (at "/p/F.nix" 5) ];
          expectedError = refuses "o" "submodule" "/p/F\\.nix";
        };
        # THE FORCED-CONDITION LEAK (9f4bn's adjacent finding). `mkForce (mkIf false …)` survives
        # discharge as the `mkIf` record itself, and wins on priority, so the fold is handed a set
        # where it expects a list. The guard reads the definitions AFTER discharge — where nixpkgs'
        # `checkedAndMerged` reads `defsFinal` — so only the leaking file is named, not `G.nix`,
        # whose definition lost on priority.
        test-listOf-refuses-a-forced-condition-leak = {
          expr = defined (t.listOf t.int) [
            (at "/p/F.nix" (gm.mkForce (gm.mkIf false [ 1 ])))
            (at "/p/G.nix" [ 2 ])
          ];
          expectedError = refuses "o" "listOf" "/p/F\\.nix";
        };
        test-listOf-submodule-refuses-a-forced-condition-leak = {
          expr = defined (t.listOf sub) [
            (at "/p/F.nix" (gm.mkForce (gm.mkIf false [ { a = 1; } ])))
            (at "/p/G.nix" [ { a = 2; } ])
          ];
          expectedError = refuses "o" "listOf" "/p/F\\.nix";
        };
        # THE NESTED POSITION: the inner container's fold is reached through the element path, so
        # the location is the element's and the type named is the inner one.
        test-nested-listOf-in-attrsOf-refuses-at-the-key = {
          expr = defined (t.attrsOf (t.listOf t.int)) [ (at "/p/F.nix" { k = 5; }) ];
          expectedError = refuses "o\\.k" "listOf" "/p/F\\.nix";
        };
        test-nested-attrsOf-in-listOf-refuses-at-the-index = {
          expr = defined (t.listOf (t.attrsOf t.int)) [ (at "/p/F.nix" [ 5 ]) ];
          expectedError = refuses "o\\.0" "attrsOf" "/p/F\\.nix";
        };
      };

    # The DEFINITION-side twin of `declaration-merge` above. Two equal-priority `freeformType`
    # contributions used to be resolved by taking the last: the loser was destroyed and no channel
    # said so, and where the pair was UNMERGEABLE the engine threw about the AUTHOR'S KEY — in one
    # presentation order only — for a fault living in the freeform declarations. The selection now
    # folds through `mergeTypes` and a `null` answer is a named refusal, exactly as one plane over.
    #
    # ★ TWO ORDERS, TWO REGEXES, DELIBERATELY. `mergeTypesReason` reports the pair in the order it
    # was asked, and the file list is in fold order for the same reason `declaringSitesAt` reports
    # in authored order. A cell asserting ONE message for both orders would go red against a correct
    # build, so the per-order patterns ARE the discrimination rather than a duplication of it.
    #
    # ★ EVERY PATTERN HERE IS ANCHORED `^…$`. These messages carry ERE metacharacters — the
    # parenthesised reason clause and the backquoted type names' surrounding punctuation — so each
    # is escaped and the anchors carry only the ends.
    flake.testsError.freeform-selection = {
      # Asserting the MESSAGE, not that it threw: the old site threw here too, in this order, about
      # `x'. A bare throw assertion cannot separate the two.
      test-unmergeable-freeform-pair-refused-by-name = {
        expr = realize {
          modules = [
            ffStrA
            ffIntB
            ffUseX
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the freeform type is defined with types that do not merge \\(`attrsOf' over `string' and `attrsOf' over `int', whose element types do not merge: `string' and `int'\\); defined in A, B$";
        };
      };
      # The reverse order. This is the one that did not throw at all — it returned `{ x = "s"; }` by
      # discarding `attrsOf str` — so it is what fails if the refusal is order-dependent.
      test-unmergeable-freeform-pair-refused-in-the-reverse-order = {
        expr = realize {
          modules = [
            ffIntB
            ffStrA
            ffUseX
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the freeform type is defined with types that do not merge \\(`attrsOf' over `int' and `attrsOf' over `string', whose element types do not merge: `int' and `string'\\); defined in B, A$";
        };
      };
      # The SECOND feeder, same pair. `_module.freeformType` reaches the selection as N definitions
      # rather than as one `recursiveUpdate` result, so these two cells are what fail if the
      # selection is fixed and the collapse above it is not.
      test-unmergeable-module-freeform-pair-refused-by-name = {
        expr = realize {
          modules = [
            ffModStrA
            ffModIntB
            ffUseX
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the freeform type is defined with types that do not merge \\(`attrsOf' over `string' and `attrsOf' over `int', whose element types do not merge: `string' and `int'\\); defined in A, B$";
        };
      };
      test-unmergeable-module-freeform-pair-refused-in-the-reverse-order = {
        expr = realize {
          modules = [
            ffModIntB
            ffModStrA
            ffUseX
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the freeform type is defined with types that do not merge \\(`attrsOf' over `int' and `attrsOf' over `string', whose element types do not merge: `int' and `string'\\); defined in B, A$";
        };
      };
      # THE FILE LIST IS EVERY CONTRIBUTOR, NOT THE PAIR HOLDING THE REFUSAL. The fold starts from
      # the LAST winner, so it refuses at its first step — `attrsOf str` from `A` against `attrsOf
      # int` from `B` — and `ffSubA`'s `A` is named anyway, undeduplicated and in fold order, because
      # it is a module the author still has to reconcile. Same convention, and same reason, as
      # `test-refusal-names-the-full-path-and-every-declaring-file` above.
      test-freeform-refusal-names-every-contributing-file = {
        expr = realize {
          modules = [
            ffSubA
            ffStrA
            ffIntB
            ffUseK
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the freeform type is defined with types that do not merge \\(`attrsOf' over `string' and `attrsOf' over `int', whose element types do not merge: `string' and `int'\\); defined in A, A, B$";
        };
      };
      # The runner is not uniformly throwing: the same fixture vocabulary, one contribution, returns
      # a value. The mergeable-pair and priority arms live in `ci/tests/merge.nix`, which is where a
      # cell asserting a VALUE belongs.
      test-control-a-single-freeform-contribution-returns-a-value = {
        expr = cfg {
          modules = [
            ffSubA
            ffUseK
          ];
        };
        expected = {
          k = {
            a = "a";
          };
        };
      };
    };

    # The VALUE-plane twin of `freeform-selection` above, one file over in the vocabulary
    # (den-hoag-1fu0a). `anything`'s non-structural arm ended `prelude.last vals`: two UNEQUAL
    # equal-priority definitions returned ONE of them and destroyed the other in silence, where
    # nixpkgs' `anything.merge` reaches `mergeEqualOption` and THROWS. Reproduced against the pinned
    # nixpkgs before the edit: `"x"` vs `"y"` returned a value here and refused there. The arm now
    # consults `mergeLeaf`, this engine's own agree-or-refuse leaf fold — the same relation `raw`
    # and every no-`.merge` leaf already fold by.
    #
    # ★ ASSERTING THE MESSAGE, NOT THAT IT THREW. The old site did not throw AT ALL on any of these,
    # so a bare `tryEval` cell would be satisfied by the defect's own successful answer; and the
    # nested cell's whole subject is WHICH path the refusal names, which `tryEval` discards.
    #
    # ★ EVERY PATTERN IS ANCHORED `^…$` and the option paths carry `.`, an ERE metacharacter, so the
    # separators are escaped and the anchors carry only the ends.
    flake.testsError.anything-scalar-tie = {
      test-unequal-scalar-pair-refused-by-name = {
        expr = realize {
          modules = [
            anyDecl
            anyStrA
            anyStrB
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': \"y\"\n- In `A': \"x\"$";
        };
      };
      # The reverse order. Both orders SUCCEEDED before, with two DIFFERENT wrong answers — defs
      # reach the fold in reverse module order, so `last` returned `"x"` for `[A B]` and `"y"` for
      # `[B A]`. A one-order cell would only ever have caught half of it.
      test-unequal-scalar-pair-refused-in-the-reverse-order = {
        expr = realize {
          modules = [
            anyDecl
            anyStrB
            anyStrA
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `A': \"x\"\n- In `B': \"y\"$";
        };
      };
      # THE DESCENT NAMES THE FULL PATH. The tie is under two attrset levels, reached through the
      # arm's own per-key recursion, and the refusal names `o.svc.k` rather than the option root.
      # This is the cell that fails if the arm refuses but the recursion drops `loc` — which the old
      # fold did, taking neither `loc` nor `file` past its own door.
      test-nested-scalar-tie-names-the-full-path = {
        expr = realize {
          modules = [
            anyDecl
            {
              _file = "A";
              o.svc = {
                k = "x";
                keep = "same";
              };
            }
            {
              _file = "B";
              o.svc = {
                k = "y";
                keep = "same";
              };
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o\\.svc\\.k' has conflicting definitions:\n- In `B': \"y\"\n- In `A': \"x\"$";
        };
      };
      # A HETEROGENEOUS pair. nixpkgs refuses this through a different arm — `commonType` fails
      # before any merge function is chosen, with "conflicting option types" — so this cell records
      # that gen-merge refuses the same shape and says which words it uses, rather than leaving a
      # reader to assume the two libraries' messages coincide. It used to return `1`.
      test-heterogeneous-scalar-pair-refused-by-name = {
        expr = realize {
          modules = [
            anyDecl
            {
              _file = "A";
              o = 1;
            }
            {
              _file = "B";
              o = "one";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': \"one\"\n- In `A': 1$";
        };
      };
      # ★★ A STATED DIVERGENCE FROM THE FOREIGN PROTOCOL, ASSERTED RATHER THAN INHERITED
      # (den-hoag-1fu0a). FUNCTIONS reach this arm, because gen-merge ships no `lambda` arm for
      # `anything` — the type's own header declares that absence. nixpkgs has one: it applies the
      # definitions POINTWISE and merges the results, so two functions AGREEING at every argument
      # give it a value (measured at the pinned rev: `"v"`). Here the arm is agree-or-refuse and
      # Nix's `==` answers `false` for any two lambdas — even for the same lambda — so agreement is
      # not observable and this refuses. It is stricter than nixpkgs, and strictly better than the
      # `prelude.last` selection it replaced, which returned one function and destroyed the other
      # in silence. These two cells record WHAT IS; whether `anything` should compose functions is
      # a design question filed on its own, and closing it is what turns them red.
      test-pointwise-agreeing-function-definitions-refused-though-nixpkgs-composes = {
        expr = realize {
          modules = [
            anyDecl
            anyFnA
            anyFnAgreeB
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': <a lambda>\n- In `A': <a lambda>$";
        };
      };
      # The control that keeps the cell above honest about its subject. Both arms refuse, and with
      # the SAME message — which is the finding, not a duplication of it: agreement changes nothing
      # here, where in nixpkgs it is the whole difference between a value and a refusal.
      test-disagreeing-function-definitions-refused-with-the-same-message = {
        expr = realize {
          modules = [
            anyDecl
            anyFnA
            anyFnDisagreeB
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': <a lambda>\n- In `A': <a lambda>$";
        };
      };
      # The runner is not uniformly throwing on this vocabulary: one definition attempts no merge
      # and returns a value. The equal-pair and priority arms are VALUE assertions and live in
      # `ci/tests/merge.nix`, which is where a cell asserting a value belongs.
      test-control-a-single-anything-definition-returns-a-value = {
        expr = cfg {
          modules = [
            anyDecl
            anyStrA
          ];
        };
        expected = {
          o = "x";
        };
      };
    };

    # `anything` carries a value carrying `__mint` WHOLE, by `mergeLeaf` (lib/types.nix), so two
    # minted definitions are agree-or-refuse over the whole value and a conflict is named AT THE
    # OPTION. The rebuild it replaced recursed per key and refused at an inner one (`o.name`), or
    # answered with a value.
    #
    # ★ ASSERTING THE MESSAGE, NOT THAT IT THREW: both cells THREW before the carry arm too, or
    # returned a value, and a `tryEval` cell is satisfied by any throw.
    flake.testsError.anything-carry = {
      test-two-minted-values-refused-at-the-option = {
        expr = realize {
          modules = [
            anyDecl
            {
              _file = "A";
              o = t.int;
            }
            {
              _file = "B";
              o = t.str;
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': <a set>\n- In `A': <a set>$";
        };
      };
      # ★★ THE TWIN COST, STATED. Two INDEPENDENT constructions of one minted type carry one digest
      # and are one identity (the control is `ci/tests/merge.nix`
      # `test-control-anything-twin-identity-and-one-value-twice`), but their closures are distinct,
      # so `==` answers false and the fold refuses the WHOLE value. The rebuild handed back a value
      # whose digest read cleanly — this cell's red. Reading only `__mint.minted` keeps the subject
      # the fold, not a conflicting closure the rebuild would have refused on demand.
      test-twin-minted-constructions-defined-twice-refused = {
        expr =
          (cfg {
            modules = [
              anyDecl
              {
                _file = "A";
                o = t.enum "e" [
                  "a"
                  "b"
                ];
              }
              {
                _file = "B";
                o = t.enum "e" [
                  "a"
                  "b"
                ];
              }
            ];
          }).o.__mint.minted;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': <a set>\n- In `A': <a set>$";
        };
      };
    };

    # ── the leaf fold's REFUSAL half, met DIRECTLY rather than through a type's arm (den-hoag-txdgz)
    # `mergeLeaf` is agree-or-refuse, and every cell above reaches it through `anything`'s
    # non-structural arm, which is one member of the class that rides it. These are the same fold on
    # the class's own members: `raw` is the only strategy in lib/types.nix bringing no `mergeDefs`,
    # and no gen-types checker brings one at all, so both arrive at the engine's own leaf fold. The
    # VALUE half — equal winners collapsing — is `ci/tests/merge.nix`'s `leafFold` group, which is
    # where a cell asserting a value belongs.
    #
    # ★ WHAT TURNS THESE RED IS THE COLLAPSE BEING WIDENED, NOT REMOVED — the opposite direction
    # from the value cells, which is why the surface needs both. A fold that SELECTED a winner
    # instead of demanding agreement (`prelude.last vals`, the shape den-hoag-1fu0a removed one
    # vocabulary over) answers both of these with a value and destroys the other definition with no
    # diagnostic on any channel.
    #
    # ★ ANCHORED `^…$`; the option path here is a bare `o` and carries no ERE metacharacter, so the
    # anchors carry the ends and nothing else needs escaping.
    flake.testsError.leaf-fold-tie = {
      test-raw-unequal-winners-refused-by-name = {
        expr = realize {
          modules = [
            { options.o = gm.mkOption { type = t.raw; }; }
            {
              _file = "A";
              o = "x";
            }
            {
              _file = "B";
              o = "y";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': \"y\"\n- In `A': \"x\"$";
        };
      };
      # A gen-types `list` CHECKER, not gen-merge's `listOf` strategy: the definitions disagree and
      # the leaf fold refuses, where a concatenating fold would answer `[ 1 2 ]` and pass.
      test-leaf-list-unequal-winners-refused-rather-than-concatenated = {
        expr = realize {
          modules = [
            { options.o = gm.mkOption { type = t.list; }; }
            {
              _file = "A";
              o = [ 1 ];
            }
            {
              _file = "B";
              o = [ 2 ];
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': <a list>\n- In `A': <a list>$";
        };
      };
      # The refusal forces NO list element (den-hoag-shared-refusal-renderer-6wtos, gate C1). List
      # `==` decides unequal lengths without reading an element, so `({ }).nope` — an uncatchable
      # abort at its WHNF, the shape of a definition naming an absent config attribute — is first
      # reached, if at all, inside the refusal. A renderer that forced it would replace this
      # catchable, named refusal with an `EvalError`.
      test-leaf-list-conflict-forces-no-element = {
        expr = realize {
          modules = [
            { options.o = gm.mkOption { type = t.list; }; }
            {
              _file = "A";
              o = [
                "a"
                ({ }).nope
              ];
            }
            {
              _file = "B";
              o = [ "b" ];
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `B': <a list>\n- In `A': <a list>$";
        };
      };
    };

    # ── the conflict refusal NAMES EVERY DEFINITION'S FILE (den-hoag-ur0nr, ADR-0025 item 1) ─────
    # Two sites throw it — the engine's own `mergeLeaf` and the boundary's `leafFold`, the fold a
    # gen type with none of its own publishes into a FOREIGN module system — and one cell per site
    # meets each through its own entry. The file is the name a reader acts on; before this refusal
    # listed the definitions, both sites named the option and neither file, so every conjunct but
    # the file lines was already satisfied by the state these cells exclude. A scalar value is
    # printed beside its file, which is the rest of what nixpkgs' `mergeEqualOption` lists.
    flake.testsError.conflict-names-files = {
      test-engine-leaf-fold-conflict-names-both-files = {
        expr = realize {
          modules = [
            { options.o = gm.mkOption { type = t.raw; }; }
            {
              _file = "a.nix";
              o = "x";
            }
            {
              _file = "b.nix";
              o = "y";
            }
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `b\\.nix': \"y\"\n- In `a\\.nix': \"x\"$";
        };
      };
      # The BOUNDARY site, reached the only way it is reached: a gen type bringing no fold, mounted
      # in a REAL `lib.evalModules`, which calls the exported `merge` with its own `{ file; value; }`
      # definitions.
      test-boundary-leaf-fold-conflict-names-both-files = {
        expr =
          builtins.deepSeq
            (nixpkgsLib.evalModules {
              modules = [
                {
                  options.o = nixpkgsLib.mkOption {
                    type = genMergeVocab.defineType {
                      name = "gauge";
                      verify = v: if builtins.isInt v then null else "expected an int";
                    };
                  };
                }
                {
                  _file = "a.nix";
                  o = 1;
                }
                {
                  _file = "b.nix";
                  o = 2;
                }
              ];
            }).config
            null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `o' has conflicting definitions:\n- In `b\\.nix': 2\n- In `a\\.nix': 1$";
        };
      };
    };

    # A UNION merges every definition through a member that accepts it, or refuses by name. These
    # cells are the only assertion available for that refusal: the shape it replaces was an
    # INTERPRETER type error — `expected a list but found a string: "b"` — which escapes
    # `builtins.tryEval`, so before the rule there was nothing for any in-language cell to observe
    # and after it there is nothing but the message. The before/after exit-code pair those cells
    # cannot carry is `ci/bench/either-totality.sh`.
    #
    # ★ EVERY PATTERN HERE IS ANCHORED `^…$`, for the reason stated below the sub-protocol cells.
    # These messages DO carry ERE metacharacters — the parenthesised member clause and the `.` in
    # every file name — so each is escaped and the anchors are left to carry only the ends.
    flake.testsError.union-merge = {
      # The definition set the interpreter used to be handed. The message names the option and, per
      # member, the files whose definitions THAT member could not take: an author told only "the
      # definitions do not agree" still has to work out which member was in play and which file
      # broke it.
      test-mixed-definitions-refused-by-name = {
        expr = builtins.deepSeq (unionOf
          [ "x" ]
          [
            {
              file = "list.nix";
              value = [ "a" ];
            }
            {
              file = "str.nix";
              value = "b";
            }
          ]
        ) null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' has definitions no single `either' member accepts \\(`listOf' rejects str\\.nix; `string' rejects list\\.nix\\)$";
        };
      };
      # EVERY offending definition is named, not the pair a dispatch happened to be holding. Two
      # list definitions and one string: the member that takes lists rejects one file, the member
      # that takes strings rejects two, and an author reconciling only the first collision the
      # interpreter would have reported would leave a definition set that still refuses.
      #
      # ★ THE FILE LIST IS IN DEFINITION ORDER — the order the merge is handed them, which is the
      # reverse of the authored module order and is why `two.nix` precedes `one.nix` here. It is a
      # set of files to go edit and no ordering is claimed for it; the cell pins the order anyway,
      # so a fold that starts handing definitions over differently says so here rather than in a
      # consumer's diagnostics. The declaration-merge messages above name files in AUTHORED order
      # because they read a site list, which this path does not have.
      test-refusal-names-every-definition-each-member-rejects = {
        expr = builtins.deepSeq (unionOf
          [ "x" ]
          [
            {
              file = "one.nix";
              value = [ "a" ];
            }
            {
              file = "two.nix";
              value = [ "b" ];
            }
            {
              file = "three.nix";
              value = "c";
            }
          ]
        ) null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' has definitions no single `either' member accepts \\(`listOf' rejects three\\.nix; `string' rejects two\\.nix, one\\.nix\\)$";
        };
      };
      # The path is the FULL option path. A union sitting under a nested option is where a message
      # can report the leaf name and read as correct, which sends the author looking for an option
      # called `slot`.
      test-refusal-names-the-full-option-path = {
        expr = builtins.deepSeq (unionOf
          [ "rack" "slot" ]
          [
            {
              file = "list.nix";
              value = [ "a" ];
            }
            {
              file = "str.nix";
              value = "b";
            }
          ]
        ) null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `rack\\.slot' has definitions no single `either' member accepts \\(`listOf' rejects str\\.nix; `string' rejects list\\.nix\\)$";
        };
      };
      # LIVE CONTROLS, same run, same skeleton — and a run in which these do not pass says nothing
      # about the cells above, which are equally consistent with a union that refuses everything.
      # Definitions one member takes WHOLE still merge through it, on both members: two lists merge
      # into one list through the member that accepts lists, and a lone string merges through the
      # member that accepts strings. The list value is pinned exactly, because the obligation on
      # this rule is that a definition set which merged before merges to the same bytes.
      test-homogeneous-list-definitions-still-merge-control = {
        expr =
          unionOf
            [ "x" ]
            [
              {
                file = "one.nix";
                value = [ "a" ];
              }
              {
                file = "two.nix";
                value = [ "b" ];
              }
            ];
        expected = {
          x = [
            "b"
            "a"
          ];
        };
      };
      test-string-definition-merges-through-the-other-member-control = {
        expr =
          unionOf
            [ "x" ]
            [
              {
                file = "str.nix";
                value = "b";
              }
            ];
        expected = {
          x = "b";
        };
      };
      # gen-types' `union` over a gen-merge STRUCTURAL member. A `submodule` carries `admits` and no
      # `verify`, so the union read the member's `verify` bare and aborted uncatchably with
      # `attribute 'verify' missing`, on the fold and on a nixpkgs mount alike. gen-types (cyiuz)
      # now refuses a member that is not a checker by name; this namespace needs no change of its
      # own, only the relock onto it. The two sites are two cells because a cell carries one
      # `expectedError`; the checker-only union beside them is their control.
      test-gentypes-union-over-a-strategy-refuses-by-name = {
        expr = builtins.deepSeq (cfg {
          modules = [
            {
              options.seam = gm.mkOption {
                type = t.union [
                  (t.submodule { options.key = gm.mkOption { type = t.str; }; })
                  t.str
                ];
              };
            }
            { config.seam.key = "sateen"; }
          ];
        }) null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-types: union: member 'submodule' is not a checker";
        };
      };
      test-gentypes-union-over-a-strategy-refuses-by-name-mounted = {
        expr =
          builtins.deepSeq
            (nixpkgsLib.evalModules {
              modules = [
                {
                  options.seam = nixpkgsLib.mkOption {
                    type = t.union [
                      (t.submodule { options.key = gm.mkOption { type = t.str; }; })
                      t.str
                    ];
                  };
                }
                { config.seam.key = "sateen"; }
              ];
            }).config
            null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-types: union: member 'submodule' is not a checker";
        };
      };
      test-gentypes-union-over-checkers-answers-control = {
        expr =
          (cfg {
            modules = [
              {
                options.seam = gm.mkOption {
                  type = t.union [
                    t.int
                    t.str
                  ];
                };
              }
              { config.seam = "hello"; }
            ];
          }).seam;
        expected = "hello";
      };
    };

    # The sub-protocol refusal fires at CONSTRUCTION, so there is no bad intermediate to inspect and
    # nothing to assert about a value — only the message. These cells are why the second output
    # exists.
    #
    # ★ EVERY PATTERN HERE IS ANCHORED `^…$`. nix-unit SEARCHES `expectedError.msg` rather than
    # matching it whole, so an unanchored pattern pins a SUBSTRING: it would keep passing if the
    # message grew a wrong clause on either side, which is most of what a message assertion is for.
    # Neither message below contains an ERE metacharacter, so nothing needs escaping and the anchors
    # carry the whole of the exactness.
    flake.testsError.structural-sub-protocol = {
      # The refusal names the TYPE and the field it did not supply — the two things the author has
      # to know. A refusal saying only "incomplete type" would leave both to be re-derived.
      test-element-carrier-missing-one-field-refused-by-name = {
        expr = rackOf { };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `rackOf' carries an element type but does not supply `substSubModules'; a structural type may not inherit a leaf's protocol answer$";
        };
      };
      # A MODULE-SET carrier is in the domain by the other arm, and the message names EVERY missing
      # field in protocol order rather than stopping at the first.
      test-module-set-carrier-names-every-missing-field = {
        expr = gm.mkOptionType {
          name = "slotOf";
          getSubModules = [ skeleton ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `slotOf' carries a module set but does not supply `getSubOptions', `substSubModules'; a structural type may not inherit a leaf's protocol answer$";
        };
      };
      # `deferredModule` HAS a module set and it is empty, so it answers the sub-protocol itself —
      # including the rebuild. Over a NON-EMPTY set there is nothing it could build: the type carries
      # no static-module parameter, so the modules could only be dropped, and a rebuild that silently
      # discards what it was handed is the wrong value with no diagnostic. It refuses, naming the type
      # and what it cannot do with the set.
      test-deferredModule-rebuild-over-non-empty-set-refused-by-name = {
        expr = t.deferredModule.substSubModules [ skeleton ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `deferredModule' cannot be rebuilt over a module set of 1; it carries no static modules and dropping them would lose the declarations silently$";
        };
      };
      # LIVE CONTROL, same run, same type: over its OWN empty set the rebuild returns the type. This
      # is the argument nixpkgs `fixupOptionType` actually passes on a mount, so without this row the
      # refusal above is equally consistent with a `substSubModules` that refuses everything — which
      # would break every mounted `deferredModule` option rather than only the impossible rebuild.
      test-deferredModule-rebuild-over-empty-set-returns-the-type-control = {
        expr =
          let
            ty = t.deferredModule.substSubModules [ ];
          in
          {
            inherit (ty) name;
            subModules = ty.getSubModules;
          };
        expected = {
          name = "deferredModule";
          subModules = [ ];
        };
      };
      # LIVE CONTROL, same run, same skeleton: supply the third field and the SAME hand-built type
      # constructs and answers. Without it both cells above are consistent with a surface that
      # refuses every hand-built type carrying an element.
      test-element-carrier-supplying-all-three-constructs-control = {
        expr =
          let
            ty = rackOf {
              substSubModules = _m: null;
              recarry =
                c:
                rackOf {
                  substSubModules = _m: null;
                  elemType = c.element;
                };
            };
          in
          {
            inherit (ty) name;
            subOptions = ty.getSubOptions [ ];
            subModules = ty.getSubModules;
          };
        expected = {
          name = "rackOf";
          subOptions = { };
          subModules = null;
        };
      };
    };

    # ── the boundary's own refusals ───────────────────────────────────────────────────────────────
    # The rule above has TWO arms, and until now only one of them was armed. A descriptor written in
    # the foreign protocol's words is refused at the IMPORT environment and the message names the
    # foreign fields, because that is the vocabulary its author wrote in. A record built in gen's own
    # words is refused at gen's own constructor and the message names the gen formals. Both are the
    # same rule; a suite that exercised only one of them would leave the other free to rot.
    flake.testsError.interface = {
      test-gen-record-carrying-a-parameter-without-a-substructure-is-refused = {
        expr = genMergeVocab.mkType {
          name = "crate";
          carries.element = t.str;
          recarry = c: c.element;
          substructure = {
            declares = _prefix: { };
            modules = null;
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `crate' carries a parameter but does not supply `rebuild'; a type that carries something answers for it rather than inheriting a leaf's answers$";
        };
      };
      # THE FOURTH CARRIED-ROLE FORMAL, and the last one that was left un-total. The boundary reads
      # `recarry` to rebuild a carrying type over another payload wherever it DERIVES the relation —
      # except where the record stated its own, which is answered by that instead — so a record
      # without it used to construct, export, and then detonate with a bare missing-attribute error the moment
      # a foreign engine applied the functor — an interpreter abort naming neither the type nor the
      # field. Every shipped carrying type supplies it, which is exactly why nothing caught this: the
      # failure was reachable only by a future author, and by then the refusal would not exist.
      test-gen-record-declaring-a-role-without-a-rebuild-is-refused = {
        expr = genMergeVocab.mkType {
          name = "crate";
          carries.element = t.str;
          substructure = {
            declares = _prefix: { };
            modules = null;
            rebuild = _m: null;
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `crate' carries a parameter but does not supply `recarry'; a type that carries something answers for it rather than inheriting a leaf's answers$";
        };
      };
      # LIVE CONTROL, same run, same record: supply all four formals and it constructs. Without it the
      # two cells above are equally consistent with a constructor that refuses every record carrying a
      # role, which would fail them for a reason that has nothing to do with the missing formal.
      test-control-gen-record-supplying-all-four-formals-constructs = {
        expr =
          (genMergeVocab.mkType {
            name = "crate";
            carries.element = t.str;
            recarry = c: c.element;
            substructure = {
              declares = _prefix: { };
              modules = null;
              rebuild = _m: null;
            };
          }).name;
        expected = "crate";
      };
      # AND `deferredModule` IS THE SCOPE CONTROL: it carries a module set through its substructure
      # WITHOUT declaring a role, so it has no payload to rebuild over and owes no `recarry` — it ships
      # without one and constructs. A `recarry` requirement scoped to carrying-in-general rather than
      # to the ROLE would have broken it, and this row is what says so.
      test-control-deferredModule-carries-a-module-set-and-owes-no-recarry = {
        expr = {
          declaresNoRole = !(t.deferredModule ? carries);
          hasNoRecarry = !(t.deferredModule ? recarry);
          constructedAnyway = t.deferredModule.name;
        };
        expected = {
          declaresNoRole = true;
          hasNoRecarry = true;
          constructedAnyway = "deferredModule";
        };
      };

      # A RELATION IS REQUIRED TO CROSS, and the refusal says why rather than producing a type whose
      # foreign type-merge pair was invented at the boundary. A default chosen here would be a merge
      # rule nobody in the vocabulary picked, answering for types whose author never said whether they
      # merge — which is the silent-decision shape this library refuses everywhere else.
      test-exporting-a-record-with-no-relation-is-refused = {
        expr = interface.exportType { name = "unrelated"; };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the type `unrelated' cannot be exported: it declares no type-merge relation, so the foreign protocol's `typeMerge'/`functor' pair has no gen datum to be derived from\\. Build it through the vocabulary's own constructor, which states the relation$";
        };
      };
      # LIVE CONTROL: the same record through the vocabulary's constructor, which states the relation,
      # exports and answers. The refusal is about the missing relation, not about hand-built records.
      test-control-the-same-record-through-the-constructor-exports = {
        expr = (interface.exportType (genMergeVocab.mkType { name = "unrelated"; })).name;
        expected = "unrelated";
      };

      # THE IMPORT ENVIRONMENT IS PARTIAL AND ITS REFUSAL IS NAMED. A value that is not a record, and
      # a record that answers neither vocabulary, are both things the boundary cannot translate — and
      # saying so is what keeps `mkOptionType` from silently constructing a type out of an attrset
      # that was never one.
      test-importing-a-non-record-is-refused = {
        expr = gm.mkOptionType [ "not a type" ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: cannot import an option type from a list; the boundary translates records, not values$";
        };
      };
      test-importing-a-record-that-answers-neither-vocabulary-is-refused = {
        expr = gm.mkOptionType { colour = "red"; };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: cannot import `colour' as an option type; it answers neither this library's vocabulary nor any field of the foreign protocol$";
        };
      };
      # LIVE CONTROL: a record answering ONE field of the foreign protocol is imported, so the refusal
      # above is about answering nothing rather than about being small.
      test-control-a-record-answering-one-protocol-field-imports = {
        expr =
          (gm.mkOptionType {
            name = "tiny";
            check = builtins.isString;
          }).name;
        expected = "tiny";
      };

      # ── A STATED RELATION, AND THE TWO WAYS IT CAN FAIL TO CROSS ─────────────────────────────────
      # ★★★ THE RELATION IS NO LONGER LOST, WHICH IS WHY THESE CELLS NO LONGER SAY IT IS. `functor` is
      # an export field, so it comes off with the rest of the protocol's names — and `importType` now
      # RETAINS the author's own pair under a gen name, installs their relation, and republishes their
      # functor with its name intact. A consumer stating its parameter the nixpkgs way, BARE, is
      # therefore ADMITTED: the parameter is still in a spelling this boundary does not read, and that
      # has not changed — what changed is the CONSEQUENCE, because the relation that discriminates on
      # it is the author's own and is applied unread rather than discarded. The last cell in this
      # group is what says so, and it is the same synthetic container that used to be refused here.
      # ADR-0025 §1's rule — a value or a NAMED refusal, never a silent downgrade — is met by
      # construction on this arm instead of by refusal.
      #
      # WHAT SURVIVES AS A REFUSAL is the pair of shapes where a retained relation could not answer,
      # and the two PARTITION "supplies a functor" on `binOp`, so neither can fire for one record:
      #   · `binOp` stated and left EMPTY beside a parameter this boundary cannot read — something to
      #     discriminate on, nothing stated to discriminate with, and the type would fall back to
      #     merging on its NAME ALONE;
      #   · `binOp` stated with a functor that cannot ANSWER for it — no `name`, or no `type` to
      #     rebuild the merged parameter with. The protocol's own default reads both off the functor
      #     directly, so a gap there is an interpreter abort at a merge site far from the record that
      #     caused it — which is the refusal-shaped hole this group exists to keep closed.
      # The three controls below say the domain is exactly those two and not "supplies a functor".
      test-importing-a-functor-whose-relation-slot-is-empty-is-refused = {
        expr = gm.mkOptionType {
          name = "emptyRel";
          functor = {
            name = "emptyRel";
            # BARE, the nixpkgs convention this boundary does not read — so there IS a parameter,
            # and the `binOp` beside it that would have discriminated on it is empty.
            payload = t.str;
            binOp = null;
            type = _p: null;
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option type `emptyRel' states a parameter in its `functor' but leaves `functor\\.binOp' empty, so nothing it states can discriminate on that parameter and `emptyRel' would merge on its NAME ALONE — accepting two operands the parameter tells apart\\. State the relation in `functor\\.binOp', or drop the `functor' if merging on the name alone is what this type means$";
        };
      };
      # ★★ LIVE CONTROL, AND IT IS THE ONE THAT KEEPS THE REFUSAL PRECISE RATHER THAN MERELY LOUD. A
      # functor carrying a `binOp` but stating NO parameter — no payload, no `wrapped` — is what a
      # metadata decoration supplies, and gen-schema's `refined` (its `lib/refined.nix`) is exactly
      # this shape and is CORRECT as it stands: with nothing to discriminate on, the foreign
      # `defaultTypeMerge` IS name equality and so is the nullary relation, so no information is lost
      # and there is nothing to refuse. Every nullary foreign leaf arrives this way too. A predicate
      # keyed on "supplies a functor" instead of "states a parameter it then loses" would refuse all
      # of them, which is why this row is not optional.
      test-control-a-functor-with-no-parameter-to-discriminate-on-imports = {
        expr =
          (gm.mkOptionType {
            name = "plain";
            check = builtins.isString;
            functor = {
              name = "plain";
              payload = null;
              wrapped = null;
              binOp = _a: _b: null;
              type = null;
            };
          }).name;
        expected = "plain";
      };
      # ★ AND THE SECOND CONTROL SEPARATES THE TWO REFUSALS. A payload is what a type offers to MERGE
      # on and never what it carries, so the carried-role requirement is reached by a record stating
      # its element in the CARRYING spelling and no relation to answer for it — a different refusal
      # with a different message. Asserting that message here is what proves the two refusals are not
      # one loud predicate wearing two names.
      test-control-a-stated-element-with-no-relation-reaches-the-owed-relation-refusal = {
        expr = gm.mkOptionType {
          name = "boxOf";
          nestedTypes.elemType = t.str;
          getSubOptions = _p: { };
          getSubModules = null;
          substSubModules = _m: null;
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `boxOf' carries an element type but states no merge relation for it; state one in `functor\\.binOp' \\(with `functor\\.name' and `functor\\.type'\\), since a type that carries something answers for how two of it merge$";
        };
      };
      # An unroled `nestedTypes` key the role's own spelling would publish: the element stated at
      # the top level, `nestedTypes.elemType` holding an option record. One of the two would be lost
      # at export, so the import refuses by name.
      test-an-unroled-key-the-role-would-publish-is-refused-by-name = {
        expr = gm.mkOptionType {
          name = "boxOf";
          check = _: true;
          elemType = t.int;
          nestedTypes.elemType = {
            _type = "option";
            type = t.str;
          };
          getSubOptions = _p: { };
          getSubModules = null;
          substSubModules = _m: null;
          functor = {
            name = "boxOf";
            payload = null;
            binOp = _a: _b: null;
            type = _p: null;
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option type `boxOf' states its element in its top-level spelling, and its `nestedTypes' holds `elemType' as something that is not that element; a crossing publishes the element under that key, so one of the two would be lost\. Rename the `nestedTypes' key, or state the element there$";
        };
      };
      # ★★★ THE OTHER HALF OF THE PARTITION, AND IT IS A HAZARD THE RETENTION ITSELF CREATED. A
      # retained relation is applied through the protocol's own default, which reads `name' and `type'
      # off the author's functor and APPLIES `type' to the merged parameter. Nothing in the foreign
      # protocol makes an author write either, so a functor stating `binOp' and omitting `type'
      # constructs, exports, and then dies inside the boundary with `attribute 'type' missing' —
      # naming neither the type nor the field, at a merge site the author never wrote. Refusing at
      # import is what makes the retention total: the record that cannot be answered for never enters
      # the library, so the state the abort needs cannot form. The refusal names the FIELD, because
      # the author's remedy is to write it.
      test-importing-a-stated-relation-its-functor-cannot-answer-is-refused = {
        expr = gm.mkOptionType {
          name = "gapBox";
          functor = {
            name = "gapBox";
            payload.elemType = t.str;
            binOp = a: _b: a;
          };
          getSubOptions = _p: { };
          getSubModules = null;
          substSubModules = _m: null;
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option type `gapBox' states a merge relation in `functor\\.binOp' but its `functor' does not answer `type'; the relation is retained verbatim and applied by the protocol's own default, which reads them off it\\. Supply them, or drop `functor\\.binOp' if merging on the name alone is what this type means$";
        };
      };
      # ★★ LIVE CONTROL FOR THAT REFUSAL, AND IT IS THE ROW THAT PROVES THE RELAXATION IT GUARDS. The
      # same record with `type' supplied and STILL no `recarry': it imports, and it merges with a
      # partner its own `binOp` accepts. Without this row the refusal above is equally consistent with
      # a boundary that refuses every carrying record stating a relation — which is the pre-relaxation
      # behaviour, and would silently undo the thing the retention exists to do.
      test-control-a-complete-stated-relation-imports-and-merges-without-recarry = {
        expr =
          let
            box =
              elem:
              gm.mkOptionType {
                name = "okBox";
                functor = {
                  name = "okBox";
                  payload.elemType = elem;
                  binOp = a: _b: a;
                  type = pl: box pl.elemType;
                };
                getSubOptions = _p: { };
                getSubModules = null;
                substSubModules = _m: null;
              };
          in
          ((box t.str).typeMerge (box t.str).functor).name;
        expected = "okBox";
      };
      # ★★ AND THE ADMITTED SUBJECT ANSWERS FOR ITSELF. `foreignRelationRootWith` — the synthetic
      # foreign-relation container, above — is the shape this group used to refuse.
      # It now crosses, and these two rows are what says the admission is not a silent downgrade: its
      # own `binOp` refuses two containers over DIFFERENT elements and reconciles two over the same
      # one. That is the property the old refusal existed to protect, now held by construction. Both
      # rows in one cell because either alone is consistent with a relation that answers constantly.
      test-control-the-admitted-subject-merges-by-its-own-relation = {
        expr = {
          differingParameters = (foreignRelationRootWith t.str).typeMerge (foreignRelationRootWith t.int)
            .functor;
          equalParameters =
            ((foreignRelationRootWith t.str).typeMerge (foreignRelationRootWith t.str).functor).name;
        };
        expected = {
          differingParameters = null;
          equalParameters = "aspectsRoot";
        };
      };
      # ★ THE THIRD CONTROL IS ALREADY ABOVE AND IS NOT REPEATED HERE:
      # `test-control-a-record-answering-one-protocol-field-imports` is a descriptor with NO functor
      # at all, in this same run, and it imports. Together the four say the refusals' domain is
      # exactly "stated a parameter and lost it" and "stated a relation that cannot answer".

      # ── the PUBLISH path, which is a different site from `mkOptionType` ──────────────────────────
      # ★★★ THE REFUSAL HAS TO SURVIVE THE NAMESPACE ASSEMBLY, and it did not. `lib/default.nix`
      # computed the import environment's refusal for every entry of the injected leaf vocabulary and
      # then DISCARDED it, publishing the raw record into `lib.types` — where a mounting consumer dies
      # inside the foreign engine on a missing attribute, uncatchably and naming nothing. Measured at
      # the pre-boundary tree the same roster THREW, so it was a regression rather than a standing gap:
      # a computed refusal thrown away is worse than one never computed.
      #
      # THE PATH IS REACHED ONLY THROUGH A SUPPLIED VOCABULARY. The shipped roster does not trip the
      # rule — measured, empty — so a cell over `genMerge` could not exercise this at any strength;
      # `genMergeWith` hands the assembly a roster it did not choose, which is the input class
      # `lib/default.nix` names as supported ("in compat mode a foreign one") and the one the import
      # environment exists to be total over. The two cells here are DIFFERENT from the `mkOptionType`
      # cells above: same rule, same message, a site that had its own way of losing it.
      test-publishing-a-protocol-incomplete-leaf-is-refused-by-name = {
        expr =
          (genMergeWith (
            genTypes
            // {
              rogueOf = {
                name = "rogueOf";
                elemType = genTypes.str;
              };
            }
          )).types.rogueOf;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `rogueOf' carries an element type but does not supply `getSubOptions', `getSubModules', `substSubModules'; a structural type may not inherit a leaf's protocol answer$";
        };
      };
      # LIVE CONTROL, same roster shape, same run: the un-offending twin answers all three and
      # publishes PROTOCOL-COMPLETE, and an ordinary shipped leaf beside it still does too. Without
      # both halves the cell above is equally consistent with a namespace that refuses everything, or
      # with one poisoned wholesale by a single bad entry — and per-name laziness is exactly what makes
      # the refusal usable rather than fatal to the whole vocabulary.
      test-control-the-un-offending-twin-publishes-protocol-complete = {
        expr =
          let
            published =
              (genMergeWith (
                genTypes
                // {
                  politeOf = {
                    name = "politeOf";
                    elemType = genTypes.str;
                    getSubOptions = _p: { };
                    getSubModules = null;
                    substSubModules = _m: null;
                    functor = {
                      name = "politeOf";
                      payload = null;
                      type = null;
                      binOp = a: _b: a;
                    };
                  };
                }
              )).types;
            protocolFields = [
              "_type"
              "name"
              "description"
              "descriptionClass"
              "deprecationMessage"
              "check"
              "merge"
              "emptyValue"
              "getSubOptions"
              "getSubModules"
              "substSubModules"
              "typeMerge"
              "nestedTypes"
              "functor"
            ];
            missing = ty: builtins.filter (f: !(ty ? ${f})) protocolFields;
          in
          {
            twinMissing = missing published.politeOf;
            shippedLeafMissing = missing published.str;
          };
        expected = {
          twinMissing = [ ];
          shippedLeafMissing = [ ];
        };
      };
    };

    # The tree-as-a-type is a NESTING SEAM, not an `optionType`, and it now says so instead of
    # letting a foreign module system walk into a missing attribute. Before the mark, a real
    # `lib.evalModules` mounting it died INSIDE nixpkgs on `attribute 'deprecationMessage' missing`
    # — an interpreter error, and one `builtins.tryEval` could not catch, so there was nothing for
    # any in-language cell to observe. These cells are the whole of what replaces it. The
    # disposition (why completing the protocol is the wrong repair) is argued at the seam in
    # lib/modules.nix; what is assertable is that the read now returns a NAMED refusal.
    #
    # ★ THE PATTERNS DIFFER IN ONE PLACE ON PURPOSE. The direct read below names the field it
    # reached for and is pinned exactly. The MOUNT cannot be: which protocol field a foreign engine
    # forces first is that engine's evaluation order, not this library's behaviour, so pinning it
    # here would pin nixpkgs' internals and go red on a bump that changed nothing about the refusal.
    # That one field name is the only part left open; every other byte of the message is anchored.
    #
    # ── THE TREE AS A UNION MEMBER: gen's eval holds it, a foreign eval folds it at nixpkgs' value ─
    # The tree answers `admits` and `check` (one module-value domain), so a gen union in this
    # engine's own eval holds it as nesting (`ci/tests/nixpkgs-protocol.nix` pins the parity). What a
    # FOREIGN eval folds is each type's foreign face (`lib/interface.nix` `foreignFace`), whose check
    # reaches the tree's: the cells below pin the 180-cell family one cell per mount, a SERVED cell
    # against nixpkgs' fold of the same construction and a REFUSED one by its message. The refusals
    # left are the docs reads (`getSubModules`) and the rider, pending den-hoag-foreign-mount-parity-knhyg.
    flake.testsError.tree-type =
      let
        family = import ./tests/_fixtures/tree-union-family.nix {
          genMerge = gm;
          inherit nixpkgsLib;
        };
        T = family.T;
        table = builtins.fromJSON (builtins.readFile ./tests/_fixtures/tree-union-mount-table.json);
        treeRefusal =
          field:
          "^gen-merge: `moduleTree' is not an option type and does not answer `${field}'; it is this engine's own nesting seam, and mounting it in a foreign module system is a crossing this library does not open \\(the boundary is the evaluation, and what crosses it is plain data\\)$";
        riderRefusal =
          loc: file: "^gen-merge: option `${loc}' has definitions `moduleTree' cannot consume \\(${file}\\)$";
        doorRefusal =
          rebuiltAs:
          "^gen-merge: the type `wrap' cannot be folded by a foreign eval: its `recarry' rebuilds it as `${rebuiltAs}', so the fold published for it would be another type's$";
        # A caller composite over `el`, its `recarry` rebuilding through `rec_`: `good` rebuilds
        # itself, `bad` rebuilds a `listOf` — the one law the foreign face relies on, kept and broken.
        mkWrap =
          rec_: el:
          t.defineType {
            name = "wrap";
            carries.element = el;
            recarry = c: rec_ c.element;
            admits = _: true;
            mergeDefs = loc: defs: gm.mergeDefs loc el defs;
            substructure = {
              declares = _: { };
              modules = null;
              rebuild = _: null;
            };
          };
        good = el: mkWrap good el;
        bad = mkWrap (el: t.listOf el);
        subOf =
          type:
          t.submodule {
            options.s = gm.mkOption { inherit type; };
          };
        # A construction whose MODULE definition is SERVED folds the tree abroad. Where its string
        # definition is still REFUSED (the twelve `either`/`oneOf` over a container holding the tree
        # directly), it reaches the tree's own fold, which refuses it by the domain guard before the
        # nested eval.
        foldsAbroad = c: table.${c}.module == "SERVED";
        mountCell =
          c:
          let
            inner = builtins.elemAt (builtins.split "\\." c.construction) 2;
            recorded = table.${c.construction}.${c.definition};
          in
          {
            name = "test-mount-${builtins.replaceStrings [ "." ] [ "-" ] c.construction}-${c.definition}";
            value = {
              expr = family.foreign c.gen c.value;
            }
            // (
              if recorded == "SERVED" then
                { expected = family.foreign c.reference c.value; }
              else
                {
                  expectedError = {
                    type = "ThrownError";
                    msg =
                      if c.definition == "string" && foldsAbroad c.construction then
                        riderRefusal (if inner == "listOf" then "s\\.0" else "s\\.k") "<unknown-file>"
                      else
                        treeRefusal "[a-zA-Z]+";
                  };
                }
            );
          };
      in
      builtins.listToAttrs (map mountCell family.cells)
      // {
        # THE BOUNDARY CELL: a real nixpkgs `lib.evalModules` mounting a tree-type is refused BY NAME,
        # by gen-merge, before the consumer can trip over what the tree does not implement.
        test-foreign-mount-refused-by-name = {
          expr =
            let
              tree = gm.evalModuleTree {
                modules = [
                  {
                    options.a = gm.mkOption {
                      type = t.str;
                      default = "x";
                    };
                  }
                ];
              };
            in
            builtins.deepSeq
              (nixpkgsLib.evalModules {
                modules = [
                  {
                    options.x = nixpkgsLib.mkOption { type = tree.type; };
                    config.x = { };
                  }
                ];
              }).config.x
              null;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `moduleTree' is not an option type and does not answer `[a-zA-Z]+'; it is this engine's own nesting seam, and mounting it in a foreign module system is a crossing this library does not open \\(the boundary is the evaluation, and what crosses it is plain data\\)$";
          };
        };
        # The refusal NAMES THE FIELD the caller reached for. An author told only "this is not a type"
        # still has to work out which read they made; the per-field message tells them, and it is what
        # makes the refusal usable from any consumer rather than only from a mount.
        test-protocol-read-names-the-field = {
          expr =
            (gm.evalModuleTree {
              modules = [ { options.a = gm.mkOption { type = t.str; }; } ];
            }).type.getSubOptions
              [ ];
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `moduleTree' is not an option type and does not answer `getSubOptions'; it is this engine's own nesting seam, and mounting it in a foreign module system is a crossing this library does not open \\(the boundary is the evaluation, and what crosses it is plain data\\)$";
          };
        };
        # LIVE CONTROLS, same run, and BOTH are needed — the cells above are equally consistent with a
        # change that broke ALL mounting, and with one that broke the tree's own nesting.
        #
        # (1) A protocol-COMPLETED gen-merge type still mounts in a real `lib.evalModules` and its
        # value comes back, so the refusal above is the tree-type's and not the boundary's.
        test-completed-leaf-still-mounts-control = {
          expr =
            (nixpkgsLib.evalModules {
              modules = [
                {
                  options.x = nixpkgsLib.mkOption { type = t.str; };
                  config.x = "ok";
                }
              ];
            }).config.x;
          expected = "ok";
        };
        # (2) The seam itself still merges: a parent tree nests a child through the child's `.type`.
        # Nothing was deleted to make the mark, and this is the row that says so.
        test-tree-still-nests-in-gen-merge-control = {
          expr =
            let
              child = gm.evalModuleTree {
                modules = [
                  {
                    options.a = gm.mkOption {
                      type = t.str;
                      default = "x";
                    };
                  }
                ];
              };
            in
            cfg {
              modules = [
                { options.inner = gm.mkOption { type = child.type; }; }
                {
                  config.inner = {
                    a = "set";
                  };
                }
              ];
            };
          expected = {
            inner = {
              a = "set";
            };
          };
        };

        # The family is the class, and the class is enumerated by EVALUATION: every name in `types`
        # applied to a type at arity 0, 1 and 2 and to a list of types, kept when the result carries a
        # member other than a module set. A new member-taking combinator reds this cell until the
        # family covers it. `submodule` carries `moduleSet` and is the membership boundary itself.
        #
        # The five names skipped abort UNCATCHABLY on an arity misfit (`builtins.tryEval` cannot hold
        # a type error), and none takes a member: measured one process per name and arity, none
        # carries at any arity. A new name that aborts the same way reds this cell by its abort.
        test-the-family-covers-the-member-taking-census = {
          expr =
            let
              ap = f: x: if builtins.isFunction f then f x else null;
              carrying = v: builtins.isAttrs v && v ? carries && !(v.carries ? moduleSet);
              # The list arity first, so a list-taking combinator is never applied to a single type.
              arities = f: [
                (ap f [
                  t.str
                  t.str
                ])
                f
                (ap f t.str)
                (ap (ap f t.str) t.str)
              ];
              hit =
                v:
                let
                  r = builtins.tryEval (carrying v);
                in
                r.success && r.value;
              unappliable = [
                "defaultOnError"
                "defineType"
                "formatErrors"
                "mkOption"
                "mkType"
              ];
            in
            builtins.filter (n: !(builtins.elem n unappliable) && builtins.any hit (arities t.${n})) (
              builtins.attrNames t
            );
          expected = lib.unique (lib.sort lib.lessThan (map (f: f.of) (builtins.attrValues family.forms)));
        };

        # An undeclared key under a union is refused by name, as at a container element: the union
        # reaches the tree through its called fold, which is the strict one and carries no report.
        test-an-undeclared-key-under-a-union-is-refused-by-name = {
          expr = family.gen (t.either T t.str) {
            a = 1;
            zz = 2;
          };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: option `s\\.zz' is not declared by the nested tree that owns it \\(defined in <gen-merge>\\); the tree at `s' is merged where no undeclared report is carried$";
          };
        };

        # THE RIDER: the tree's fold refuses a definition outside its domain before the nested eval
        # runs, naming the option, where the loader used to refuse it as a module it could not load.
        test-a-bare-tree-refuses-a-string-before-its-nested-eval = {
          expr = family.gen T "hello";
          expectedError = {
            type = "ThrownError";
            msg = riderRefusal "s" "<gen-merge>";
          };
        };
        # …and it guards each arm of the fold, never the record: the fold stays a functor carrying
        # `.reported`, which the rich fold selects on, so the bare tree still reports what it drops.
        test-the-rider-keeps-the-fold-a-reporting-functor = {
          expr = {
            reported = T ? mergeDefs.reported;
            functor = T.mergeDefs ? __functor;
            undeclared =
              map (u: u.path)
                (gm.evalModuleTree {
                  modules = [
                    { options.s = gm.mkOption { type = T; }; }
                    {
                      config.s = {
                        a = 1;
                        zz = 2;
                      };
                    }
                  ];
                }).undeclared;
          };
          expected = {
            reported = true;
            functor = true;
            undeclared = [
              [
                "s"
                "zz"
              ]
            ];
          };
        };

        # THE KEEP-SET: foreign mounts that fold only through gen's own evals stay values. A
        # `submodule`'s fold IS gen's `evalModuleTree`, the eval boundary, so a union inside one is
        # membership however the submodule is mounted; a fence that propagated a foreign mode into
        # nested gen evals would red the submodule rows.
        test-a-union-choosing-its-string-member-first-still-mounts = {
          expr = family.foreign (t.either t.str T) "hello";
          expected = "hello";
        };
        test-a-submodule-over-the-tree-still-mounts = {
          expr = family.foreign (subOf T) { s.a = 5; };
          expected = {
            s.a = 5;
          };
        };
        test-a-container-of-submodules-over-the-tree-still-mounts = {
          expr = family.foreign (t.attrsOf (subOf T)) { k.s.a = 5; };
          expected = {
            k.s.a = 5;
          };
        };
        test-a-submodule-over-a-string-first-union-still-mounts = {
          expr = family.foreign (subOf (t.either t.str T)) { s = "hello"; };
          expected = {
            s = "hello";
          };
        };
        test-a-deferred-module-still-mounts = {
          expr =
            (nixpkgsLib.evalModules {
              modules = [
                {
                  options.a = nixpkgsLib.mkOption { type = nixpkgsLib.types.int; };
                }
                (family.foreign t.deferredModule { a = 5; })
              ];
            }).config.a;
          expected = 5;
        };
        # A submodule-wrapped union over the tree, mounted, yields what gen's own eval yields for it:
        # the union is folded by the submodule's inner eval, which is gen's own.
        test-a-submodule-wrapped-union-mounts-a-module = {
          expr = family.foreign (subOf (t.either T t.str)) { s.a = 5; };
          expected = {
            s.a = 5;
          };
        };
        test-a-submodule-wrapped-union-mounts-a-string = {
          expr = family.foreign (subOf (t.either T t.str)) { s = "hello"; };
          expected = {
            s = "hello";
          };
        };

        # THE DOOR. The foreign face rebuilds a composite through its own `recarry`; a caller whose
        # `recarry` rebuilds ANOTHER type would fold a foreign eval's definitions through that type's
        # fold, and is refused by name. Gen's own eval never reads the foreign face, so the same type
        # folds there.
        test-a-recarry-rebuilding-another-type-is-refused-abroad = {
          expr = family.foreign (bad (t.either T t.str)) { a = 5; };
          expectedError = {
            type = "ThrownError";
            msg = doorRefusal "listOf";
          };
        };
        # In gen's own eval the same composite folds its element by the "^gen-merge: `moduleTree' at option `s': its called `mergeDefs' does not evaluate the nested tree: a nested tree is a child of the one evaluation that holds it [(]`evalModuleTree'[)], read through its fold's threaded sibling, and no second evaluation is made for it$" fold, since it carries
        # no `threaded` sibling, and the tree refuses: OQ2 α (den-hoag-n6dh7), "A container that
        # does not thread it is REFUSED BY NAME — never a silent standalone evaluation". It yielded
        # `{ a = 5; }` before the switch. What carries it forward is a composite that threads the
        # sibling: `mergeDefs = { __functor = …; threaded = ev: …; }`, folding its element through `ev`.
        test-a-recarry-rebuilding-another-type-still-folds-in-gen = {
          expr = force (family.gen (bad (t.either T t.str)) { a = 5; });
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `moduleTree' at option `s': its called `mergeDefs' does not evaluate the nested tree: a nested tree is a child of the one evaluation that holds it [(]`evalModuleTree'[)], read through its fold's threaded sibling, and no second evaluation is made for it$";
          };
        };
        test-a-lawful-caller-composite-meets-the-called-fold-refusal-abroad = {
          expr = family.foreign (good (t.either T t.str)) { a = 5; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `moduleTree' at option `s': its called `mergeDefs' does not evaluate the nested tree: a nested tree is a child of the one evaluation that holds it [(]`evalModuleTree'[)], read through its fold's threaded sibling, and no second evaluation is made for it$";
          };
        };
        # Over leaves alone the face is the type itself, so the door is never reached: the fence
        # rebuilds only what holds the tree or a rebuildable composite.
        test-a-law-breaking-composite-over-a-leaf-still-mounts = {
          expr = family.foreign (bad t.str) "hello";
          expected = "hello";
        };
        # The door NARROWS: a law-breaking composite over a composite with no tree in it mounted
        # before the fence and is refused now (defaulted, reversible).
        test-a-law-breaking-composite-over-a-composite-is-refused-abroad = {
          expr = family.foreign (bad (t.listOf t.str)) [ "x" ];
          expectedError = {
            type = "ThrownError";
            msg = doorRefusal "listOf";
          };
        };
        # The law, over the class: each combinator's `recarry` rebuilds a type of its own name.
        test-every-member-taking-combinator-recarries-to-itself = {
          expr = builtins.filter (
            n:
            let
              k = family.forms.${n}.mk t t.str;
            in
            (k.recarry (
              builtins.mapAttrs (_: c: if builtins.isList c then map (_: t.int) c else t.int) k.carries
            )).name != k.name
          ) (builtins.attrNames family.forms);
          expected = [ ];
        };

        # WHAT THE FENCE DOES NOT REACH, pinned so a change to either is a decision on the record.
        #
        # A foreign container over a gen union holding the tree: the STOCK one (nixpkgs `attrsOf`) is
        # re-homed in gen's eval as gen's own and folds (`ci/tests/nesting-threaded.nix`,
        # `nesting-threaded-fence`; den-hoag-n6dh7 F2 elaboration, OQ11 (d)). An UNRECOGNISED one — a
        # non-default `placeholder` puts nixpkgs' `attrsWith` outside the six — threads through its
        # own `substSubModules` rebuild and gives nixpkgs' value (den-hoag-f8mgj arm (T)).
        test-an-unrecognised-foreign-container-over-a-gen-union-threads-in-gen = {
          expr = family.gen (nixpkgsLib.types.attrsWith {
            elemType = t.either T t.str;
            placeholder = "host";
          }) { k.a = 5; };
          expected = {
            k.a = 5;
          };
        };
        # A caller fold closing over a union LEXICALLY carries no member, so no face of it is
        # rebuilt, and it calls the union's "^gen-merge: `moduleTree' at option `s': its called `mergeDefs' does not evaluate the nested tree: a nested tree is a child of the one evaluation that holds it [(]`evalModuleTree'[)], read through its fold's threaded sibling, and no second evaluation is made for it$" fold, whose tree member refuses by name: the
        # called fold of a nesting type does not evaluate its tree (den-hoag-n6dh7 Unit 2.4, item 1).
        # It yielded `{ a = 5; }` before the switch. What carries the capability forward is the
        # threaded route: a caller fold states `mergeDefs.threaded = ev: …` and folds its union
        # through `ev` (the engine's threaded twin), so its tree is a child of the evaluation.
        test-a-lexical-closure-over-a-union-folds-abroad = {
          expr = force (
            family.foreign (t.defineType {
              name = "w";
              admits = _: true;
              mergeDefs = loc: defs: gm.mergeDefs loc (t.either T t.str) defs;
            }) { a = 5; }
          );
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `moduleTree' at option `s': its called `mergeDefs' does not evaluate the nested tree: a nested tree is a child of the one evaluation that holds it [(]`evalModuleTree'[)], read through its fold's threaded sibling, and no second evaluation is made for it$";
          };
        };
        # Control, same run: the same closure calling the union's PUBLISHED fold serves, at nixpkgs'
        # value.
        test-a-closure-over-a-unions-published-fold-is-served-abroad = {
          expr = family.foreign (t.defineType {
            name = "w";
            admits = _: true;
            mergeDefs = loc: defs: (t.either T t.str).merge loc defs;
          }) { a = 5; };
          expected = {
            a = 5;
          };
        };
      };

    # The shape-directed default-merge law's terminal arm. ci/tests/parity-surface.nix asserts THAT
    # it refuses and that the refusal is catchable; only this output can assert WHAT IT SAYS, and a
    # law whose whole contract is "a value or a NAMED refusal" (ADR-0025 §1) owes the name.
    # The text is `showConflict`'s, the ONE conflict text, naming every definition's file.
    # ★ Both patterns are anchored `^…$` — nix-unit SEARCHES `expectedError.msg`, so an unanchored
    # one pins a substring and would keep passing if the message grew a wrong clause on either side.
    # The one ERE metacharacter the messages carry, the `.` of the option path, is escaped.
    flake.testsError.default-merge-law = {
      # DIFFERING INTS are one of exactly two inputs that reach this arm — differing bools are OR'd
      # and differing strings are concatenated, so "scalars refuse" would be the wrong reading and
      # this cell is half of what fences it.
      test-differing-ints-refuse-by-name = {
        expr =
          gm.mergeDefaultOption
            [ "svc" "port" ]
            [
              {
                file = "<a>";
                value = 1;
              }
              {
                file = "<b>";
                value = 2;
              }
            ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `svc\\.port' has conflicting definitions:\\n- In `<a>': 1\\n- In `<b>': 2$";
        };
      };
      # A TYPE-HETEROGENEOUS definition list is the other one, and it reaches the same refusal by a
      # different route — no shape predicate holds of the list at all.
      test-heterogeneous-defs-refuse-by-name = {
        expr =
          gm.mergeDefaultOption
            [ "svc" "port" ]
            [
              {
                file = "<a>";
                value = 1;
              }
              {
                file = "<b>";
                value = "two";
              }
            ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option `svc\\.port' has conflicting definitions:\\n- In `<a>': 1\\n- In `<b>': \"two\"$";
        };
      };
      # LIVE CONTROL, same run: the same law on the same option path with definitions that DO
      # combine. Without it both cells above are consistent with a law that refuses everything —
      # and the whole point of the ruled arm is that most shapes do not refuse.
      test-control-the-same-law-combines-rather-than-refusing = {
        expr =
          gm.mergeDefaultOption
            [ "svc" "port" ]
            [
              {
                file = "<a>";
                value = [ 1 ];
              }
              {
                file = "<b>";
                value = [ 2 ];
              }
            ];
        expected = [
          1
          2
        ];
      };
    };

    # The REFUSING arms of a check-only `mkOptionType`'s default fold (lib/interface.nix
    # `importDescriptor`; the combining arms are ci/tests/parity-surface.nix's). Each refusal is the
    # ONE conflict text, naming every definition's file (ADR-0025 item 1). Every cell here is green at
    # gen-merge 6a508e3, whose constructor folded agree-or-refuse and so refused all three by the
    # same text: they pin that the text SURVIVES the new default. Each RED was driven by a planted
    # mutant, recorded per cell. Both patterns anchor `^…$` and carry the whole multi-line message.
    flake.testsError.mkoptiontype-default-merge =
      let
        heddle =
          descriptor: a: b:
          (genMerge.evalModuleTree {
            modules = [
              { options.heddle = genMerge.mkOption { type = genMerge.mkOptionType descriptor; }; }
              {
                _file = "/demo/warp.nix";
                heddle = a;
              }
              {
                _file = "/demo/weft.nix";
                heddle = b;
              }
            ];
          }).config.heddle;
        thread = {
          name = "thread";
          check = v: v != null;
        };
      in
      {
        # nixpkgs' own law refuses here too. RED (the default without the rider — `mergeDefaultOption`
        # refusing by its old text): ❌, the message named no file.
        test-differing-ints-refuse-naming-files = {
          expr = heddle thread 1 2;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `heddle' has conflicting definitions:\\n- In `/demo/weft\\.nix': 2\\n- In `/demo/warp\\.nix': 1$";
          };
        };
        # THE CARVE-OUT (parity criterion, owner 2026-09-25): nixpkgs' shallow `//` keeps `{ a = 1; }`
        # (warp's, the first file's) and drops weft's without a word, so this fold keeps a named refusal. RED (the
        # default as nixpkgs' law unmodified): ☢, a value and no error.
        test-differing-values-at-a-shared-attrset-key-refuse-naming-files = {
          expr = heddle thread { a = 1; } { a = 2; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `heddle' has conflicting definitions:\\n- In `/demo/weft\\.nix': <a set>\\n- In `/demo/warp\\.nix': <a set>$";
          };
        };
        # nixpkgs' function arm aborts uncatchably, or silently unwraps a `{ value = …; }` result, so
        # there is no value to take and the refusal stays (as for 0q5u6's `anything`). RED (the
        # default as nixpkgs' law unmodified): ☢, a function and no error.
        test-functions-refuse-naming-files = {
          expr = heddle thread (x: [ x ]) (x: [ (x + 1) ]);
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `heddle' has conflicting definitions:\\n- In `/demo/weft\\.nix': <a lambda>\\n- In `/demo/warp\\.nix': <a lambda>$";
          };
        };
        # A shared key compares each definer's own value slot (`sharedKeyDiffers`), and identity is
        # sound only while DISTINCT closures stay unequal: two closures of one lambda over different
        # environments, and two function literals, refuse on all three evaluators. RED (a fold that
        # calls every shared function equal): ☢, a value and no error, ×3.
        test-distinct-closures-of-one-lambda-refuse-naming-files = {
          expr =
            let
              mkF = _: x: x;
            in
            heddle thread { a = mkF 1; } { a = mkF 2; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `heddle' has conflicting definitions:\\n- In `/demo/weft\\.nix': <a set>\\n- In `/demo/warp\\.nix': <a set>$";
          };
        };
        test-two-function-literals-refuse-naming-files = {
          expr = heddle thread { a = y: y; } { a = y: y; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `heddle' has conflicting definitions:\\n- In `/demo/weft\\.nix': <a set>\\n- In `/demo/warp\\.nix': <a set>$";
          };
        };
        # R-4's FENCE: a descriptor stating `verify` is a gen leaf, whose no-fold default stays
        # `mergeLeaf` — lists that nixpkgs' law would concatenate are still refused. RED (the
        # `verify` guard struck from `importDescriptor`): ☢, a value and no error.
        test-control-a-verify-descriptor-keeps-agree-or-refuse = {
          expr = heddle {
            name = "thread";
            verify = _: null;
          } [ "warp" ] [ "weft" ];
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `heddle' has conflicting definitions:\\n- In `/demo/weft\\.nix': <a list>\\n- In `/demo/warp\\.nix': <a list>$";
          };
        };
      };

    # A DEFINITION-plane value standing in a DECLARATION position used to abort with a raw, pathless,
    # `tryEval`-UNCATCHABLE Nix type error (`expected a set but found a string: "merge"`) — fired
    # frames below the mistake, naming neither the option nor the tag. `isOptLeaf`'s disjunction is
    # binary, so the misplaced value was recursed into as though its own internals were
    # sub-declarations. ADR-0025 item 1: every operation returns a value or a NAMED refusal.
    #
    # ★ THE MISPLACEABLE TAG SET IS CLOSED AT FIVE and enumerable from the library's own source
    # (`grep -rhoP '_type\s*=\s*"\K[a-zA-Z-]+' lib/` ⇒ merge · if · order · override · option-type,
    # plus `option`, the legitimate leaf), so this group quantifies over the whole class rather than
    # over the one tag that was reported.
    #
    # ★★ AND THE FIVE CARRY **TWO** DIAGNOSES, WHICH IS WHAT THE LAST TWO CELLS FENCE. An
    # implementation emitting ONE shared message for all five would satisfy the enumeration while
    # giving `option-type` the wrong remedy — telling an author to move a TYPE under `imports`. The
    # `option-type` cell asserts the `mkOption` wrap SPECIFICALLY, and its regex matches none of the
    # four above it, so a shared-string implementation fails here while passing the combinator cells.
    flake.testsError.decl-plane-misuse = {
      test-merge-combinator-refusal-names-the-option = {
        expr = misdeclare (gm.mkMerge [ { b = declLeaf; } ]);
        expectedError = {
          type = "ThrownError";
          msg = combinatorRefusal "a" "merge";
        };
      };
      test-if-combinator-refusal-names-the-option = {
        expr = misdeclare (gm.mkIf true { b = declLeaf; });
        expectedError = {
          type = "ThrownError";
          msg = combinatorRefusal "a" "if";
        };
      };
      test-order-combinator-refusal-names-the-option = {
        expr = misdeclare (gm.mkOrder 100 { b = declLeaf; });
        expectedError = {
          type = "ThrownError";
          msg = combinatorRefusal "a" "order";
        };
      };
      test-override-combinator-refusal-names-the-option = {
        expr = misdeclare (gm.mkForce { b = declLeaf; });
        expectedError = {
          type = "ThrownError";
          msg = combinatorRefusal "a" "override";
        };
      };
      # THE DISCRIMINATING CELL. Same boundary, same class, DIFFERENT mistake: a bare type where a
      # declaration belongs. The remedy is `mkOption`, never `imports` — and this regex is spelled
      # out rather than derived from `combinatorRefusal` so the two diagnoses cannot silently become
      # one string.
      test-option-type-refusal-names-the-mkoption-remedy = {
        expr = misdeclare t.str;
        expectedError = {
          type = "ThrownError";
          msg =
            "^gen-merge: option `a' is declared as a bare type \\(`string'\\), not a declaration; "
            + "wrap it: `mkOption \\{ type = <that type>; \\}'$";
        };
      };
      # LIVE CONTROL, same run: the same option path, declared correctly, still realizes. Without it
      # the five cells above are consistent with a door that refuses every declaration.
      test-legitimate-mkoption-leaf-control = {
        expr = cfg { modules = [ { options.a = declLeaf; } ]; };
        expected = {
          a = "x";
        };
      };

      # ★★ THE SECOND CALL SITE. Every cell above forces `.config`, which is built from the GUARDED
      # `allOptions`; this one reads `.warmDecision.remerged` and nothing else, which is built from
      # `footOf`'s RAW per-module `options`. A misuse that is DECLARED and never DEFINED is invisible
      # to every other reader — `moduleDefFootprint` is definition-driven and never visits it — so
      # without a guard at that second site this fixture returns `{ }` at exit 0, silently, both at
      # HEAD and with the fold's guard alone. ★ That is the discrimination this cell exists for, and
      # it is why it must be driven red against a FOLD-GUARD-ONLY tree and not merely against HEAD:
      # a cell that already passes with one guard is measuring the other cells' door, not this one.
      test-warm-remerged-declared-only-misuse-refuses-by-name = {
        expr = remergedKeys [
          {
            _file = "edit";
            options.misuse = gm.mkMerge [ { b = declLeaf; } ];
          }
        ];
        expectedError = {
          type = "ThrownError";
          msg = combinatorRefusal "misuse" "merge";
        };
      };
      # LIVE CONTROL for the cell above, same run, SAME READ PATH — `.warmDecision.remerged`, not
      # `.config`. The control the group already has runs through a different reader entirely, so it
      # cannot say whether this one is reachable: without this cell, a guard that made `footOf` throw
      # unconditionally would pass the cell above and look like a working door.
      test-warm-remerged-clean-edit-control = {
        expr = remergedKeys [
          {
            _file = "edit";
            options.other = declLeaf;
            config.other = "o";
          }
        ];
        expected = [ "other" ];
      };
    };

    # ── THE EVALUATOR DOOR AND THE DECLARATION FOLD, by their MESSAGES ────────────────────────
    # `tryEval` discards message text, so the containment readings in `ci/tests/one-evaluator.nix`
    # say THAT these refuse and never WHICH refusal was raised — and "it threw" passes on any
    # combinator carrying one refusal anywhere in it. These cells read the text.
    flake.testsError.one-evaluator = {
      # ★ THE DOOR NAMES THE TERMS IT DID NOT FIND, at the CONSTRUCTION call, instead of letting a
      # non-evaluator through to die as `attribute 'buildRoots' missing` somewhere inside the knot —
      # an interpreter error naming a gen-merge line, uncatchable by the caller and silent about
      # which of its dependencies was wrong. The refusal is a value the door RETURNS and the
      # construction raises, which is what makes the text assertable at all.
      test-a-scope-missing-its-evaluator-terms-refuses-naming-them = {
        expr = builtins.deepSeq (genMergeWithScope { eval = x: x; }).evalModuleTree null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: declares a `scope' with no buildRoots, vertex, empty — the evaluator terms this engine drives the module-tree knot through$";
        };
      };
      # The `null` arm is separate because it is the one a caller reaches by wiring a dependency
      # that did not resolve, and the reason it deserves is about the consolidation rather than
      # about a field list: there is no second driver left to fall back to.
      test-a-null-scope-refuses-saying-there-is-no-second-driver = {
        expr = builtins.deepSeq (genMergeWithScope null).evalModuleTree null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: declares no `scope' — the module tree is evaluated on the one universal graph evaluator, and there is no second driver to fall back to$";
        };
      };
      # ★ THE FOLD NAMES WHAT WAS DEMANDED AND WHERE THE REPAIR IS. A refusal saying only "this
      # module is inadmissible" would leave the author to re-derive which of the two planes they
      # crossed, over a module set the engine has already walked. At `3aa6dac` this shape read
      # `infinite recursion encountered`, which names neither the module, the plane, nor a repair.
      test-a-config-dependent-option-key-set-refuses-at-the-fold = {
        expr = realize {
          modules = [
            (
              { config, ... }:
              {
                options = {
                  flag = gm.mkOption {
                    type = t.bool;
                    default = true;
                  };
                }
                // (if config.flag then { extra = gm.mkOption { type = t.int; }; } else { });
              }
            )
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: a module read `config' while its own declarations were being folded, .*Declare the option unconditionally and gate its `config' instead, or compose the modules before evaluation rather than through `imports = \\[ config\\.… \\]'$";
        };
      };
      # ★ THE GUARD'S DEPTH. The same read, two groups down: the key set at `g.h.k` is reached only
      # by the guard's own recursion into groups, which is a descent of its own rather than
      # `declLeafEntries`'s, so nothing else in the suites pins how far it goes. A walk that stops
      # at the top level is cheaper and green on every other cell, and this module then reads
      # `infinite recursion encountered` — uncatchable and unnamed — instead of the refusal.
      test-a-config-dependent-key-set-three-groups-down-refuses-at-the-fold = {
        expr = realize {
          modules = [
            (
              { config, ... }:
              {
                options.flag = gm.mkOption {
                  type = t.bool;
                  default = true;
                };
                options.g.h.k =
                  if config.flag then
                    {
                      leaf = gm.mkOption {
                        type = t.str;
                        default = "d";
                      };
                    }
                  else
                    { };
              }
            )
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: a module read `config' while its own declarations were being folded, .*Declare the option unconditionally and gate its `config' instead, or compose the modules before evaluation rather than through `imports = \\[ config\\.… \\]'$";
        };
      };
      # LIVE CONTROL, same run: the same reader over a module set that crosses no plane evaluates.
      # Without it the four cells above are consistent with a door and a fold that refuse
      # everything, which is a broken library passing its own oracle.
      test-the-door-and-the-fold-admit-an-ordinary-module-control = {
        expr = cfg {
          modules = [
            {
              options.ordinary = gm.mkOption {
                type = t.str;
                default = "d";
              };
            }
          ];
        };
        expected = {
          ordinary = "d";
        };
      };
    };

    # ── `withArgs`'s reserved keys ────────────────────────────────────────────────────────────
    # The inlet refuses a key a submodule's own evaluation would write over, AT THE MOMENT THE
    # CALLER STATES IT, and names the key. Refusing at the eval sites instead would be too late in
    # two ways: the loss would already have happened, and the caller's name for it would be gone.
    #
    # ★ THERE ARE FOUR, NOT ONE. `name` is injected by `submodule`'s own two `evalModuleTree` calls;
    # `config`, `options` and `prefix` are injected by the ENGINE, at both strata (`lib/modules.nix`
    # `declArgs` and `baseArgs`), with the supplied set on the LEFT of `//`, so the engine's value
    # wins. The engine refuses those three itself (`engine-reserved-args` below), but only when a
    # module is applied; the inlet answers when the caller states the key.
    #
    # Each cell reads the TEXT, not merely that it threw: `tryEval` discards the message, and "it
    # threw" passes on any refusal anywhere in the construction.
    flake.testsError.submodule-args = {
      test-withArgs-refuses-the-reserved-name-by-name = {
        expr = (t.submodule [ { } ]).withArgs { name = "CALLER"; };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `withArgs' cannot supply the base module argument `name'; a submodule's own evaluation injects over whatever a caller supplies there, so the value would be discarded rather than used$";
        };
      };
      test-withArgs-refuses-the-reserved-config-by-name = {
        expr = (t.submodule [ { } ]).withArgs { config = "CALLER"; };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `withArgs' cannot supply the base module argument `config'; a submodule's own evaluation injects over whatever a caller supplies there, so the value would be discarded rather than used$";
        };
      };
      test-withArgs-refuses-the-reserved-options-by-name = {
        expr = (t.submodule [ { } ]).withArgs { options = "CALLER"; };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `withArgs' cannot supply the base module argument `options'; a submodule's own evaluation injects over whatever a caller supplies there, so the value would be discarded rather than used$";
        };
      };
      test-withArgs-refuses-the-reserved-prefix-by-name = {
        expr = (t.submodule [ { } ]).withArgs { prefix = "CALLER"; };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `withArgs' cannot supply the base module argument `prefix'; a submodule's own evaluation injects over whatever a caller supplies there, so the value would be discarded rather than used$";
        };
      };
      # Two at once are named together rather than one-at-a-time, so a caller fixes both in one
      # edit instead of rediscovering the second after the first.
      test-withArgs-names-every-reserved-key-the-caller-stated = {
        expr = (t.submodule [ { } ]).withArgs {
          name = "A";
          prefix = "B";
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `withArgs' cannot supply the base module arguments `name', `prefix'; a submodule's own evaluation injects over whatever a caller supplies there, so the value would be discarded rather than used$";
        };
      };
      # LIVE CONTROL, same run: an UNRESERVED key is admitted and the type still builds. Without it
      # the five cells above are consistent with a `withArgs` that refuses everything — which would
      # pass its own oracle while shipping no inlet at all.
      test-withArgs-admits-an-unreserved-key-control = {
        expr = ((t.submodule [ { } ]).withArgs { anArg = "CALLER"; }).specialArgs;
        expected = {
          anArg = "CALLER";
        };
      };
    };

    # ── the engine's reserved keys ──────────────────────────────────────────────────────────────
    # `evalModuleTree`/`declaredOptions { specialArgs }` put the caller's set on the LEFT of the
    # engine's `config`/`options`/`prefix`, so a caller key among those three would reach no module.
    # It refuses by name instead, at each binding (ADR-0025 item 1). The module takes no formals and
    # reads its key only in an option default, so the declaration guard never forces `declArgs` and
    # the `evalModuleTree` cells answer from `baseArgs`; the `declaredOptions` cells answer from
    # `declArgs`. Each site therefore has cells of its own.
    flake.testsError.engine-reserved-args =
      let
        reads = k: args: {
          options.sel = gm.mkOption {
            type = t.raw;
            default = args.${k};
          };
        };
        engine =
          sa: k:
          (gm.evalModuleTree {
            modules = [ (reads k) ];
            specialArgs = sa;
          }).options.sel.default;
        declared =
          sa: k:
          (gm.declaredOptions {
            modules = [ (reads k) ];
            specialArgs = sa;
          }).sel.default;
        msg =
          keys:
          "^gen-merge: `specialArgs' cannot supply the base module ${keys}; the engine injects its own value there, so the caller's would be discarded rather than used$";
        refused = keys: {
          type = "ThrownError";
          msg = msg keys;
        };
        # One answer per key, per door: REFUSED, the caller's value, or LOST (the engine's won).
        answer =
          e:
          let
            r = builtins.tryEval e;
          in
          if !r.success then
            "REFUSED"
          else if r.value == "CALLER" then
            "CALLER"
          else
            "LOST";
        viaWithArgs = k: answer ((t.submodule [ { } ]).withArgs { ${k} = "CALLER"; }).specialArgs.${k};
        one = k: { ${k} = "CALLER"; };
      in
      {
        test-evalModuleTree-refuses-a-caller-config-by-name = {
          expr = engine { config = "CALLER"; } "config";
          expectedError = refused "argument `config'";
        };
        test-evalModuleTree-refuses-a-caller-options-by-name = {
          expr = engine { options = "CALLER"; } "options";
          expectedError = refused "argument `options'";
        };
        test-evalModuleTree-refuses-a-caller-prefix-by-name = {
          expr = engine { prefix = "CALLER"; } "prefix";
          expectedError = refused "argument `prefix'";
        };
        test-evalModuleTree-names-every-reserved-key-the-caller-stated = {
          expr = engine {
            config = "A";
            prefix = "B";
          } "config";
          expectedError = refused "arguments `config', `prefix'";
        };
        # At HEAD `config`/`options` refused here with ADR-0033's "a module read `config'" text,
        # which blamed the module for a key the caller supplied; `prefix` was lost in silence.
        test-declaredOptions-refuses-a-caller-config-by-name = {
          expr = declared { config = "CALLER"; } "config";
          expectedError = refused "argument `config'";
        };
        test-declaredOptions-refuses-a-caller-options-by-name = {
          expr = declared { options = "CALLER"; } "options";
          expectedError = refused "argument `options'";
        };
        test-declaredOptions-refuses-a-caller-prefix-by-name = {
          expr = declared { prefix = "CALLER"; } "prefix";
          expectedError = refused "argument `prefix'";
        };
        # The two reserved sets are spelled twice (`withArgs`' in `lib/types.nix`, the engine's
        # inline at each binding), so this cell holds them to one answer per key. Only `name`
        # differs, because `submodule` injects `name` and the engine does not. `lib` and `anArg`
        # are the controls: every door admits them. Each answer comes through `tryEval`, so this
        # cell is also the catchability oracle.
        test-withArgs-and-both-engine-strata-agree-per-key = {
          expr = builtins.listToAttrs (
            map
              (k: {
                name = k;
                value = {
                  withArgs = viaWithArgs k;
                  engine = answer (engine (one k) k);
                  declared = answer (declared (one k) k);
                };
              })
              [
                "config"
                "options"
                "prefix"
                "name"
                "lib"
                "anArg"
              ]
          );
          expected =
            let
              all3 = v: {
                withArgs = v;
                engine = v;
                declared = v;
              };
            in
            {
              config = all3 "REFUSED";
              options = all3 "REFUSED";
              prefix = all3 "REFUSED";
              name = {
                withArgs = "REFUSED";
                engine = "CALLER";
                declared = "CALLER";
              };
              lib = all3 "CALLER";
              anArg = all3 "CALLER";
            };
        };
      };

    # ── WHICH REFUSAL FIRED WHEN A FOREIGN SELF-MERGE IS DECLINED ───────────────────────────────
    # The containment itself is a boolean and is asserted on the value plane
    # (`tests/nixpkgs-protocol.nix`). WHICH refusal fired is a claim about the message, which
    # `tryEval` discards — so it belongs here, the same split `union-merge` above makes.
    #
    # At HEAD these cells did not fail, they killed the runner: nixpkgs' `either.typeMerge` unfolds
    # `types.json` forever and dies with an interpreter error rather than a `throw`. The message
    # below only exists because the boundary declines to make the call at all.
    flake.testsError.foreign-selfmerge = {
      # The pair the message names is `nullOr'/`nullOr' because that is `types.json`'s own `.name` —
      # the pre-existing spelling the throw site interpolates, not something the guard introduces.
      # Without the reason clause the message would read as an ordinary name mismatch between two
      # identically-named types, which is a different defect with a different fix.
      test-undecidable-foreign-selfmerge-refused-by-name = {
        expr = declaredTwice nixpkgsLib.types.json nixpkgsLib.types.json;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`nullOr' and `nullOr', whose structure does not bottom out within the boundary's type-walk fuel \\(32\\)\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # The CLASS, not the two names. `serializableValueWith` is a public constructor and every
      # container over an undecidable type is undecidable too, so a guard keyed on `json`/`toml` by
      # name would let both through to the same abort. `listOf json` is the nesting; the message is
      # the container's, and the reason still names the ceiling that was reached.
      test-a-container-over-an-undecidable-type-is-refused-too = {
        expr = declaredTwice (nixpkgsLib.types.listOf nixpkgsLib.types.json) (
          nixpkgsLib.types.listOf nixpkgsLib.types.json
        );
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`listOf' and `listOf', whose structure does not bottom out within the boundary's type-walk fuel \\(32\\)\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # LIVE CONTROL, same run, and it is wrapped in `tryEval` ON PURPOSE: an `expectedError` cell
      # whose control is left to throw would throw the very message the cells above pin, and a
      # boundary that refused EVERY foreign pair would score green on all three. Reading the control
      # as a VALUE is what makes that impossible — a decidable foreign pair still reaches nixpkgs'
      # own `typeMerge` and comes back with a real merged type.
      test-a-decidable-foreign-pair-still-merges-control = {
        expr = (builtins.tryEval (declaredTwice nixpkgsLib.types.number nixpkgsLib.types.number));
        expected = {
          success = true;
          value = "either";
        };
      };
    };
    # File threading (ci/tests/file-thread.nix): the refusal TEXT names the file a wrapped
    # declaration came from, at top level and inside a `submodule` def (`lib/types.nix`
    # `defToModule` wraps each def with `setDefaultModuleLocation`). Each wrapped arm has a
    # direct-`_file` control carrying the same message.
    flake.testsError.file-thread =
      let
        F = "/real/F.nix";
        sdml = file: m: {
          _file = file;
          imports = [ m ];
        };
        declA = {
          _file = "/real/A.nix";
          options.a = gm.mkOption { type = t.int; };
        };
        redeclare =
          m:
          (gm.evalModuleTree {
            modules = [
              declA
              m
            ];
          }).options.a.type.name;
        strA = {
          options.a = gm.mkOption { type = t.str; };
        };
        freeformA = {
          _file = "/real/A.nix";
          freeformType = t.int;
        };
        freeform =
          m:
          builtins.deepSeq (cfg {
            modules = [
              freeformA
              m
            ];
          }) null;
        declaredMsg = "^gen-merge: option `a' is declared with types that do not merge \\(`int' and `string'\\); declared in /real/A\\.nix, /real/F\\.nix$";
        freeformMsg = "^gen-merge: the freeform type is defined with types that do not merge \\(`int' and `string'\\); defined in /real/A\\.nix, /real/F\\.nix$";
      in
      {
        test-declared-in-names-wrapped-file = {
          expr = redeclare (sdml F strA);
          expectedError = {
            type = "ThrownError";
            msg = declaredMsg;
          };
        };
        test-declared-in-direct-file-control = {
          expr = redeclare (strA // { _file = F; });
          expectedError = {
            type = "ThrownError";
            msg = declaredMsg;
          };
        };
        test-declared-in-inside-submodule-names-def-file = {
          expr =
            (gm.evalModuleTree {
              modules = [
                {
                  options.s = gm.mkOption {
                    type = t.submodule {
                      _file = "/real/SUB.nix";
                      options.a = gm.mkOption { type = t.int; };
                    };
                  };
                }
                # A FUNCTION def: a submodule reads an attrset def as config, and only a module
                # can declare an option.
                {
                  _file = F;
                  config.s = _: strA;
                }
              ];
            }).config.s.a;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: option `s\\.a' is declared with types that do not merge \\(`int' and `string'\\); declared in /real/SUB\\.nix, /real/F\\.nix$";
          };
        };
        test-freeform-defined-in-names-wrapped-file = {
          expr = freeform (sdml F { freeformType = t.str; });
          expectedError = {
            type = "ThrownError";
            msg = freeformMsg;
          };
        };
        test-freeform-defined-in-direct-file-control = {
          expr = freeform {
            _file = F;
            freeformType = t.str;
          };
          expectedError = {
            type = "ThrownError";
            msg = freeformMsg;
          };
        };
      };

    # A FOREIGN TYPE'S `check` IS APPLIED BEFORE ITS FOLD (`../tests/foreign-leaf-check.nix` holds the
    # class table). The refusal names the option, the type's description and the failing file; the
    # two further cells are the ones whose stock arm was not a catchable refusal at all — a hybrid
    # descriptor's own `mergeDefs` fed a non-list, and a gen `listOf` round-tripped through
    # `mkOptionType`, each of which aborted in a raw builtin.
    flake.testsError.foreign-leaf-check =
      let
        read =
          T: defs:
          builtins.deepSeq
            (gm.evalModuleTree {
              modules = [ { options.p = gm.mkOption { type = T; }; } ] ++ defs;
            }).config.p
            null;
        bad = v: [
          {
            _file = "bad.nix";
            p = v;
          }
        ];
      in
      {
        test-foreign-type-refusal-names-option-type-file = {
          expr = read nixpkgsLib.types.str (bad 1);
          expectedError = {
            type = "ThrownError";
            msg = "option `p'.*not of type `string'.*`bad\\.nix'";
          };
        };
        test-hybrid-descriptor-checks-before-its-own-mergeDefs = {
          expr = read (gm.mkOptionType {
            name = "h";
            check = builtins.isList;
            mergeDefs = _loc: defs: builtins.concatLists (map (d: d.value) defs);
          }) (bad 1);
          expectedError = {
            type = "ThrownError";
            msg = "option `p'.*not of type `h'.*`bad\\.nix'";
          };
        };
        test-v2-headError-refusal-names-its-reason = {
          expr =
            read
              (
                nixpkgsLib.types.attrsOf nixpkgsLib.types.int
                // {
                  merge = {
                    __functor =
                      self: loc: defs:
                      (self.v2 { inherit loc defs; }).value;
                    v2 = _: {
                      headError.message = "boom";
                      value = { };
                      valueMeta = { };
                    };
                  };
                }
              )
              (bad {
                a = 1;
              });
          expectedError = {
            type = "ThrownError";
            msg = "option `p'.*not of type.*TypeError: boom";
          };
        };
        test-v2-answer-without-headError-aborts-as-nixpkgs-does = {
          expr =
            read
              (
                nixpkgsLib.types.attrsOf nixpkgsLib.types.int
                // {
                  merge = {
                    __functor =
                      self: loc: defs:
                      (self.v2 { inherit loc defs; }).value;
                    v2 = _: {
                      value = { };
                      valueMeta = { };
                    };
                  };
                }
              )
              (bad {
                a = 1;
              });
          expectedError = {
            type = "TypeError";
            msg = "called without required argument 'headError'";
          };
        };
        test-submodule-bearing-adhoc-check-override-refused-by-name = {
          expr =
            read
              (
                nixpkgsLib.types.submodule { options.q = nixpkgsLib.mkOption { type = nixpkgsLib.types.int; }; }
                // {
                  check = builtins.isAttrs;
                }
              )
              (bad {
                q = 1;
              });
          expectedError = {
            type = "ThrownError";
            msg = "option `p'.*ad-hoc.*submodule-bearing";
          };
        };
        test-v2-adhoc-check-override-refused-by-name = {
          expr = read (nixpkgsLib.types.attrsOf nixpkgsLib.types.int // { check = builtins.isAttrs; }) (bad {
            a = 1;
          });
          expectedError = {
            type = "ThrownError";
            msg = "option `p'.*ad-hoc";
          };
        };
        test-round-tripped-structural-type-refuses-by-name = {
          expr = read (gm.mkOptionType (t.listOf t.int)) (bad 1);
          expectedError = {
            type = "ThrownError";
            msg = "option `p'.*not of type `.*`bad\\.nix'";
          };
        };
      };

    # THE MODULE READER IS THE REFERENCE'S `unifyModuleSyntax`. A structured module (one carrying
    # `config` or `options`) with any other key outside the module keys is refused BY NAME, naming
    # the key and the file, on each door's first read of a module — every config read, every
    # declaration-only read, and every reader that treats a value as a module: top level,
    # `check = false`, `types.submodule`, `types.deferredModule` and `lint`. `disabledModules` is
    # refused by presence in both module forms, and before the surplus test. The reference's third
    # arm, a module FUNCTION whose result is not an attribute set, is refused at the same reads
    # EXCEPT `lint`: lint never applies a function module (it is function-opaque by design), so no
    # function result reaches it.
    flake.testsError.module-reader = {
      # The third arm, at an `imports` element: `readerSelfFn` returns itself, so the result is a
      # function.
      test-function-result-not-a-module-refused-top-level = {
        expr =
          withControl
            (viaTop (_: {
              a = 5;
            })).a
            5
            (builtins.deepSeq (viaTop (_: readerSelfFn)) null);
        expectedError = {
          type = "ThrownError";
          msg = fnResultMsg "/real/M\\.nix" "lambda";
        };
      };
      # The declaration-only reads refuse it too, where they once answered silently (`[ "a" "foo" ]`).
      test-function-result-not-a-module-refused-on-the-options-read = {
        expr = withControl (readerOptionNames (_: {
          a = 5;
        })) [ "a" "foo" ] (readerOptionNames (_: readerSelfFn));
        expectedError = {
          type = "ThrownError";
          msg = fnResultMsg "<gen-merge>" "lambda";
        };
      };
      test-function-result-not-a-module-refused-by-declared-options = {
        expr = withControl (readerDeclaredNames (_: {
          a = 5;
        })) [ "a" "foo" ] (readerDeclaredNames (_: readerSelfFn));
        expectedError = {
          type = "ThrownError";
          msg = fnResultMsg "<gen-merge>" "lambda";
        };
      };
      # A path module is attributed to its own file. Control: a path module that is an attrset.
      test-function-result-not-a-module-names-its-file = {
        expr = withControl (readerPathA ./tests/_fixtures/def-reading-a5.nix) 5 (
          builtins.deepSeq (readerPathA ./tests/_fixtures/fn-returns-fn.nix) null
        );
        expectedError = {
          type = "ThrownError";
          msg = fnResultMsg "/[^']*/_fixtures/fn-returns-fn\\.nix" "lambda";
        };
      };
      test-surplus-key-refused-top-level = {
        expr = withControl (viaTop readerC0).a 2 (builtins.deepSeq (viaTop readerBad) null);
        expectedError = {
          type = "ThrownError";
          msg = surplusMsg "/real/M\\.nix";
        };
      };
      # Not gated by `check`: a lax eval does not report the key on `.undeclared`, it refuses.
      test-surplus-key-refused-with-check-false = {
        expr = withControl (viaTopLax readerC0) [ ] (viaTopLax (readerBad // { _file = "/real/X.nix"; }));
        expectedError = {
          type = "ThrownError";
          msg = surplusMsg "/real/X\\.nix";
        };
      };
      # A FUNCTION def, because a submodule reads an attrset def as config (`types.submodule`), so
      # the module reader applies to its function and path defs.
      test-surplus-key-refused-in-a-submodule-def = {
        expr = withControl (viaSubmodule (_: readerC0)).a 2 (
          builtins.deepSeq (viaSubmodule (_: readerBad)) null
        );
        expectedError = {
          type = "ThrownError";
          msg = surplusMsg "/real/S\\.nix";
        };
      };
      test-surplus-key-refused-in-a-deferred-module-def = {
        expr = withControl (viaDeferred readerC0).a 2 (builtins.deepSeq (viaDeferred readerBad) null);
        expectedError = {
          type = "ThrownError";
          msg = surplusMsg "/real/D\\.nix, via option d";
        };
      };
      # `lint` reads through the same reader: without it, lint called a module the engine refuses
      # "portable" (`[ ]`).
      test-surplus-key-refused-by-lint = {
        expr = withControl (viaLint readerC0) [ ] (viaLint {
          bogus = gm.mkAfter [ 1 ];
          config.a = 2;
        });
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: module `/real/L\\.nix' has an unsupported attribute `bogus'\\. .*";
        };
      };
      # S5, shorthand: `foo = 1` beside `disabledModules` was read as structured and `foo` dropped.
      test-disabled-modules-refused-on-a-shorthand-module = {
        expr = withControl (viaTop { foo = 1; }).foo 1 (
          builtins.deepSeq (viaTop {
            _file = "/real/DM.nix";
            foo = 1;
            disabledModules = [ ];
          }) null
        );
        expectedError = {
          type = "ThrownError";
          msg = disabledMsg "/real/DM\\.nix";
        };
      };
      # S5b, structured: the key was admitted and ignored on the cold path.
      test-disabled-modules-refused-on-a-structured-module = {
        expr = withControl (viaTop readerC0).a 2 (
          builtins.deepSeq (viaTop {
            _file = "/real/DS.nix";
            config.a = 2;
            disabledModules = [ ];
          }) null
        );
        expectedError = {
          type = "ThrownError";
          msg = disabledMsg "/real/DS\\.nix";
        };
      };
      # ORDER: a module carrying both a surplus key and `disabledModules` gets the `disabledModules`
      # refusal, not the surplus one.
      test-disabled-modules-refused-before-the-surplus-key = {
        expr = withControl (viaTop readerC0).a 2 (
          builtins.deepSeq (viaTop {
            _file = "/real/DO.nix";
            config.a = 2;
            bogus = 1;
            disabledModules = [ ];
          }) null
        );
        expectedError = {
          type = "ThrownError";
          msg = disabledMsg "/real/DO\\.nix";
        };
      };
      # `lint` refuses `disabledModules` at its own first read, the empty list included: without its
      # site, lint called this module portable (`[ ]`).
      test-disabled-modules-refused-by-lint = {
        expr = withControl (viaLint readerC0) [ ] (viaLint {
          config.a = 2;
          disabledModules = [ ];
        });
        expectedError = {
          type = "ThrownError";
          msg = disabledMsg "/real/L\\.nix";
        };
      };

      # THE DECLARATION-ONLY READS. The refusals fire on each door's first read of a module, which is
      # the declaration stratum's, so a read that forces no config refuses as a config read does.
      # Before, the typo's declaration `c` vanished from these answers without a word (`[ "b" ]`),
      # where the reference refuses the module.
      test-declaration-only-read-of-a-typo-key-refused-by-name = {
        expr = withControl (builtins.attrNames (gm.declaredOptions { modules = [ readerRight ]; })) [
          "b"
          "c"
        ] (builtins.attrNames (gm.declaredOptions { modules = [ readerTypo ]; }));
        expectedError = {
          type = "ThrownError";
          msg = surplusKeyMsg "/real/T\\.nix" "option";
        };
      };
      test-declaration-only-options-read-of-a-typo-key-refused-by-name = {
        expr =
          builtins.attrNames
            (gm.evalModuleTree {
              modules = [
                readerDecl
                readerTypo
              ];
            }).options;
        expectedError = {
          type = "ThrownError";
          msg = surplusKeyMsg "/real/T\\.nix" "option";
        };
      };
      test-substructure-declares-of-a-typo-key-refused-by-name = {
        expr = withControl (readerDeclares readerRight) [
          "b"
          "c"
        ] (readerDeclares readerTypo);
        expectedError = {
          type = "ThrownError";
          msg = surplusKeyMsg "/real/T\\.nix" "option";
        };
      };
      # Where the reference REMOVES `x` (`[ "_module" ]`), the declaration read answered `[ "x" ]`:
      # a changed meaning on a module set the reference accepts. It is refused by name instead.
      test-declaration-only-read-of-disabled-modules-refused-by-name = {
        expr =
          withControl (builtins.attrNames (gm.declaredOptions { modules = [ readerKeyed ]; })) [ "x" ]
            (
              builtins.attrNames (
                gm.declaredOptions {
                  modules = [
                    readerKeyed
                    {
                      _file = "/real/DK.nix";
                      disabledModules = [ { key = "B"; } ];
                    }
                  ];
                }
              )
            );
        expectedError = {
          type = "ThrownError";
          msg = disabledMsg "/real/DK\\.nix";
        };
      };
    };

    # EACH NESTING TYPE READS A DEFINITION AS ITS REFERENCE DOES (`defsAsModules`, nixpkgs'
    # `allModules` flag for flag), and a value that is not a module is refused by name. The values
    # these readings produce are `./tests/def-reading.nix`; these are the refusals. The tree type
    # reads every def as a module, so a mixed def meets the module reader; `types.submodule` reads an
    # attrset def as config, so a module key in one is an undeclared option.
    flake.testsError.def-reading =
      let
        tree = (gm.evalModuleTree { modules = [ { options.a = int0; } ]; }).type;
        sub = t.submodule { options.a = int0; };
        int0 = gm.mkOption {
          type = t.int;
          default = 0;
        };
        valueAt =
          type: def:
          (cfg {
            modules = [
              { options.t = gm.mkOption { inherit type; }; }
              {
                _file = "/real/F.nix";
                config.t = def;
              }
            ];
          }).t;
        notModuleMsg = "^gen-merge: a module must be a path, a function or an attribute set, and this one is string \\(an `imports' element, or a nesting type's definition read as a module\\)$";
        undeclaredMsg =
          key: "^gen-merge: option `t\\.${key}' does not exist \\(no freeformType to absorb it\\)$";
        # An option named `imports', so the def `{ imports = [ "x" ]; }` is a value at `submodule`
        # and a module whose import is not a module at the tree type.
        importsTree =
          (gm.evalModuleTree {
            modules = [ { options.imports = gm.mkOption { type = t.listOf t.str; }; } ];
          }).type;
      in
      {
        # Uncatchable at the tree type before the landing: the def was read as config.
        test-tree-function-def-with-surplus-key-refused = {
          expr = builtins.deepSeq (valueAt tree (
            { ... }:
            {
              bogus = 1;
              config.a = 2;
            }
          )) null;
          expectedError = {
            type = "ThrownError";
            msg = surplusMsg "/real/F\\.nix";
          };
        };
        test-tree-mixed-def-refused-by-the-module-reader = {
          expr = builtins.deepSeq (valueAt tree {
            bogus = 1;
            config.a = 2;
          }) null;
          expectedError = {
            type = "ThrownError";
            msg = surplusMsg "/real/F\\.nix";
          };
        };
        # `lint` refuses a value that is not a module as the engine does, where it answered "no
        # findings" (`[ ]`) for a module set the engine refuses. The path-literal control is collected.
        test-lint-module-that-is-not-a-module-refused = {
          expr = withControl (builtins.length (
            gm.lint {
              modules = [ ./tests/_fixtures/lint-options-arg.nix ];
            }
          )) 1 (builtins.deepSeq (gm.lint { modules = [ "m.nix" ]; }) null);
          expectedError = {
            type = "ThrownError";
            msg = notModuleMsg;
          };
        };
        test-tree-import-that-is-not-a-module-refused = {
          expr = builtins.deepSeq (valueAt importsTree { imports = [ "x" ]; }) null;
          expectedError = {
            type = "ThrownError";
            msg = notModuleMsg;
          };
        };
        test-submodule-config-key-is-an-undeclared-option = {
          expr = builtins.deepSeq (valueAt sub { config.a = 2; }) null;
          expectedError = {
            type = "ThrownError";
            msg = undeclaredMsg "config";
          };
        };
        test-submodule-imports-key-is-an-undeclared-option = {
          expr = builtins.deepSeq (valueAt sub { imports = [ { a = 4; } ]; }) null;
          expectedError = {
            type = "ThrownError";
            msg = undeclaredMsg "imports";
          };
        };
        test-submodule-functor-key-is-an-undeclared-option = {
          expr = builtins.deepSeq (valueAt sub { __functor = _: { ... }: { a = 6; }; }) null;
          expectedError = {
            type = "ThrownError";
            msg = undeclaredMsg "__functor";
          };
        };
        # The top level: nixpkgs aborts on `import "x"`; this refuses by name.
        test-top-level-import-that-is-not-a-module-refused = {
          expr = builtins.deepSeq (cfg {
            modules = [
              { options.imports = gm.mkOption { type = t.listOf t.str; }; }
              { imports = [ "x" ]; }
            ];
          }) null;
          expectedError = {
            type = "ThrownError";
            msg = notModuleMsg;
          };
        };
      };
    flake.testsError.empty-definitions =
      let
        t = genMerge.types;
        sub = t.submodule {
          options.a = genMerge.mkOption { type = t.int; };
        };
      in
      {
        test-submodule-empty-value-refuses-an-undefined-sub-option = {
          expr =
            (genMerge.evalModuleTree {
              modules = [
                { options.o = genMerge.mkOption { type = sub; }; }
                { config.o = genMerge.mkIf false { a = 1; }; }
              ];
            }).config.o.a;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `a' is used but not defined$";
          };
        };
      };
    # den-hoag-zakjg U1 — `bandedLeaves`' refusals, and the values its records never force. The
    # value cells are ./tests/bands.nix.
    flake.testsError.bands =
      let
        decl = {
          options.x = gm.mkOption { type = t.str; };
        };
        undefined = gm.evalModuleTree { modules = [ decl ]; };
        # `x` IS defined by the third module; the second module's own error is raised while `x`'s
        # definitions are collected.
        userError = gm.evalModuleTree {
          modules = [
            decl
            { config = throw "USER-ERROR"; }
            { x = "v"; }
          ];
        };
        planted = gm.evalModuleTree {
          modules = [
            {
              options.x = gm.mkOption {
                type = t.str;
                default = throw "PLANTED";
              };
            }
          ];
        };
      in
      {
        # The provenance record became total; the value did not.
        test-an-undefined-leaf-value-still-refuses = {
          expr = undefined.config.x;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `x' is used but not defined$";
          };
        };
        test-a-user-error-reads-as-itself-in-the-value = {
          expr = userError.config.x;
          expectedError = {
            type = "ThrownError";
            msg = "^USER-ERROR$";
          };
        };
        # ...and in the band: the defined leaf is never recorded as "unset: no definition".
        test-a-user-error-propagates-from-the-band-never-reads-as-unset = {
          expr =
            (gm.bandedLeaves {
              scope = "u";
              result = userError;
            }).x.reason;
          expectedError = {
            type = "ThrownError";
            msg = "^USER-ERROR$";
          };
        };
        # The error above fires where the provenance KEY SET is computed, before any leaf is
        # classified. This one is local to `x`'s own definition: the key set reads, and only the
        # classification of `x` meets it, which is where a `tryEval` would have read "no definition".
        test-a-user-error-in-the-leafs-own-definition-propagates-from-its-band = {
          expr =
            (gm.bandedLeaves {
              scope = "u";
              result = gm.evalModuleTree {
                modules = [
                  decl
                  { x = gm.mkIf (throw "USER-ERROR") "v"; }
                ];
              };
            }).x.reason;
          expectedError = {
            type = "ThrownError";
            msg = "^USER-ERROR$";
          };
        };
        # The control for `test-a-conflicting-leaf-bands-without-forcing-its-value`: the same leaf's
        # value refuses, so a band read that forced it would refuse too.
        test-a-conflicting-leaf-value-refuses-where-its-band-reads = {
          expr =
            (gm.evalModuleTree {
              modules = [
                decl
                { x = "a"; }
                { x = "b"; }
              ];
            }).config.x;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option `x' has conflicting definitions:";
          };
        };
        # The control for `test-every-unset-reason`: the planted default the band never forces.
        test-the-planted-default-fires-when-the-value-is-read = {
          expr = planted.config.x;
          expectedError = {
            type = "ThrownError";
            msg = "^PLANTED$";
          };
        };
        test-a-freeform-priority-is-no-band = {
          expr = gm.priorityBand null;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge[.]priorityBand: the priority is a null, not an override number$";
          };
        };
        test-a-scope-that-is-not-a-string-is-refused = {
          expr = builtins.attrNames (
            gm.bandedLeaves {
              scope = null;
              result = undefined;
            }
          );
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge[.]bandedLeaves: `scope' is a null, not the contributor's scope id$";
          };
        };
        test-a-result-that-is-not-an-evaluation-is-refused = {
          expr = builtins.attrNames (
            gm.bandedLeaves {
              scope = "u";
              result = undefined.config;
            }
          );
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge[.]bandedLeaves: `result' is not an `evalModuleTree' result [(]it needs `options', `provenance' and `config'[)]$";
          };
        };
      };
    # 0s6zi — a tree merged as a container element carries no undeclared report, so it refuses a
    # key its own level does not declare, by name, with the element's location and the def's file.
    flake.testsError.container-element =
      let
        el =
          (gm.evalModuleTree {
            check = false;
            modules = [
              {
                options.known = gm.mkOption {
                  type = t.str;
                  default = "k";
                };
              }
            ];
          }).type;
        cx =
          ty: def:
          (gm.evalModuleTree {
            check = false;
            modules = [
              { options.x = gm.mkOption { type = ty; }; }
              {
                _file = "/real/F.nix";
                config.x = def;
              }
            ];
          }).config.x;
        bad = {
          known = "v";
          bogus = 1;
        };
        msg =
          path: at:
          "^gen-merge: option `${path}' is not declared by the nested tree that owns it \\(defined in /real/F\\.nix\\); the tree at `${at}' is merged where no undeclared report is carried$";
      in
      {
        test-attrsof-element-refuses-deep = {
          expr = builtins.deepSeq (cx (t.attrsOf el) { a = bad; }) null;
          expectedError = {
            type = "ThrownError";
            msg = msg "x\\.a\\.bogus" "x\\.a";
          };
        };
        test-attrsof-element-refuses-at-element-whnf = {
          expr = builtins.seq (cx (t.attrsOf el) { a = bad; }).a null;
          expectedError = {
            type = "ThrownError";
            msg = msg "x\\.a\\.bogus" "x\\.a";
          };
        };
        test-listof-element-refuses = {
          expr = builtins.deepSeq (cx (t.listOf el) [ bad ]) null;
          expectedError = {
            type = "ThrownError";
            msg = msg "x\\.0\\.bogus" "x\\.0";
          };
        };
        # 9f4bn K4, the non-reporting half: an element whose every def is discharged takes the
        # tree's `whenEmpty`, the strict fold over no definitions, and the tree's own undeclared
        # `zz` is refused rather than dropped (nixpkgs at `check = false` drops it: the P1 boundary).
        test-an-empty-element-tree-refuses-its-own-finding = {
          expr =
            let
              zzTree =
                (gm.evalModuleTree {
                  check = false;
                  modules = [
                    {
                      options.b = gm.mkOption {
                        type = t.int;
                        default = 7;
                      };
                    }
                    { config.zz = 1; }
                  ];
                }).type;
            in
            builtins.deepSeq (cx (t.lazyAttrsOf zzTree) { a = gm.mkIf false { b = 9; }; }).a.b null;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: option `zz' is not declared by the nested tree that owns it \\(defined in <gen-merge>\\); the tree is merged where no undeclared report is carried$";
          };
        };
        test-nullor-element-refuses = {
          expr = builtins.deepSeq (cx (t.nullOr el) bad) null;
          expectedError = {
            type = "ThrownError";
            msg = msg "x\\.bogus" "x";
          };
        };
      };

    # tgj54 — at the bare site a finding is refused at its OWNER's level, in the owner's regime:
    # a strict nested tree refuses its own key as an option that does not exist.
    flake.testsError.bare-site =
      let
        t2 =
          (gm.evalModuleTree {
            check = true;
            modules = [
              {
                options.k = gm.mkOption {
                  type = t.str;
                  default = "d";
                };
              }
            ];
          }).type;
        t1 =
          (gm.evalModuleTree {
            check = true;
            modules = [ { options.sub = gm.mkOption { type = t2; }; } ];
          }).type;
      in
      {
        test-a-strict-nested-tree-refuses-its-own-finding-in-its-own-words = {
          expr = realize {
            check = false;
            modules = [
              { options.x = gm.mkOption { type = t1; }; }
              {
                _file = "/real/F.nix";
                config.x.sub = {
                  k = "s";
                  bogus = 1;
                };
              }
            ];
          };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: option `x\\.sub\\.bogus' does not exist \\(no freeformType to absorb it\\)$";
          };
        };
      };

    # AN OPERAND WHOSE NAME IS NOT A STRING, at each refusal site in lib/ that names a merge operand —
    # the six relations in lib/types.nix, the two parametric-leaf refusals in lib/default.nix,
    # `foreignRel` in lib/interface.nix and the two declaration-plane reasons in lib/modules.nix — all
    # of which now name it through `interface.nameOf`. Before that reader existed, every one of these
    # aborted with a coercion error — class `TypeError`, which `tryEval` does not contain — so the
    # declaration plane's own refusal never got to speak. `type = "ThrownError"` is therefore the
    # discriminating half of each cell: against the old tree nix-unit reds it and names the class it
    # actually met, and the message pins which site answered.
    flake.testsError.partner-name-not-a-string =
      let
        badlyNamed = {
          name = 7;
        };
        # A caller's foreign-protocol type that STATES its relation, so the boundary retains it as
        # `foreignRel` rather than supplying the nullary one.
        foreignStating = gm.mkOptionType {
          name = "foreign";
          check = _: true;
          merge = _loc: defs: (builtins.head defs).value;
          functor = {
            name = "foreign";
            type = _: foreignStating;
            payload = null;
            wrapped = null;
            binOp = _: _: null;
          };
        };
        # Raw records with no relation of their own, so the declaration plane's reasons speak: one
        # nested past the boundary's type-walk fuel, one that bottoms out at once.
        nested =
          n:
          if n == 0 then
            { name = "leaf"; }
          else
            {
              name = "deep";
              nestedTypes.elemType = nested (n - 1);
            };
        declaredTwice =
          a: b:
          realize {
            modules = [
              { options.x = gm.mkOption { type = a; }; }
              { options.x = gm.mkOption { type = b; }; }
            ];
          };
        refuses = pair: {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(${pair}\\); declared in <gen-merge>, <gen-merge>$";
        };
      in
      {
        test-nullary-relation-names-the-partner-name-type = {
          expr = declaredTwice t.bool badlyNamed;
          expectedError = refuses "`bool' and `<a name of type int>'";
        };
        test-element-relation-names-the-partner-name-type = {
          expr = declaredTwice (t.attrsOf t.int) badlyNamed;
          expectedError = refuses "`attrsOf' and `<a name of type int>'";
        };
        test-element-relation-names-the-partner-element-name-type = {
          expr = declaredTwice (t.attrsOf t.int) (t.attrsOf badlyNamed);
          expectedError = refuses "`attrsOf' over `int' and `attrsOf' over `<a name of type int>', whose element types do not merge: `int' and `<a name of type int>'";
        };
        test-submodule-relation-names-the-partner-name-type = {
          expr = declaredTwice (t.submodule { }) badlyNamed;
          expectedError = refuses "`submodule' and `<a name of type int>'";
        };
        test-attrs-relation-names-the-partner-name-type = {
          expr = declaredTwice t.attrs badlyNamed;
          expectedError = refuses "`attrs' and `<a name of type int>'";
        };
        test-either-relation-names-the-partner-name-type = {
          expr = declaredTwice (t.either t.int t.str) badlyNamed;
          expectedError = refuses "`either' and `<a name of type int>'";
        };
        test-unminted-parametric-leaf-names-the-partner-name-type = {
          expr = declaredTwice (t.refined t.str (_: true)) badlyNamed;
          expectedError = refuses "`refined<string>' and `<a name of type int>', whose parameters live behind their own predicate and cannot be compared";
        };
        test-minted-parametric-leaf-names-the-partner-name-type = {
          expr = declaredTwice (t.union [ t.str ]) badlyNamed;
          expectedError = refuses "`union<string>' and `<a name of type int>', which mint to different constructions and carry no readable component values to reconcile";
        };
        test-stated-foreign-relation-names-the-partner-name-type = {
          expr = declaredTwice foreignStating badlyNamed;
          expectedError = refuses "`foreign' and `<a name of type int>', which the first type's own `functor' does not reconcile";
        };
        test-undecidable-pair-names-the-operand-name-type = {
          expr = declaredTwice (nested 40) badlyNamed;
          expectedError = refuses "`<a name of type int>' and `deep', whose structure does not bottom out within the boundary's type-walk fuel \\(32\\)";
        };
        test-reasonless-pair-names-the-operand-name-type = {
          expr = declaredTwice { name = "plain"; } badlyNamed;
          expectedError = refuses "`plain' and `<a name of type int>'";
        };
      };

    # A TYPE'S OWN NAME (or a member's) that is not a string, at each refusal site in lib/ that
    # names the type it is about rather than its merge partner. Each of these interpolated the name
    # directly and aborted with a coercion error — class `TypeError`, which `tryEval` does not
    # contain. They now read it through `interface.nameOf`, so `type = "ThrownError"` is the
    # discriminating half of every cell and the message pins which site answered. The last two
    # cells pin the one wording change the reader brings: an UNNAMED record is `<unnamed>' at every
    # site, where these sites used to say `raw' or `?'.
    flake.testsError.own-name-not-a-string =
      let
        bad = 7;
        declaredTwice =
          a: b:
          realize {
            modules = [
              { options.x = gm.mkOption { type = a; }; }
              { options.x = gm.mkOption { type = b; }; }
            ];
          };
        refuses = pair: {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(${pair}\\); declared in <gen-merge>, <gen-merge>$";
        };
        thrown = msg: {
          type = "ThrownError";
          inherit msg;
        };
        leafProtocol = {
          getSubOptions = _: { };
          getSubModules = null;
          substSubModules = _: null;
          recarry = x: x;
        };
        noRelation = {
          name = "f";
          type = null;
          payload = null;
          binOp = _: _: null;
        };
        # Two raw records with no gen relation, whose own `typeMerge' joins to a type named `j' —
        # a join that keeps neither operand's name, so the witness names it.
        renamingJoin = name: {
          inherit name;
          check = _: true;
          merge = _: defs: (builtins.head defs).value;
          typeMerge = _: {
            name = "j";
            check = _: true;
          };
          functor = noRelation;
        };
      in
      {
        test-nullary-relation-names-its-own-name-type = {
          expr = declaredTwice (t.mkType { name = bad; }) t.str;
          expectedError = refuses "`<a name of type int>' and `string'";
        };
        test-either-names-its-member-name-type = {
          expr = realize {
            modules = [
              {
                options.x = gm.mkOption {
                  type = t.either (t.mkType {
                    name = bad;
                    admits = _: false;
                  }) t.int;
                };
              }
              { config.x = "no"; }
            ];
          };
          expectedError = thrown "^gen-merge: option `x' has definitions no single `either' member accepts \\(`<a name of type int>' rejects <gen-merge>; `int' rejects <gen-merge>\\)$";
        };
        test-stated-foreign-relation-names-its-own-name-type = {
          expr = declaredTwice (gm.mkOptionType {
            name = bad;
            check = _: true;
            functor = noRelation;
          }) t.str;
          expectedError = refuses "`<a name of type int>' and `string', which the first type's own `functor' \\(named `f'\\) does not reconcile with the second's \\(named `string'\\)";
        };
        test-bare-type-declaration-names-its-name-type = {
          expr = realize {
            modules = [
              {
                options.x = {
                  _type = "option-type";
                  name = bad;
                };
              }
            ];
          };
          expectedError = thrown "^gen-merge: option `x' is declared as a bare type \\(`<a name of type int>'\\), not a declaration; ";
        };
        test-structural-type-missing-its-sub-protocol-names-its-name-type = {
          expr =
            (t.mkType {
              name = bad;
              carries.element = t.str;
            }).typeMergeRel;
          expectedError = thrown "^gen-merge: the structural type `<a name of type int>' carries a parameter but does not supply ";
        };
        test-checked-fold-names-its-name-type = {
          expr = realize {
            modules = [
              {
                options.x = gm.mkOption {
                  type = gm.mkOptionType {
                    name = bad;
                    check = _: false;
                  };
                };
              }
              { config.x = 1; }
            ];
          };
          expectedError = thrown "^gen-merge: a definition for option `x' is not of type `<a name of type int>', in `<gen-merge>'$";
        };
        test-two-carried-roles-names-its-name-type = {
          expr =
            (gm.mkOptionType (
              leafProtocol
              // {
                name = bad;
                check = _: true;
                carries = {
                  a = t.str;
                  b = t.str;
                };
              }
            )).functor;
          expectedError = thrown "^gen-merge: the type `<a name of type int>' declares 2 carried roles ";
        };
        test-unspelled-carried-role-names-its-name-type = {
          expr =
            (gm.mkOptionType (
              leafProtocol
              // {
                name = bad;
                check = _: true;
                carries.zz = t.str;
              }
            )).functor;
          expectedError = thrown "^gen-merge: the type `<a name of type int>' carries the role `zz', ";
        };
        test-renaming-foreign-join-names-the-operand-name-type = {
          expr = declaredTwice (renamingJoin "b") (renamingJoin bad);
          expectedError = refuses "`<a name of type int>' and `b', which their own relation joins to `j', a type that states neither declaration's own check";
        };
        test-carrier-refusal-names-its-name-type = {
          expr = gm.mkOptionType {
            name = bad;
            nestedTypes.elemType = t.str;
          };
          expectedError = thrown "^gen-merge: the structural type `<a name of type int>' carries an element type but does not supply ";
        };
        test-unreadable-functor-names-its-name-type = {
          expr = gm.mkOptionType {
            name = bad;
            functor = {
              name = "f";
              binOp = null;
              payload.x = 1;
            };
          };
          expectedError = thrown "^gen-merge: the option type `<a name of type int>' states a parameter in its `functor' but leaves ";
        };
        test-unanswerable-relation-names-its-name-type = {
          expr = gm.mkOptionType {
            name = bad;
            functor = {
              binOp = a: _: a;
              payload = null;
            };
          };
          expectedError = thrown "^gen-merge: the option type `<a name of type int>' states a merge relation in `functor\\.binOp' ";
        };
        test-stated-relation-join-names-the-join-name-type = {
          expr = declaredTwice (gm.mkOptionType {
            name = "fr";
            check = _: true;
            functor = noRelation;
            typeMerge = _: { name = bad; };
          }) t.str;
          expectedError = refuses "`fr' and `string', which the first type's own `functor' joins to `<a name of type int>', a type that states neither declaration's own check";
        };
        test-rebuilt-type-without-a-relation-names-its-name-type = {
          expr =
            (gm.mkOptionType (
              leafProtocol
              // {
                name = "box";
                check = _: true;
                nestedTypes.elemType = t.str;
                recarry = _: { name = bad; };
              }
            )).functor.type
              { elemType = t.int; };
          expectedError = thrown "^gen-merge: the type `<a name of type int>' cannot be exported: it declares no type-merge relation";
        };
        test-an-unnamed-type-is-named-unnamed = {
          expr = declaredTwice (t.mkType { }) t.str;
          expectedError = refuses "`<unnamed>' and `string'";
        };
        test-an-unnamed-bare-type-declaration-is-named-unnamed = {
          expr = realize { modules = [ { options.x._type = "option-type"; } ]; };
          expectedError = thrown "^gen-merge: option `x' is declared as a bare type \\(`<unnamed>'\\), not a declaration; ";
        };
      };

    # THE REFUSAL NAMES THE NAME THAT GOVERNED. The foreign protocol keys a redeclaration on the
    # FUNCTOR name; a derivation keeps its base's TYPE name and distinguishes only the functor. So
    # the pair `int' and `int' refuses, and a message naming only type names reads as a
    # self-contradiction. Both sites that spell the pair now name the two functor names where they
    # differ: `foreignRel' (a stated relation) and the declaration plane's null-reason fallback (two
    # raw foreign records). The control keeps a functor-name clause out where the names agree.
    flake.testsError.refusal-names-the-functor-names =
      let
        declaredTwice =
          a: b:
          realize {
            modules = [
              { options.x = gm.mkOption { type = a; }; }
              { options.x = gm.mkOption { type = b; }; }
            ];
          };
        refuses = pair: {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(${pair}\\); declared in <gen-merge>, <gen-merge>$";
        };
        derivedInt =
          fname:
          gm.mkOptionType {
            name = "int";
            check = builtins.isInt;
            functor = {
              name = fname;
              type = null;
              payload = null;
              binOp = _: _: null;
            };
          };
        rawOf = fname: {
          name = "int";
          check = builtins.isInt;
          merge = _: defs: (builtins.head defs).value;
          functor = {
            name = fname;
            type = null;
            payload = null;
            binOp = _: _: null;
          };
          typeMerge = f: if f.name == fname then rawOf fname else null;
        };
      in
      {
        test-a-stated-relation-refusal-names-both-functor-names = {
          expr = declaredTwice (derivedInt "refined") t.int;
          expectedError = refuses "`int' and `int', which the first type's own `functor' \\(named `refined'\\) does not reconcile with the second's \\(named `int'\\)";
        };
        test-a-reasonless-refusal-names-both-functor-names = {
          expr = declaredTwice (rawOf "refined") (rawOf "int");
          expectedError = refuses "`int' and `int', whose functors are named `refined' and `int'";
        };
        test-control-agreeing-functor-names-are-not-named = {
          expr = declaredTwice (derivedInt "refined") (derivedInt "refined");
          expectedError = refuses "`int' and `int', which the first type's own `functor' does not reconcile";
        };
      };

    # THE NAMESPACE ASSEMBLY'S REFUSALS OVER A SUPPLIED VOCABULARY (den-hoag-2f4gm). Each names
    # what is wrong in the caller's terms; `tryEval` would discard which.
    flake.testsError.linkset-vocabulary = {
      # Owned staleness: an allowlist entry naming nothing the RIGHT side exports refuses, and the
      # message says it is judged against the side the allowlist decides for.
      test-stale-entry-names-the-side-it-is-judged-against = {
        expr =
          (genLinkset.mergeExports {
            left = {
              library = "l";
              exports = { };
            };
            right = {
              library = "gen-merge";
              exports.x = 1;
            };
            allow.nosuch.ground = "names a name the right side does not export";
          }).exports;
        expectedError = {
          type = "ThrownError";
          msg = "^linkset: allowlist entry 'nosuch' names no export of 'gen-merge', the side the allowlist decides in favour of\\.";
        };
      };
      # A non-attrset vocabulary refuses by name, catchably — it used to abort `mapAttrs`.
      test-null-vocabulary-refuses-by-name = {
        expr = builtins.attrNames (genMergeWith null).types;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: declares a `types' that is a null rather than a leaf vocabulary record \\(an attribute set\\)$";
        };
      };
      test-list-vocabulary-refuses-by-name = {
        expr = builtins.attrNames (genMergeWith [ ]).types;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: declares a `types' that is a list rather than a leaf vocabulary record \\(an attribute set\\)$";
        };
      };
      # The honest wiring mistake: the gen-types FLAKE passed where its `lib` belongs. Admitted, its
      # `narHash`/`inputs`/… published as types and `types.str` aborted uncatchably.
      test-flake-passed-as-vocabulary-refuses-by-name = {
        expr = (genMergeWith genTypesFlake).types.str;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: declares a `types' that is a tagged `flake' value rather than a leaf vocabulary record — a flake's outputs; its vocabulary is the flake's `lib'$";
        };
      };
      # Any other tagged value — here one type passed where a namespace of them belongs.
      test-single-type-passed-as-vocabulary-refuses-by-name = {
        expr = builtins.attrNames (genMergeWith nixpkgsLib.types.str).types;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: declares a `types' that is a tagged `option-type' value rather than a leaf vocabulary record$";
        };
      };
      # The undeclared refusal names the supplied vocabulary neutrally — this library cannot know
      # whose it is — and names the one name demanded, not the namespace's whole undecided set.
      test-undeclared-collision-names-the-supplied-vocabulary = {
        expr =
          (genMergeWith (
            nixpkgsLib.types // { inherit (genTypes) rewritesCheck witnessRecord witnessedCheck; }
          )).types.submodule;
        expectedError = {
          type = "ThrownError";
          msg = "^linkset: undeclared export collision between 'the supplied `types` vocabulary' and 'gen-merge' at name 'submodule'\\.";
        };
      };
      # The per-name refusal is a named, catchable refusal at the name, over a vocabulary that
      # shares only that name undeclared; `tests/linkset.nix` pins that the rest publishes.
      test-undeclared-collision-refuses-at-its-name = {
        expr =
          (genMergeWith {
            inherit (nixpkgsLib.types) str nullOr;
            inherit (genTypes) rewritesCheck witnessRecord witnessedCheck;
          }).types.nullOr;
        expectedError = {
          type = "ThrownError";
          msg = "^linkset: undeclared export collision between 'the supplied `types` vocabulary' and 'gen-merge' at name 'nullOr'\\.";
        };
      };
    };

    # THE `types` FORMAL IS THE gen-types LIBRARY, AND THE DOOR SAYS SO (den-hoag-ydro3). The core
    # builds every export through gen-types' check-witness protocol, so a `types` without it, or with
    # one the per-fold sites' inline test disagrees with, is refused at construction: each cell
    # demands `evalModuleTree`, which never touches the namespace, so the refusal is the core's. The
    # live control is every other cell in this repository, built over the shipped gen-types.
    flake.testsError.check-witness-protocol =
      let
        withoutProtocol =
          n:
          "^gen-merge: declares a `types' with no ${n} — the `types' formal is the gen-types library, whose check-witness protocol every type this library exports is built and read through \\(a gen-types older than that protocol lacks them\\)$";
        disagrees =
          what:
          "^gen-merge: declares a `types' whose check-witness protocol disagrees with the test this library restates inline at its per-fold sites: ${what}\\. The two spellings must say the same thing, so a gen-types whose witness changed needs a gen-merge restating the changed test$";
        record = fn: {
          __functor = self: self._fn;
          _fn = fn;
        };
        # DRIFT 1, a renamed field: gen-types' two functions agree with each other on a witness field
        # the inline test does not read, so the inline test would read every rewritten `check' as
        # the type's own.
        renamed = genTypes // {
          witnessedCheck =
            fn:
            let
              check = record fn;
            in
            {
              inherit check;
              _checkWitnessMoved = check;
            };
          rewritesCheck = t: t ? _checkWitnessMoved && t ? check && t.check != t._checkWitnessMoved;
        };
        # DRIFT 2, the same field holding something else: the inline test would read every own
        # `check' as rewritten.
        reshaped = genTypes // {
          witnessedCheck =
            fn:
            let
              check = record fn;
            in
            {
              inherit check;
              _checkWitness = { inherit check; };
            };
          rewritesCheck = t: t ? _checkWitness && t ? check && t.check != t._checkWitness.check;
        };
        # DRIFT 3, a field beyond the two: both tests still agree on the pair, but gen-merge
        # re-publishes the pair by its two names, so every exported type would lose the third and
        # gen-types' own test would read each as its own.
        widened = genTypes // {
          witnessedCheck =
            fn:
            let
              check = record fn;
            in
            {
              inherit check;
              _checkWitness = check;
              _witnessTag = true;
            };
          rewritesCheck = t: t ? _witnessTag && t ? _checkWitness && t ? check && t.check != t._checkWitness;
        };
        # DRIFT 4, a test answering other than a boolean: an `if` over its answer aborts
        # uncatchably at the first fold that asks, so the door names it first.
        notBool = genTypes // {
          rewritesCheck = _: null;
        };
        # DRIFT 5, the pair this library spells (den-hoag-ydro3 arm (c)): `witnessRecord`'s record
        # shaped otherwise than the one `witnessedCheck` publishes, so `exportType`'s pair is not
        # `witnessedCheck`'s.
        reshapedRecord = genTypes // {
          witnessRecord = fn: genTypes.witnessRecord fn // { _witnessTag = true; };
        };
        # ...or no record at all: a bare function, as the published `check` was before it was a record.
        bareRecord = genTypes // {
          witnessRecord = fn: fn;
        };
        # ...or shaped alike, but a record gen-types' own test does not read as a witness.
        unrecognisedRecord = genTypes // {
          witnessRecord = _: record null;
          rewritesCheck = t: genTypes.rewritesCheck t || (t ? check && t.check ? _fn && t.check._fn == null);
        };
      in
      {
        test-nixpkgs-types-as-the-vocabulary-refuses-by-name = {
          expr = (genMergeWith nixpkgsLib.types).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = withoutProtocol "`rewritesCheck', `witnessRecord', `witnessedCheck'";
          };
        };
        test-a-vocabulary-missing-one-protocol-name-names-it = {
          expr = (genMergeWith (removeAttrs genTypes [ "witnessedCheck" ])).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = withoutProtocol "`witnessedCheck'";
          };
        };
        test-a-protocol-name-that-cannot-be-applied-is-refused = {
          expr = (genMergeWith (genTypes // { rewritesCheck = true; })).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: declares a `types' whose `rewritesCheck' cannot be applied — the check-witness protocol every type this library exports is built and read through$";
          };
        };
        test-a-renamed-witness-field-is-refused-by-the-agreement-door = {
          expr = (genMergeWith renamed).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = disagrees "the inline test reads that pair with its `check' replaced as its own; the inline test's negation reads that pair with its `check' replaced as its own";
          };
        };
        test-a-witness-field-holding-something-else-is-refused-by-the-agreement-door = {
          expr = (genMergeWith reshaped).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = disagrees "the inline test reads the pair `witnessedCheck' built as rewritten; the inline test's negation reads the pair `witnessedCheck' built as rewritten";
          };
        };
        test-a-witness-pair-with-a-field-beyond-the-two-is-refused = {
          expr = (genMergeWith widened).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: declares a `types' whose `witnessedCheck' builds the fields `_checkWitness', `_witnessTag', `check' rather than exactly `check' and `_checkWitness', the two this library publishes on every exported type, so a field beyond them would be lost from each$";
          };
        };
        test-a-vocabulary-without-witnessRecord-names-it = {
          expr = (genMergeWith (removeAttrs genTypes [ "witnessRecord" ])).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = withoutProtocol "`witnessRecord'";
          };
        };
        test-a-test-answering-other-than-a-boolean-is-refused-by-name = {
          expr = (genMergeWith notBool).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: declares a `types' whose check-witness protocol answers other than a boolean: gen-types' `rewritesCheck' answers a null over the pair `witnessedCheck' built; gen-types' `rewritesCheck' answers a null over the pair `witnessedCheck' built with its `check' replaced\\. Its test is a predicate$";
          };
        };
        test-a-witness-record-shaped-otherwise-is-refused = {
          expr = (genMergeWith reshapedRecord).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: declares a `types' whose `witnessRecord' builds a record with the fields `__functor', `_fn', `_witnessTag' where the record `witnessedCheck' publishes has `__functor', `_fn', so the pair this library spells from it on every exported type is not the pair `witnessedCheck' builds$";
          };
        };
        test-a-witness-record-that-is-not-a-record-is-refused = {
          expr = (genMergeWith bareRecord).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: declares a `types' whose `witnessRecord' builds a lambda, where the check witness this library publishes under both fields of every exported type must be a record$";
          };
        };
        test-a-spelled-pair-the-test-reads-otherwise-is-refused = {
          expr = (genMergeWith unrecognisedRecord).evalModuleTree;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: declares a `types' whose check-witness protocol reads the pair this library spells from `witnessRecord' otherwise than the pair `witnessedCheck' builds: gen-types' `rewritesCheck' reads the pair this library spells from `witnessRecord' as rewritten\\. Every exported type publishes the spelled pair, so its witness would be misread$";
          };
        };
      };

    # A DECLARED `type` THAT IS NOT A TYPE IS REFUSED BY NAME WHERE THE FOLD DEMANDS IT (ADR-0025
    # item 1; `interface.typeDefect`). Each vocabulary member below publishes — the namespace judges
    # only what this library demands of it — and was accepted silently at the option, the definition
    # returned unchecked. One cell per arm of the predicate, and the freeform fold beside it.
    flake.testsError.declared-type =
      let
        T =
          (genMergeWith (
            genTypes
            // {
              bad5 = 5;
              badFn = _: 5;
              badPattern = { a }: genTypes.str;
              badTag = {
                _type = "option";
                type = genTypes.str;
                description = "d";
              };
            }
          )).types;
        read =
          type: v:
          realize {
            modules = [
              { options.p = gm.mkOption { inherit type; }; }
              { p = v; }
            ];
          };
        readCfg =
          type: v:
          (cfg {
            modules = [
              { options.p = gm.mkOption { inherit type; }; }
              { p = v; }
            ];
          }).p;
        refused = reason: {
          type = "ThrownError";
          msg = "^gen-merge: option `p' declares a `type' that ${reason}$";
        };
        notAType = kind: "is a value of type `${kind}', not a type";
        fnReason = "is a function, not a type \\(a type constructor must be applied\\)";
        freeform =
          type:
          realize {
            modules = [
              { freeformType = type; }
              { q = "a"; }
            ];
          };
      in
      {
        test-a-scalar-member-as-a-type-is-refused = {
          expr = read T.bad5 "a";
          expectedError = refused (notAType "int");
        };
        test-a-bare-constructor-as-a-type-is-refused = {
          expr = read T.enum "a";
          expectedError = refused fnReason;
        };
        test-an-under-applied-constructor-is-refused = {
          expr = read (T.enum "e") "a";
          expectedError = refused fnReason;
        };
        test-a-constructor-returning-a-non-type-is-refused = {
          expr = read (T.badFn 1) "a";
          expectedError = refused (notAType "int");
        };
        test-a-namespace-as-a-type-is-refused = {
          expr = read T.refinements "a";
          expectedError = refused "answers neither this library's type vocabulary nor any field of the foreign protocol";
        };
        test-a-tagged-non-type-is-refused = {
          expr = read T.badTag "a";
          expectedError = refused "is a tagged `option' value, not a type";
        };
        # An ABSENT `type` is the untyped option (the control below); a `type` stated as `null` is a
        # value in type position. nixpkgs refuses it too, uncatchably.
        test-a-null-type-is-refused = {
          expr = read null "a";
          expectedError = refused (notAType "null");
        };
        # Reached through the default alone: the fold demands the type there too.
        test-a-defaulted-option-with-a-non-type-is-refused = {
          expr = realize {
            modules = [
              {
                options.p = gm.mkOption {
                  type = T.bad5;
                  default = "d";
                };
              }
            ];
          };
          expectedError = refused (notAType "int");
        };
        # FALSIFIER, not a door: a pattern formal given the wrong set aborts inside the application,
        # before any value exists to be judged. Pinned so the door is never read as covering it.
        test-a-misapplied-pattern-constructor-aborts-before-the-door = {
          expr = read (T.badPattern { }) "a";
          expectedError = {
            type = "TypeError";
            msg = "called without required argument 'a'";
          };
        };
        test-a-non-type-freeform-is-refused = {
          expr = freeform T.bad5;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the freeform type is a value of type `int', not a type$";
          };
        };
        test-a-bare-constructor-freeform-is-refused = {
          expr = freeform T.enum;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the freeform type ${fnReason}$";
          };
        };
        # LIVE CONTROLS, same run. A leaf still refuses a bad definition with its own message and
        # admits a good one; the untyped option stays untyped; the fold's own vocabulary is admitted
        # (a type answering by `mergeDefs` alone, and the bare `mkType { }`); and the namespace door
        # is not widened — the scalar member still publishes.
        test-a-leaf-still-refuses-a-bad-definition-by-its-own-message = {
          expr = read T.str 1;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: a definition for option `p' is not of the expected type: ";
          };
        };
        test-controls-admitted = {
          expr = {
            str = readCfg T.str "a";
            untyped =
              (cfg {
                modules = [
                  { options.p = gm.mkOption { }; }
                  { p = "a"; }
                ];
              }).p;
            foldOnly = readCfg (T.mkType { mergeDefs = _loc: _defs: "folded"; }) "a";
            bareMkType = readCfg (T.mkType { }) "a";
            published = T ? bad5;
            freeform =
              (cfg {
                modules = [
                  { freeformType = T.attrsOf T.str; }
                  { q = "a"; }
                ];
              }).q;
          };
          expected = {
            str = "a";
            untyped = "a";
            foldOnly = "folded";
            bareMkType = "a";
            published = true;
            freeform = "a";
          };
        };
      };

    # A NON-TYPE IN AN ELEMENT POSITION IS REFUSED BY NAME WHERE A FOLD DEMANDS THE ELEMENT (ADR-0025
    # item 1). Every container demands its element through the published `mergeDefs`
    # (`lib/modules.nix` `mergeDefsWith`), and so does the freeform plane; each read below used to
    # return the definition unchecked. An element no fold demands is not judged (the controls).
    flake.testsError.element-type =
      let
        L = nixpkgsLib.types;
        read =
          type: v:
          realize {
            modules = [
              { options.p = gm.mkOption { inherit type; }; }
              { p = v; }
            ];
          };
        readCfg =
          type: v:
          (cfg {
            modules = [
              { options.p = gm.mkOption { inherit type; }; }
              { p = v; }
            ];
          }).p;
        refused = loc: reason: {
          type = "ThrownError";
          msg = "^gen-merge: option `${loc}' is folded through an element type that ${reason}$";
        };
        notAType = kind: "is a value of type `${kind}', not a type";
        freeform =
          type:
          cfg {
            modules = [
              { freeformType = type; }
              { x = "a"; }
            ];
          };
        direct =
          type:
          gm.mergeDefs [ "o" ] type [
            {
              file = "f";
              value = "a";
            }
          ];
      in
      {
        test-attrsOf-a-scalar-is-refused = {
          expr = read (t.attrsOf 5) { x = "a"; };
          expectedError = refused "p.x" (notAType "int");
        };
        test-listOf-a-scalar-is-refused = {
          expr = read (t.listOf 5) [ "a" ];
          expectedError = refused "p.0" (notAType "int");
        };
        test-nullOr-a-scalar-is-refused = {
          expr = read (t.nullOr 5) "a";
          expectedError = refused "p" (notAType "int");
        };
        test-either-a-scalar-first-is-refused = {
          expr = read (t.either 5 t.str) "a";
          expectedError = refused "p" (notAType "int");
        };
        # Nested: each level re-enters the same fold, and the loc names the concrete position.
        test-a-nested-scalar-element-is-refused-at-its-position = {
          expr = read (t.attrsOf (t.listOf 5)) { x = [ "a" ]; };
          expectedError = refused "p.x.0" (notAType "int");
        };
        test-attrsOf-a-bare-constructor-is-refused = {
          expr = read (t.attrsOf t.enum) { x = "a"; };
          expectedError = refused "p.x" "is a function, not a type \\(a type constructor must be applied\\)";
        };
        test-attrsOf-null-is-refused = {
          expr = read (t.attrsOf null) { x = "a"; };
          expectedError = refused "p.x" (notAType "null");
        };
        # The first member refuses the value, so the non-type member is the one chosen.
        test-either-a-scalar-reached-as-the-chosen-member-is-refused = {
          expr = read (t.either t.str 5) 1;
          expectedError = refused "p" (notAType "int");
        };
        # The published fold itself: `null` is a value in type position here too, never "untyped".
        test-the-published-mergeDefs-refuses-a-null-type = {
          expr = direct null;
          expectedError = refused "o" (notAType "null");
        };
        # The freeform plane folds its undeclared keys through the freeform type's own element.
        test-a-freeform-element-that-is-not-a-type-is-refused = {
          expr = builtins.deepSeq (freeform (t.attrsOf 5)) null;
          expectedError = refused "x" (notAType "int");
        };
        # LIVE CONTROLS, same run. The leaf still refuses a bad definition by its own message.
        test-an-element-leaf-still-refuses-a-bad-definition-by-its-own-message = {
          expr = read (t.attrsOf t.str) { x = 1; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: a definition for option `p.x' is not of the expected type: ";
          };
        };
        # Legitimate elements admit, over both vocabularies, and an element no fold demands is not
        # judged.
        test-element-controls-admitted = {
          expr = {
            str = readCfg (t.attrsOf t.str) { x = "a"; };
            raw = readCfg (t.attrsOf t.raw) { x = "a"; };
            bareMkType = readCfg (t.attrsOf (t.mkType { })) { x = "a"; };
            foldOnly = readCfg (t.attrsOf (t.mkType { mergeDefs = _loc: _defs: "folded"; })) { x = "a"; };
            submodule = readCfg (t.attrsOf (t.submodule { options.q = gm.mkOption { type = t.str; }; })) {
              x.q = "a";
            };
            nullOr = readCfg (t.nullOr t.str) "a";
            either = readCfg (t.either t.int t.str) "a";
            foreignContainer = readCfg (L.attrsOf t.str) { x = "a"; };
            foreignElement = readCfg (t.attrsOf L.str) { x = "a"; };
            directRaw = direct t.raw;
            freeform = (freeform (t.attrsOf t.str)).x;
            emptyAttrsOf = readCfg (t.attrsOf 5) { };
            nullNullOr = readCfg (t.nullOr 5) null;
            firstMember = readCfg (t.either t.str 5) "a";
          };
          expected = {
            str.x = "a";
            raw.x = "a";
            bareMkType.x = "a";
            foldOnly.x = "folded";
            submodule.x.q = "a";
            nullOr = "a";
            either = "a";
            foreignContainer.x = "a";
            foreignElement.x = "a";
            directRaw = "a";
            freeform = "a";
            emptyAttrsOf = { };
            nullNullOr = null;
            firstMember = "a";
          };
        };
        # THE LAZINESS CONTRACT: the element is judged at its fold and never before it. Reading the
        # keys forces no element, and an element type bound through the config is read at the fold,
        # where a judgement at the container's construction would force it early.
        test-reading-the-keys-forces-no-element = {
          expr = builtins.attrNames (readCfg (t.attrsOf 5) { x = "a"; });
          expected = [ "x" ];
        };
        test-a-config-derived-element-type-is-read-at-the-fold = {
          expr =
            (cfg {
              modules = [
                (
                  { config, ... }:
                  {
                    options.t = gm.mkOption {
                      type = t.raw;
                      default = t.raw;
                    };
                    options.p = gm.mkOption { type = t.attrsOf config.t; };
                  }
                )
                { p.x = "a"; }
              ];
            }).p;
          expected.x = "a";
        };
      };

    # den-hoag-n6dh7 Unit 2.1: the nesting declaration's two refusals. `declaresNesting` at fuel
    # exhaustion (S2, RULED (i)) names the fuel and the remedy, on nixpkgs' `types.json` shape; a
    # `declaresNesting` marker other than `false` is refused at `mkOptionType`, naming the field.
    # `ci/tests/nesting-declaration.nix` pins that each is catchable and holds the opt-out's arm.
    flake.testsError.nesting-declaration =
      let
        np = nixpkgsLib.types;
        valueType = np.nullOr (
          np.oneOf [
            np.str
            (np.attrsOf valueType)
            (np.listOf valueType)
          ]
        );
      in
      {
        test-a-self-referential-element-is-refused-naming-the-fuel-and-the-remedy = {
          expr = interface.declaresNesting (np.uniq valueType);
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: cannot decide whether the option type `unique' declares a gen nesting type as an element: its type structure nests deeper than the walk's fuel [(]32[)], as a self-referential element does[.] Wrap the element in a recognised container [(]attrsOf, lazyAttrsOf, listOf, nullOr, either, oneOf[)], declare no gen nesting element, or state the answer with `declaresNesting = false' on the type$";
          };
        };
        test-a-true-marker-is-refused-at-mk-option-type = {
          expr = force (
            gm.mkOptionType {
              name = "marked";
              declaresNesting = true;
            }
          );
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option type `marked' states `declaresNesting' as `true'; the field is a declared opt-out and takes only `false'[.] A type that wraps a gen nesting type states it by carrying that type as its element, not by this field$";
          };
        };
        test-a-non-boolean-marker-is-refused-at-mk-option-type = {
          expr = force (
            gm.mkOptionType {
              name = "marked";
              declaresNesting = "no";
            }
          );
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the option type `marked' states `declaresNesting' as a string; the field is a declared opt-out and takes only `false'[.] A type that wraps a gen nesting type states it by carrying that type as its element, not by this field$";
          };
        };
      };

    # den-hoag-n6dh7 Unit 2.2: the import refusal (OQ11 (d)) at both of its doors, and S2 (i)'s fuel
    # refusal at the engine's. The engine's names `evalModuleTree` and the option; `mkOptionType`'s
    # names that door. Each names the container and what in it declared the element.
    # `ci/tests/nesting-threaded.nix` pins that each is catchable. The one `submodule` row of U2-o
    # (a lax tree inside a `submodule`, whose child evaluates in the submodule's called mode) keeps
    # today's literal, and the `$` is load-bearing: a message with a suffix fails it.
    flake.testsError.nesting-threaded =
      let
        np = nixpkgsLib.types;
        sub = t.submodule { options.x = gm.mkOption { type = t.int; }; };
        opt =
          type: def:
          force
            (gm.evalModuleTree {
              modules = [
                {
                  options.h = gm.mkOption { inherit type; };
                  config.h = def;
                }
              ];
            }).config.h;
        protocol = {
          inherit (sub) getSubOptions getSubModules;
          substSubModules = _: sub;
        };
        valueType = np.nullOr (
          np.oneOf [
            np.str
            (np.attrsOf valueType)
            (np.listOf valueType)
          ]
        );
        # The remedies are the ones that exist (den-hoag-f8mgj M6): the six, a container whose
        # rebuild threads, and the opt-out with its price.
        rule = "and it cannot thread the evaluation to that nested tree here[.] Use attrsOf, lazyAttrsOf, listOf, nullOr, either or oneOf; or, bound in gen's own evaluation rather than through `mkOptionType', a container whose `substSubModules' rebuild states its element and whose `check' does not read the nested tree; or state `declaresNesting = false' on the type and take the stated price: a nested tree it forwards to is then evaluated standalone$";
        # The option's value applied to `null`, forced: a function-valued option's body.
        call =
          type: def:
          force (
            (gm.evalModuleTree {
              modules = [
                {
                  options.h = gm.mkOption { inherit type; };
                  config.h = def;
                }
              ];
            }).config.h
              null
          );
        # The verdict on a refined gen element under a threaded container and under its sibling.
        refinedElement = {
          type = "ThrownError";
          msg = "^gen-merge: a definition for option `h[.]a' is not of type `submodule', in `<gen-merge>'$";
        };
        # A hand-rolled forwarding container: its rebuild is `drop` where given, and otherwise
        # forwards the module list to its element, as nixpkgs' own containers do.
        fwdBy =
          drop: elem:
          nixpkgsLib.mkOptionType {
            name = "fwd";
            check = _: true;
            merge = loc: defs: elem.merge loc defs;
            nestedTypes.elemType = elem;
            inherit (elem) getSubOptions getSubModules;
            substSubModules = if drop != null then drop else (m: fwdBy null (elem.substSubModules m));
          };
        # The door and the option, as the caller named them.
        atEngine = "`evalModuleTree' at option `h': ";
        atImport = "`mkOptionType': ";
        # OQ1 arm (ii-a): the walk's offer refusal, opened with the caller's door.
        offered =
          door: name:
          "^gen-merge: ${door}the option type `${name}' offers a type declaring a gen nesting type to merge on [(]its functor payload's `elemType'[)] but states no element it carries; a payload says what a type merges on, not what it carries, so its fold would evaluate the nested tree standalone and nothing would say so[.] State the element in `nestedTypes[.]elemType' or a top-level `elemType', or state `declaresNesting = false' on the type and take that stated price$";
        # OQ2 arm (b): the disagreement between what a record carries and what it merges on.
        disagrees =
          name: what:
          "^gen-merge: ${atEngine}the option type `${name}' states its ${what} in a carrying spelling and offers a different one to merge on in its functor payload's `elemType'; it would carry one type and merge on another, so no reading of it is the type it states[.] State the same type in both$";
        # nixpkgs' `types.json` shape, built once per call: two calls are two distinct constructions
        # of one shape, each with a self-referential `description`.
        json =
          _:
          let
            v = np.nullOr (
              np.oneOf [
                np.str
                (np.attrsOf v)
                (np.listOf v)
              ]
            );
          in
          v;
        # A strict tree record, built once per call: two calls are two distinct constructions.
        tree =
          _:
          (gm.evalModuleTree {
            modules = [ { options.a = gm.mkOption { type = t.int; }; } ];
          }).type;
      in
      {
        # F2 α (M3): a rebuild that drops its argument does not state the threaded element, and would
        # reach the tree through the bridge, so it is refused by name (one that forwards it threads:
        # `ci/tests/nesting-threaded.nix`, `nesting-threaded-rehome`).
        test-a-rebuild-that-drops-its-element-is-refused-by-name = {
          expr = opt (fwdBy (_: sub) sub) { x = 1; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `evalModuleTree' at option `h': the option type `fwd' declares a gen nesting type as an element [(]its `nestedTypes[.]elemType'[)], ${rule}";
          };
        };
        # Condition (2) (M4): `functionTo` folds its element inside the function it returns, where its
        # merge exposes no site, so a nested-tree read there is refused by name; a member that never
        # reads the tree (a string definition) still answers (`nesting-threaded-rehome`).
        test-a-tree-folded-where-the-merge-does-not-expose-it-is-refused-by-name = {
          expr = call (np.functionTo (t.either (tree null) t.str)) (_: {
            a = 1;
          });
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `evalModuleTree' at option `h[.]<function body>': the option type `functionTo' folds its gen nesting element at a position its own merge does not expose when the option is merged [(]inside a value it returns, such as a function body[)], so that nested tree cannot be threaded into this evaluation[.] Declare the tree at a position the merge returns as a value, or state `declaresNesting = false' on the type and take the stated price: a nested tree it forwards to is then evaluated standalone$";
          };
        };
        # M8: the record's own `check` rides on the threaded fold, and the verdict names the
        # container. Over `attrsWith{placeholder}` the name is `attrsOf', as on the sibling.
        test-a-container-refinement-is-enforced-on-the-threaded-fold = {
          expr = opt (np.addCheck (np.attrsWith {
            elemType = sub;
            placeholder = "host";
          }) (_: false)) { a.x = 1; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: a definition for option `h' is not of type `attrsOf', in `<gen-merge>'$";
          };
        };
        test-a-unique-refinement-is-enforced-on-the-threaded-fold = {
          expr = opt (np.addCheck (np.uniq sub) (_: false)) { x = 1; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: a definition for option `h' is not of type `unique', in `<gen-merge>'$";
          };
        };
        # A rewrite over `unique` whose check reads the tree is evaluated on the value (the tree's
        # `check` is its module-value domain), so a passing one serves.
        test-a-unique-refinement-that-reads-the-tree-is-served = {
          expr =
            (gm.evalModuleTree {
              modules = [
                {
                  options.h = gm.mkOption { type = np.addCheck (np.uniq (tree null)) (_: true); };
                  config.h = {
                    a = 1;
                  };
                }
              ];
            }).config.h;
          expected = {
            a = 1;
          };
        };
        # G1: a refinement on the ELEMENT under `unique` leaves a lambda in the compared slot, which is
        # never read as stock (`==` on a lambda is evaluator-dependent), so it is refused, never served.
        test-a-unique-over-a-refined-tree-union-is-refused = {
          expr = opt (np.unique { message = "m"; } (np.addCheck (t.either (tree null) t.str) (_: false))) {
            a = 1;
          };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: a definition for option `h' is not of type `unique', in `<gen-merge>'$";
          };
        };
        # A `coercedTo` over a union holding the tree is served: the union's check reads only the value.
        test-a-coerced-to-over-a-tree-union-is-served = {
          expr =
            (gm.evalModuleTree {
              modules = [
                {
                  options.h = gm.mkOption { type = np.coercedTo np.bool (_: null) (t.either (tree null) t.str); };
                  config.h = {
                    a = 1;
                  };
                }
              ];
            }).config.h;
          expected = {
            a = 1;
          };
        };
        # G2: a refinement on the threaded ELEMENT is carried as the engine's threaded site carries it,
        # so `attrsWith{placeholder}` and `attrListOf` refuse exactly as the sibling `attrsOf` does.
        test-an-element-refinement-is-carried-on-a-placeholder-attrs-with = {
          expr = opt (np.attrsWith {
            elemType = np.addCheck sub (_: false);
            placeholder = "host";
          }) { a.x = 1; };
          expectedError = refinedElement;
        };
        test-an-element-refinement-is-carried-on-an-attr-list-of = {
          expr = opt (np.attrListOf (np.addCheck sub (_: false))) { a.x = 1; };
          expectedError = refinedElement;
        };
        test-an-element-refinement-is-carried-on-the-sibling-attrs-of = {
          expr = opt (np.attrsOf (np.addCheck sub (_: false))) { a.x = 1; };
          expectedError = refinedElement;
        };
        test-an-element-refinement-that-reads-the-tree-is-refused-by-name = {
          expr = opt (np.attrsWith {
            elemType = np.addCheck (t.either (tree null) t.str) (_: false);
            placeholder = "host";
          }) { a.x = 1; };
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: a definition for option `h[.]a' is not of type `either', in `<gen-merge>'$";
          };
        };
        test-a-hand-rolled-container-declaring-by-nested-types-is-refused-at-construction = {
          expr = force (
            gm.mkOptionType (
              {
                name = "fwd";
                merge = loc: defs: sub.merge loc defs;
                nestedTypes.elemType = sub;
              }
              // protocol
            )
          );
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `mkOptionType': the option type `fwd' declares a gen nesting type as an element [(]its `nestedTypes[.]elemType'[)], ${rule}";
          };
        };
        # The payload answers only what a type merges on (the 2026-09-25 ruling), so a record whose
        # payload is its only statement declares nothing; offering a nesting element there is
        # refused by name (OQ1 arm (ii-a)), at construction and at the engine alike.
        test-a-hand-rolled-container-offering-by-payload-is-refused-at-construction = {
          expr = force (
            gm.mkOptionType (
              {
                name = "fwd";
                merge = loc: defs: sub.merge loc defs;
                functor = {
                  name = "fwd";
                  payload.elemType = sub;
                  binOp = _: _: null;
                  type = _: null;
                  wrapped = null;
                };
              }
              // protocol
            )
          );
          expectedError = {
            type = "ThrownError";
            msg = offered atImport "fwd";
          };
        };
        test-a-stock-container-stripped-of-its-nested-types-is-refused-at-the-engine = {
          expr = opt (np.listOf sub // { nestedTypes = { }; }) [ { x = 1; } ];
          expectedError = {
            type = "ThrownError";
            msg = offered atEngine "listOf";
          };
        };
        # The top-level `elemType` is a carrying spelling `statedRoles` reads, so a record stating
        # its element only there declares it.
        test-a-hand-rolled-container-declaring-by-top-level-elemType-is-refused-at-construction = {
          expr = force (
            gm.mkOptionType (
              {
                name = "fwd";
                merge = loc: defs: sub.merge loc defs;
                elemType = sub;
              }
              // protocol
            )
          );
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `mkOptionType': the option type `fwd' declares a gen nesting type as an element [(]its `elemType'[)], ${rule}";
          };
        };
        # OQ2 arm (b): a stock container whose payload offers one element and whose `nestedTypes`
        # states another is refused, never re-homed over either.
        test-a-container-whose-two-elements-disagree-is-refused-at-the-engine = {
          expr = opt (np.listOf np.str // { nestedTypes.elemType = sub; }) [ "a" ];
          expectedError = {
            type = "ThrownError";
            msg = disagrees "listOf" "element";
          };
        };
        test-a-union-whose-two-member-lists-disagree-is-refused-at-the-engine = {
          expr = opt (
            np.either np.int np.str
            // {
              nestedTypes = {
                left = sub;
                right = np.str;
              };
            }
          ) "a";
          expectedError = {
            type = "ThrownError";
            msg = disagrees "either" "members";
          };
        };
        # A tree is compared by its `merge` alone, since every tree publishes the same module-value
        # `check` (den-hoag-4ifgb M0, den-hoag-f8mgj arm Q), and a disagreement over it is still this refusal, not the tree's
        # tombstone: a tree stated over another element offered, and two trees constructed apart.
        test-a-container-stating-a-tree-and-offering-another-element-is-refused-at-the-engine = {
          expr = opt (np.listOf np.str // { nestedTypes.elemType = tree 1; }) [ "a" ];
          expectedError = {
            type = "ThrownError";
            msg = disagrees "listOf" "element";
          };
        };
        # The guard is symmetric: a tree OFFERED against another element stated is refused by name
        # too, and does not fall back to comparing the tree's `check` (M0 gate C2).
        test-a-container-offering-a-tree-and-stating-another-element-is-refused-at-the-engine = {
          expr = opt (np.listOf (tree 1) // { nestedTypes.elemType = np.str; }) [ { } ];
          expectedError = {
            type = "ThrownError";
            msg = disagrees "listOf" "element";
          };
        };
        test-two-constructions-of-a-tree-disagree-by-name = {
          expr = opt (np.listOf (tree 1) // { nestedTypes.elemType = tree 2; }) [ { } ];
          expectedError = {
            type = "ThrownError";
            msg = disagrees "listOf" "element";
          };
        };
        # The disagreement is judged whether or not the record would be re-homed: a container over
        # no nesting element whose two statements differ is refused with the same reason.
        test-a-non-nesting-container-whose-two-elements-disagree-is-refused-at-the-engine = {
          expr = opt (np.listOf np.str // { nestedTypes.elemType = np.int; }) [ "a" ];
          expectedError = {
            type = "ThrownError";
            msg = disagrees "listOf" "element";
          };
        };
        # Two separate constructions of a self-referential type are two elements: compared by their
        # `check` and `merge` closures, never whole, the disagreement is the named refusal and not an
        # uncatchable recursion through `description`.
        test-two-constructions-of-a-self-referential-element-disagree-by-name = {
          expr = opt (np.listOf (json 1) // { nestedTypes.elemType = json 2; }) [ "x" ];
          expectedError = {
            type = "ThrownError";
            msg = disagrees "listOf" "element";
          };
        };
        test-two-constructions-of-a-self-referential-member-disagree-by-name = {
          expr = opt (
            np.either (json 1) np.str
            // {
              nestedTypes = {
                left = json 2;
                right = np.str;
              };
            }
          ) "x";
          expectedError = {
            type = "ThrownError";
            msg = disagrees "either" "members";
          };
        };
        # The payload-side element is not compared whole, so a `type` it carries is never read.
        test-a-payload-element-s-type-is-not-read-to-judge-a-disagreement = {
          expr = opt (
            np.listOf (np.str // { type = throw "gen-merge test: the payload element's type was read"; })
            // {
              nestedTypes.elemType = np.int;
            }
          ) [ "a" ];
          expectedError = {
            type = "ThrownError";
            msg = disagrees "listOf" "element";
          };
        };
        test-an-unmarked-self-referential-element-is-refused-at-the-engine = {
          expr = opt (np.uniq valueType) "x";
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: cannot decide whether the option type `unique' declares a gen nesting type as an element: its type structure nests deeper than the walk's fuel [(]32[)], as a self-referential element does[.] Wrap the element in a recognised container [(]attrsOf, lazyAttrsOf, listOf, nullOr, either, oneOf[)], declare no gen nesting element, or state the answer with `declaresNesting = false' on the type$";
          };
        };
        test-a-lax-tree-inside-a-submodule-refuses-its-finding-as-today = {
          expr =
            (gm.evalModuleTree {
              modules = [
                {
                  options.s = gm.mkOption {
                    type = t.submodule {
                      options.t = gm.mkOption {
                        type =
                          (gm.evalModuleTree {
                            modules = [ { options.x = gm.mkOption { type = t.int; }; } ];
                            check = false;
                          }).type;
                      };
                    };
                  };
                  config.s.t = {
                    x = 1;
                    bogus = 2;
                  };
                }
              ];
            }).config.s.t.x;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: option `s[.]t[.]bogus' is not declared by the nested tree that owns it$";
          };
        };
      };

    # den-hoag-n6dh7 Unit 2.4: S1 class (a), RULED (iii). A container that keys its elements by
    # reading their definitions, holding nested trees, under an over-approximating container other
    # than `lazyAttrsOf` (under `lazyAttrsOf` it is a container node, den-hoag-9d80v), is refused by
    # name where its positions are keyed, naming the option, both containers and the upgrade path.
    # `overRoot` is `lazyAttrsOf` under another name: the walk reads a container by its name, so it
    # stands for every other split container whose fold sets no mark (gen-aspects' `aspectsRoot`, or
    # a freeform plane typed by one).
    flake.testsError.nesting-keys = {
      test-a-strict-container-of-trees-under-another-over-approximating-one-names-both-containers = {
        expr =
          let
            r = genMergeCore.evalModuleTreeExposed {
              modules = [
                {
                  options.o = gm.mkOption {
                    type = overRoot (t.attrsOf (t.submodule { options.x = gm.mkOption { type = t.int; }; }));
                  };
                  config.o.j.k.x = 1;
                }
              ];
            };
          in
          force r._evaluation.allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: nta: option `o' declares `attrsOf' of nested trees under `overRoot': the inner container keys its elements by reading their definitions, and under a container that does not, keying one nested tree would force every sibling's definition[.] Declare the inner container outside `overRoot', or make it lazy; a container node admits the shape under `lazyAttrsOf' only, whose fold reads it$";
        };
      };
      # den-hoag-i4c0n C1's guard arm: the child of an undefined, default-less union with a nesting
      # member refuses as a candidate, never with the merge record's "used but not defined", which
      # reading the fold's `typeDefs` off that record unguarded raises.
      test-an-undefined-union-childs-read-refuses-as-a-candidate = {
        expr =
          let
            r = genMergeCore.evalModuleTreeExposed {
              modules = [
                {
                  options.o = gm.mkOption {
                    type = t.either (t.submodule { options.x = gm.mkOption { type = t.int; }; }) t.str;
                  };
                }
              ];
            };
          in
          force
            (r._evaluation.get (genScope.mintNtaId {
              host = "module-tree";
              name = "nested";
              group = "[\"o\"]";
              key = "[]";
            }) "result").config;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `evalModuleTree': option `o': the fold of the tree holding it did not select a nested tree at this position [(]it folds as `string'[)], so this nested tree is a candidate and is never evaluated$";
        };
      };
    };

    # den-hoag-n6dh7 Unit 2.4, placement: the refusals a nested tree's placement adds, each anchored
    # `^…$`. `ci/tests/nesting-placement.nix` pins that each is catchable where it fires.
    flake.testsError.nesting-placement =
      let
        sub = t.submodule { options.x = gm.mkOption { type = t.int; }; };
        host =
          type: defs:
          [
            { options.o = gm.mkOption { inherit type; }; }
          ]
          ++ map (d: { config.o = d; }) defs;
        tree =
          (gm.evalModuleTree {
            modules = [ { options.x = gm.mkOption { type = t.int; }; } ];
          }).type;
        laxTree =
          (gm.evalModuleTree {
            check = false;
            modules = [ { options.x = gm.mkOption { type = t.int; }; } ];
          }).type;
        recsub = t.submodule {
          options.x = gm.mkOption { type = recsub; };
          options.v = gm.mkOption {
            type = t.int;
            default = 7;
          };
        };
        down = d: v: if d == 0 then v else down (d - 1) v.x;
        called =
          type: field: loc:
          "^gen-merge: `${type}'${
            if loc == null then "" else " at option `${loc}'"
          }: its called `${field}' does not evaluate the nested tree: a nested tree is a child of the one evaluation that holds it [(]`evalModuleTree'[)], read through its fold's threaded sibling, and no second evaluation is made for it$";
      in
      {
        # U2-l: a candidate's `result`, read by its identifier.
        test-a-candidates-result-names-the-door-and-its-loc = {
          expr =
            let
              r = genMergeCore.evalModuleTreeExposed {
                modules = host (t.lazyAttrsOf (t.either sub t.str)) [ { foo = "s"; } ];
              };
            in
            force
              (r._evaluation.get (genScope.mintNtaId {
                host = "module-tree";
                name = "nested";
                group = "[\"o\"]";
                key = "[\"foo\"]";
              }) "result").config;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `evalModuleTree': option `o[.]foo': the fold of the tree holding it did not select a nested tree at this position [(]it folds as `string'[)], so this nested tree is a candidate and is never evaluated$";
          };
        };
        # U2-r: a union's container member under an over-approximating container other than
        # `lazyAttrsOf`, S1 class (a), RULED (iii).
        test-a-unions-strict-container-under-another-over-approximating-one-names-the-union-and-its-position = {
          expr =
            force
              (genMergeCore.evalModuleTreeExposed {
                modules = host (overRoot (t.either (t.attrsOf sub) t.str)) [ { p.a.x = 1; } ];
              })._evaluation.allNodeIds;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: nta: option `o' declares `either' at position \\[\"p\"\\], whose member `attrsOf' holds nested trees, under `overRoot': the member keys its elements by reading their definitions, and under a container that does not, keying one nested tree would force every sibling's definition[.] Declare the member outside `overRoot', or make it lazy; a container node admits the shape under `lazyAttrsOf' only, whose fold reads it$";
          };
        };
        # S1 class (a) with a LAZY inner container: refused on (iii)'s own ground, *defaulted,
        # reversible* (orchestrator ruling, den-hoag-n6dh7); the text does not call it strict, and
        # names arm (v), the container node (den-hoag-9d80v). And `listOf` under the same container.
        test-a-lazy-container-of-trees-under-another-over-approximating-one-is-refused-without-calling-it-strict = {
          expr =
            force
              (genMergeCore.evalModuleTreeExposed {
                modules = host (overRoot (t.lazyAttrsOf sub)) [ { j.k.x = 1; } ];
              })._evaluation.allNodeIds;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: nta: option `o' declares `lazyAttrsOf' of nested trees under `overRoot': the inner container's key set is its definitions' data, and under a container that does not read them, keying one nested tree would force every sibling's definition[.] Declare the inner container outside `overRoot'; a container node admits the shape under `lazyAttrsOf' only, whose fold reads it$";
          };
        };
        test-a-list-of-trees-under-another-over-approximating-container-is-refused = {
          expr =
            force
              (genMergeCore.evalModuleTreeExposed {
                modules = host (overRoot (t.listOf sub)) [ { j = [ { x = 1; } ]; } ];
              })._evaluation.allNodeIds;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: nta: option `o' declares `listOf' of nested trees under `overRoot': the inner container keys its elements by reading their definitions, and under a container that does not, keying one nested tree would force every sibling's definition[.] Declare the inner container outside `overRoot', or make it lazy; a container node admits the shape under `lazyAttrsOf' only, whose fold reads it$";
          };
        };
        # U2-s: growth over empty seeds past the fuel.
        test-growth-over-empty-seeds-names-the-fuel-and-the-remedy = {
          expr = force (down 32 (gm.evalModuleTree { modules = host recsub [ ]; }).config.o);
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: `evalModuleTree': option `x' holds a nested tree with no definition inside 32 enclosing nested trees that have none either: a nesting type that holds itself grows undefined trees without end, and the walk refuses past its fuel of 32 rather than hang[.] Define the position, or reach the recursion through a container whose keys are data [(]`attrsOf', `listOf'[)]$";
          };
        };
        # Item 1: every evaluating field of a nesting type refuses where it is CALLED.
        test-a-submodules-called-fold-refuses = {
          expr = force (
            gm.mergeDefs [ "o" ] sub [
              {
                file = "/f";
                value.x = 1;
              }
            ]
          );
          expectedError = {
            type = "ThrownError";
            msg = called "submodule" "mergeDefs" "o";
          };
        };
        test-a-submodules-called-empty-value-refuses = {
          expr = force sub.whenEmpty.value;
          expectedError = {
            type = "ThrownError";
            msg = called "submodule" "whenEmpty" null;
          };
        };
        test-the-tree-records-called-fold-refuses = {
          expr = force (
            gm.mergeDefs [ "o" ] tree [
              {
                file = "/f";
                value.x = 1;
              }
            ]
          );
          expectedError = {
            type = "ThrownError";
            msg = called "moduleTree" "mergeDefs" "o";
          };
        };
        test-the-tree-records-called-empty-value-refuses = {
          expr = force tree.whenEmpty.value;
          expectedError = {
            type = "ThrownError";
            msg = called "moduleTree" "whenEmpty" null;
          };
        };
        # U2-o's `submodule` row (v7, gate v1 K2): a lax tree inside a `submodule` evaluates in the
        # submodule's called mode, `{ true; false; }`, so the finding is today's, byte for byte. The
        # `$` is load-bearing: v6's mode gives a message carrying this one as its prefix.
        test-a-lax-tree-inside-a-submodule-refuses-with-todays-message = {
          expr =
            force
              (gm.evalModuleTree {
                modules = [
                  {
                    options.s = gm.mkOption {
                      type = t.submodule { options.t = gm.mkOption { type = laxTree; }; };
                    };
                  }
                  {
                    _file = "/r1";
                    config.s.t = {
                      x = 1;
                      bogus = 2;
                    };
                  }
                ];
              }).config.s.t;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: option `s[.]t[.]bogus' is not declared by the nested tree that owns it$";
          };
        };
      };

    # A CHECK A FOREIGN WRAPPER STATES OVER A GEN RECORD (den-hoag-4ifgb; `../tests/check-carriage.nix`
    # holds the values). Carried, its refusal is the checked fold's, naming the option and the file.
    # Over a member holding the nested tree the rewritten check is evaluated too (the tree's `check`
    # is its module-value domain), so a failing one refuses as the checked fold and a passing one serves.
    flake.testsError.check-carriage =
      let
        np = nixpkgsLib.types;
        no = _: false;
        tree =
          (gm.evalModuleTree {
            modules = [
              {
                options.a = gm.mkOption {
                  type = t.int;
                  default = 0;
                };
              }
            ];
          }).type;
        sub = t.submodule { options.a = gm.mkOption { type = t.int; }; };
        opt =
          T: V:
          realize {
            modules = [
              { options.s = gm.mkOption { type = T; }; }
              {
                _file = "def.nix";
                s = V;
              }
            ];
          };
        carried = name: {
          type = "ThrownError";
          msg = "^gen-merge: a definition for option `s' is not of type `${name}', in `def[.]nix'$";
        };
      in
      {
        test-a-rewritten-leaf-check-refuses-as-the-checked-fold = {
          expr = opt (np.addCheck t.int no) 5;
          expectedError = carried "int";
        };
        test-a-re-homed-non-empty-list-refuses-as-the-checked-fold = {
          expr = opt (np.nonEmptyListOf sub) [ ];
          expectedError = carried "listOf";
        };
        test-a-rewritten-check-over-a-union-holding-the-tree-refuses-as-the-checked-fold = {
          expr = opt (np.addCheck (t.either tree t.str) no) { a = 5; };
          expectedError = carried "either";
        };
        test-a-passing-rewritten-check-over-a-union-holding-the-tree-is-served = {
          expr =
            (cfg {
              modules = [
                { options.s = gm.mkOption { type = np.addCheck (t.either tree t.str) (_: true); }; }
                {
                  s = {
                    a = 5;
                  };
                }
              ];
            }).s;
          expected = {
            a = 5;
          };
        };
        test-a-rewritten-check-over-a-nullable-tree-refuses-as-the-checked-fold = {
          expr = opt (np.addCheck (t.nullOr tree) no) { a = 5; };
          expectedError = carried "nullOr";
        };
        test-a-rewritten-check-over-a-union-member-holding-the-tree-refuses-as-the-checked-fold = {
          expr = opt (t.listOf (np.addCheck (t.either tree t.str) no)) [ { a = 5; } ];
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: a definition for option `s[.]0' is not of type `either', in `def[.]nix'$";
          };
        };
      };

    # den-hoag-7gp66 P1: which message fires for gen-merge's three closed doors — evalModuleTree
    # (mixed), lint (record), mkCoreValue (record) — now that each routes through gen-prelude's
    # shared `checkOptions` / `checkRequired` (R6: names the door first, the construct last).
    # `ci/tests/door-checks.nix` pins that each refusal is catchable and that a record door still
    # admits an extra field; this suite pins the exact wording. evalModuleTree's cells force only
    # the application, since the door refuses there.
    flake.testsError.door-checks =
      let
        pin = door: msg: {
          type = "ThrownError";
          msg = "^${door}: ${msg}$";
        };
      in
      {
        test-eval-module-tree-unknown-option-named = {
          expr = builtins.seq (gm.evalModuleTree {
            modules = [ ];
            notAnOption = 1;
          }) null;
          expectedError = pin "gen-merge[.]evalModuleTree" "'notAnOption' is not an option of this door; the options are closed [(]accepted: 'modules', 'specialArgs', 'check', 'prefix', 'coreShortCircuit', 'warmFrom', 'editedModules'[)] [(]in prelude[.]checkOptions[)]";
        };
        test-eval-module-tree-missing-modules-named = {
          expr = builtins.seq (gm.evalModuleTree { }) null;
          expectedError = pin "gen-merge[.]evalModuleTree" "required field 'modules' is missing [(]required: 'modules'[)] [(]in prelude[.]checkRequired[)]";
        };
        test-eval-module-tree-non-set-named = {
          expr = builtins.seq (gm.evalModuleTree "modules") null;
          expectedError = pin "gen-merge[.]evalModuleTree" "the argument must be an attrset, not a string [(]required: 'modules'[)] [(]in prelude[.]checkRequired[)]";
        };
        test-lint-missing-modules-named = {
          expr = force (gm.lint { });
          expectedError = pin "gen-merge[.]lint" "required field 'modules' is missing [(]required: 'modules'[)] [(]in prelude[.]checkRequired[)]";
        };
        test-mk-core-value-missing-values-named = {
          expr = force (gm.mkCoreValue { digest = "d"; });
          expectedError = pin "gen-merge[.]mkCoreValue" "required field 'values' is missing [(]required: 'digest', 'values'[)] [(]in prelude[.]checkRequired[)]";
        };
      };

    # THE RESERVATION SCOPE (`__reservedKeys`, den-hoag-8x97u): a name the marker reserves, written
    # at the top level of any module the marked one imports, is refused with the supplier's own text
    # and the module's attribution, through every route the collector follows. These are MESSAGE
    # cells on purpose: before the scope existed the marker itself was undeclared config, so every
    # scoped fixture already refused (`option `__reservedKeys' does not exist`) and a `tryEval` cell
    # could not tell the door from its absence. Each cell first forces its LIVE CONTROL, the same
    # route writing the unreserved `j`, which must read 1. The compose half, with the marked
    # module's own level and the first-occurrence rule, is `ci/tests/reserved-keys.nix`.
    flake.testsError.reserved-keys =
      let
        int0 = gm.mkOption {
          type = t.int;
          default = 0;
        };
        decl.options = {
          k = int0;
          j = int0;
        };
        res.names.k = "RESERVED-k";
        scopedBy = r: child: {
          _file = "/fx/entry.nix";
          __reservedKeys = r;
          imports = [ child ];
        };
        read =
          r: child:
          cfg {
            modules = [
              decl
              (scopedBy r child)
            ];
          };
        # route: (name -> module writing that name at its top level)
        refuses =
          route: withControl (read res (route "j")).j 1 (builtins.deepSeq (read res (route "k")).k null);
        owner = file: {
          type = "ThrownError";
          msg = "^RESERVED-k \\(module `${file}'\\)$";
        };
        malformedMsg = what: {
          type = "ThrownError";
          msg = "^gen-merge: module `/fx/entry\\.nix' is imported under a malformed `__reservedKeys': ${what}\\. The key is .*$";
        };
        malformed = r: builtins.deepSeq (read r { j = 1; }).j null;
      in
      {
        test-imports-route-refused-with-owner-text = {
          expr = refuses (n: {
            ${n} = 1;
          });
          expectedError = owner "/fx/entry\\.nix";
        };
        test-nested-imports-route-refused = {
          expr = refuses (n: {
            imports = [ { ${n} = 1; } ];
          });
          expectedError = owner "/fx/entry\\.nix";
        };
        test-function-module-route-refused-after-application = {
          expr = refuses (n: { ... }: { ${n} = 1; });
          expectedError = owner "/fx/entry\\.nix";
        };
        test-functor-module-route-refused-after-application = {
          expr = refuses (n: {
            __functor = _: _: { ${n} = 1; };
          });
          expectedError = owner "/fx/entry\\.nix";
        };
        test-let-built-imports-list-refused = {
          expr = refuses (
            n:
            let
              xs = [ { ${n} = 1; } ];
            in
            {
              imports = xs;
            }
          );
          expectedError = owner "/fx/entry\\.nix";
        };
        test-whole-module-mkif-refused-after-push-down = {
          expr = refuses (n: gm.mkIf true { ${n} = 1; });
          expectedError = owner "/fx/entry\\.nix";
        };
        test-whole-module-mkmerge-refused-after-push-down = {
          expr = refuses (n: gm.mkMerge [ { ${n} = 1; } ]);
          expectedError = owner "/fx/entry\\.nix";
        };
        test-require-route-refused = {
          expr = refuses (n: {
            require = [ { ${n} = 1; } ];
          });
          expectedError = owner "/fx/entry\\.nix";
        };
        # A path module is named by its path. Its control is an inline `j` write through the same
        # scope (a second fixture file would carry nothing the inline one does not).
        test-path-module-route-refused-naming-the-file = {
          expr = withControl (read res { j = 1; }).j 1 (
            builtins.deepSeq (read res ./tests/_fixtures/reserved-k.nix).k null
          );
          expectedError = owner "/[^']*/_fixtures/reserved-k\\.nix";
        };
        # The clause sits BEFORE the structured-surplus clause: a structured module carrying a
        # reserved name gets the owner's text, not the generic "move it into `config'" remedy. Its
        # control writes `j` through the structured module's own `config`, since a top-level `j`
        # beside `options` is the surplus refusal itself.
        test-structured-module-gets-owner-text-not-surplus-remedy = {
          expr =
            withControl
              (read res {
                options.other = int0;
                config.j = 1;
              }).j
              1
              (
                builtins.deepSeq
                  (read res {
                    options.other = int0;
                    k = 1;
                  }).k
                  null
              );
          expectedError = owner "/fx/entry\\.nix";
        };
        # A scoped module function whose result is not an attribute set keeps the reader's own
        # named refusal: the scope reads an attrset's keys only, so it never turns that refusal into
        # an uncatchable `attrNames` abort.
        test-scoped-function-result-not-a-module-keeps-its-refusal = {
          expr =
            withControl
              (read res (_: {
                j = 1;
              })).j
              1
              (builtins.deepSeq (read res (_: readerSelfFn)).k null);
          expectedError = {
            type = "ThrownError";
            msg = fnResultMsg "/fx/entry\\.nix" "lambda";
          };
        };
        # A MALFORMED MARKER IS REFUSED BY NAME, one cell per shape. Each once aborted uncatchably
        # (a string marker; a non-string text) or read as an empty reservation (`names` a list).
        test-malformed-marker-string-refused-by-name = {
          expr = malformed "k";
          expectedError = malformedMsg "it is a string";
        };
        test-malformed-marker-non-string-text-refused-by-name = {
          expr = malformed { names.k = 5; };
          expectedError = malformedMsg "its `names\\.k' is not a refusal text";
        };
        test-malformed-marker-names-list-refused-by-name = {
          expr = malformed { names = [ "k" ]; };
          expectedError = malformedMsg "its `names' is a list";
        };
      };

    # THE KEY COMPARISON (`__keyEq`, den-hoag-kind-generator-collision-d4gnx): each refusal by name.
    # Each cell first forces its LIVE CONTROL, an equal pair under the same key, which must read one
    # module. The compose half and the catchability of every arm is `ci/tests/key-eq.nix`.
    flake.testsError.key-eq =
      let
        decl.options.l = gm.mkOption {
          type = t.listOf t.str;
          default = [ ];
        };
        withEq = decide: file: v: {
          _file = file;
          key = "K";
          __keyEq = {
            subject = v;
            inherit decide;
          };
          l = [ v ];
        };
        eq = withEq (a: b: a == b);
        plain = file: v: {
          _file = file;
          key = "K";
          l = [ v ];
        };
        l = mods: (cfg { modules = [ decl ] ++ mods; }).l;
        controlled =
          mods:
          withControl (l [
            (eq "/fx/a.nix" "x")
            (eq "/fx/b.nix" "x")
          ]) [ "x" ] (builtins.deepSeq (l mods) null);
        unequal = {
          type = "ThrownError";
          msg = "^gen-merge: modules `/fx/a\\.nix' and `/fx/b\\.nix' share the key 'K' and are not equal under its key comparison \\(`__keyEq'\\)\\. One key is one declaration: .*$";
        };
        onlyOne = file: {
          type = "ThrownError";
          msg = "^gen-merge: modules `/fx/a\\.nix' and `/fx/b\\.nix' share the key 'K', and only `${file}' publishes a key comparison \\(`__keyEq'\\)\\. .*$";
        };
      in
      {
        test-unequal-pair-refused-by-name = {
          expr = controlled [
            (eq "/fx/a.nix" "x")
            (eq "/fx/b.nix" "y")
          ];
          expectedError = unequal;
        };
        test-unequal-pair-other-order-refused-by-name = {
          expr = controlled [
            (eq "/fx/a.nix" "y")
            (eq "/fx/b.nix" "x")
          ];
          expectedError = unequal;
        };
        # Only one publishing refuses in both orders (ADR-0022), naming the one that publishes.
        test-kept-publishes-dropped-does-not-refused-by-name = {
          expr = controlled [
            (eq "/fx/a.nix" "x")
            (plain "/fx/b.nix" "y")
          ];
          expectedError = onlyOne "/fx/a\\.nix";
        };
        test-dropped-publishes-kept-does-not-refused-by-name = {
          expr = controlled [
            (plain "/fx/a.nix" "y")
            (eq "/fx/b.nix" "x")
          ];
          expectedError = onlyOne "/fx/b\\.nix";
        };
        # A non-boolean answer is refused by name, catchably, where it once aborted on `if`.
        test-non-boolean-decide-refused-by-name = {
          expr = controlled [
            (withEq (_: _: "yes") "/fx/a.nix" "x")
            (withEq (_: _: "yes") "/fx/b.nix" "x")
          ];
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: the key comparison \\(`__keyEq\\.decide'\\) of key 'K' returned string, not a boolean\\. .*$";
          };
        };
        # `decide`'s own refusal propagates unchanged: the publisher names its own difference.
        test-decide-own-refusal-propagates = {
          expr = controlled [
            (withEq (_: _: throw "DECIDE-OWN") "/fx/a.nix" "x")
            (withEq (_: _: throw "DECIDE-OWN") "/fx/b.nix" "x")
          ];
          expectedError = {
            type = "ThrownError";
            msg = "^DECIDE-OWN$";
          };
        };
        # `__keyEq` on a module with no `key` has nothing to decide: refused by name, where it would
        # otherwise be stripped as a module key and silently ignored.
        test-keyless-publisher-refused-by-name = {
          expr = controlled [
            {
              _file = "/fx/c.nix";
              __keyEq = {
                subject = 1;
                decide = _: _: true;
              };
              l = [ "z" ];
            }
          ];
          expectedError = {
            type = "ThrownError";
            msg = "^gen-merge: module `/fx/c\\.nix' publishes a key comparison \\(`__keyEq'\\) but no `key'\\. .*$";
          };
        };
      };

    # Which declaration's added check a type merge drops, named (`mergeTypesReason`'s drop arm,
    # lib/modules.nix), and the same reason riding a container's refusal one level down (`elementRel`,
    # lib/types.nix). `ci/tests/check-family-merge.nix` pins that each pair refuses and that one shared
    # wrapped value declared twice does not.
    flake.testsError.dropped-wrapper-check =
      let
        wi = nixpkgsLib.types.addCheck t.int (x: x > 0);
        wi2 = nixpkgsLib.types.addCheck t.int (x: x > 0);
        u = t.union [ t.int ];
        wu = nixpkgsLib.types.addCheck u (x: x > 0);
        declaredTwice =
          a: b:
          realize {
            modules = [
              { options.x = gm.mkOption { type = a; }; }
              { options.x = gm.mkOption { type = b; }; }
            ];
          };
        refuses = pair: {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(${pair}\\); declared in <gen-merge>, <gen-merge>$";
        };
        drops = whose: "which merge to `int', a type that drops the `check' a wrapper added to ${whose}";
      in
      {
        # The leaf pair is named deciding (later) type first, so a later wrapper is "the first".
        test-a-later-wrappers-check-is-named = {
          expr = declaredTwice t.int wi;
          expectedError = refuses "`int' and `int', ${drops "the first"}";
        };
        test-an-earlier-wrappers-check-is-named = {
          expr = declaredTwice wi t.int;
          expectedError = refuses "`int' and `int', ${drops "the second"}";
        };
        test-two-wrappers-name-both-checks = {
          expr = declaredTwice wi wi2;
          expectedError = refuses "`int' and `int', ${drops "both"}";
        };
        test-a-parametric-wrapper-is-named = {
          expr = declaredTwice u wu;
          expectedError = refuses "`union<int>' and `union<int>', which merge to `union<int>', a type that drops the `check' a wrapper added to the first";
        };
        # Inside a container the earlier operand's relation asks first (`declaredPair`'s veto), so the
        # element pair reads earlier first and the later wrapper is "the second".
        test-a-container-names-the-cause-at-depth = {
          expr = declaredTwice (t.listOf t.int) (t.listOf wi);
          expectedError = refuses "`listOf' over `int' and `listOf' over `int', whose element types do not merge: `int' and `int', ${drops "the second"}";
        };
      };

    # A NIXPKGS SUBMODULE'S `nestedTypes` IS NEVER FORCED WHERE NIXPKGS WOULD NOT FORCE IT
    # (den-hoag-a0c4z; `../tests/submodule-laziness.nix` holds the values). The recogniser is for
    # laziness only, so what it does not admit keeps its carrying spelling read: the same poison on
    # a `listOf`/`attrsOf` fires, and a hand-built container whose payload states `modules` beside a
    # static gen nesting element, stating no `getSubModules`, keeps both ruled refusals (n6dh7
    # OQ11 (d)'s nesting-element refusal, and the witness's dropped check). Each has its
    # `staticModules` twin, which refuses alike. The undeclared control refuses naming the full path
    # as nixpkgs does, from the joined evaluation rather than one operand's.
    flake.testsError.submodule-laziness =
      let
        lib = nixpkgsLib;
        np = lib.types;
        int = lib.mkOption { type = np.int; };
        poisonMsg = "submodule-laziness: nestedTypes forced e975a05c0a";
        poison = ty: ty // { nestedTypes = throw poisonMsg; };
        fired = {
          type = "ThrownError";
          msg = "^${poisonMsg}$";
        };
        at = modules: builtins.deepSeq (cfg { inherit modules; }).s null;
        fakeList =
          elem: payload:
          lib.mkOptionType {
            name = "fakeList";
            check = builtins.isList;
            merge = _loc: defs: lib.concatMap (d: d.value) defs;
            nestedTypes.elemType = elem;
            functor = np.defaultFunctor "fakeList" // {
              inherit payload;
              binOp = a: _b: a;
              type = _p: fakeList elem payload;
            };
          };
        nesting = payload: [
          {
            options.s = lib.mkOption {
              type = fakeList (t.submodule { options.y = int; }) payload;
              default = [ ];
            };
          }
          { s = [ { y = 2; } ]; }
        ];
        redeclared = payload: [
          {
            options.s = lib.mkOption {
              type = fakeList np.port payload;
              default = [ ];
            };
          }
          { options.s = lib.mkOption { type = fakeList np.int payload; }; }
          { s = [ 70000 ]; }
        ];
        nestingRefusal = {
          type = "ThrownError";
          msg = "^gen-merge: `evalModuleTree' at option `s': the option type `fakeList' declares a gen nesting type as an element \\(its `nestedTypes\\.elemType'\\), and it cannot thread the evaluation to that nested tree here\\..*$";
        };
        droppedCheck = {
          type = "ThrownError";
          msg = "^gen-merge: option `s' is declared with types that do not merge \\(`fakeList' and `fakeList', which their own relation joins to `fakeList', a type that states the check `fakeList' declares but not the check `fakeList' declares\\); declared in <gen-merge>, <gen-merge>$";
        };
      in
      {
        test-a-poisoned-listOf-is-read = {
          expr = at [
            {
              options.s = lib.mkOption {
                type = poison (np.listOf np.int);
                default = [ ];
              };
            }
            { s = [ 1 ]; }
          ];
          expectedError = fired;
        };
        test-a-poisoned-listOf-redeclared-is-read = {
          expr = at [
            {
              options.s = lib.mkOption {
                type = poison (np.listOf np.int);
                default = [ ];
              };
            }
            { options.s = lib.mkOption { type = poison (np.listOf np.int); }; }
            { s = [ 1 ]; }
          ];
          expectedError = fired;
        };
        test-a-poisoned-attrsOf-is-read = {
          expr = at [
            {
              options.s = lib.mkOption {
                type = poison (np.attrsOf np.int);
                default = { };
              };
            }
            { s.k = 1; }
          ];
          expectedError = fired;
        };
        test-a-payload-stating-modules-keeps-the-nesting-element-refusal = {
          expr = at (nesting {
            modules = [ ];
          });
          expectedError = nestingRefusal;
        };
        test-a-payload-stating-static-modules-keeps-the-nesting-element-refusal = {
          expr = at (nesting {
            staticModules = [ ];
          });
          expectedError = nestingRefusal;
        };
        test-a-payload-stating-modules-keeps-the-dropped-check-refusal = {
          expr = at (redeclared {
            modules = [ ];
          });
          expectedError = droppedCheck;
        };
        test-a-payload-stating-static-modules-keeps-the-dropped-check-refusal = {
          expr = at (redeclared {
            staticModules = [ ];
          });
          expectedError = droppedCheck;
        };
        test-an-undeclared-key-names-the-joined-path = {
          expr = at [
            {
              options.s = lib.mkOption {
                type = np.submodule { config.y = 2; };
                default = { };
              };
            }
            { options.s = lib.mkOption { type = np.submodule { options.x = int; }; }; }
          ];
          expectedError = {
            type = "ThrownError";
            msg = "^The option `s\\.y' does not exist\\. Definition values:\n- In `<unknown-file>': 2\n\nDid you mean `s\\.x'\\?$";
          };
        };
      };

    # `deriveType`'s refusals (den-hoag-5kic), each by name: a base that is not a completed option
    # type, a delta reaching past metadata, no `id`, a `key` Nix `==` cannot decide, and a demand for
    # the identity of a sealed derivation. The two declaration cells read a relation's own reason
    # through the declaration plane; `ci/tests/derive-type.nix` holds the refusals as values.
    flake.testsError.derive-type =
      let
        tagged.id = "tagged";
        derive = gm.deriveType;
        declared =
          a: b:
          realize {
            modules = [
              { options.o = gm.mkOption { type = a; }; }
              { options.o = gm.mkOption { type = b; }; }
              { o = "a"; }
            ];
          };
        refusal = msg: {
          type = "ThrownError";
          inherit msg;
        };
      in
      {
        test-a-constructor-is-not-a-base = {
          expr = force (derive t.listOf tagged);
          expectedError = refusal "^gen-merge: `deriveType' over `<not a type>': the base is a function, not a type \\(a type constructor must be applied\\)$";
        };
        test-an-uncompleted-record-is-not-a-base = {
          expr = force (derive (genMergeVocab.mkType { name = "m"; }) tagged);
          expectedError = refusal "^gen-merge: `deriveType' over `m': the base has not been completed \\(it states no foreign protocol; build it through `defineType' first\\)$";
        };
        test-an-option-descriptor-is-not-a-base = {
          expr = force (derive (gm.mkOption { type = t.str; }) tagged);
          expectedError = refusal "^gen-merge: `deriveType' over `<unnamed>': the base is a tagged `option' value, not a type$";
        };
        test-a-delta-past-metadata-is-refused = {
          expr = force (
            derive t.str (
              tagged
              // {
                fields = _: {
                  mergeDefs = null;
                  check = null;
                };
              }
            )
          );
          expectedError = refusal "^gen-merge: `deriveType' over `string' as `tagged': `fields' sets `check', `mergeDefs', which are not metadata; a type whose behaviour or relation differs is a new type \\(`mkOptionType'\\), not a derivation$";
        };
        test-a-derivation-without-an-id-is-refused = {
          expr = force (derive t.str { });
          expectedError = refusal "^gen-merge: `deriveType' over `string' states no string `id'; a derivation's merge identity is the string it names$";
        };
        test-a-key-holding-a-type-is-refused = {
          expr = force (derive t.str (tagged // { key.inner = [ t.int ]; }));
          expectedError = refusal "^gen-merge: `deriveType' over `string' as `tagged': its `key' holds an option type, which Nix `==' cannot compare totally; key a derivation by plain data$";
        };
        test-a-sealed-derivation-answers-no-identity = {
          expr = force (derive t.str tagged).__id;
          expectedError = refusal "^gen-merge: the derivation `tagged' of `string' is sealed: it states no minted identity, so it has none to answer with \\(pass `mint' to `deriveType'\\)$";
        };
        test-a-derivation-declared-beside-its-base-names-the-pair = {
          expr = declared (derive t.str tagged) t.str;
          expectedError = refusal "^gen-merge: option `o' is declared with types that do not merge \\(the derivation `tagged' of `string' and `string'\\); declared in <gen-merge>, <gen-merge>$";
        };
        test-two-derivations-whose-keys-differ-name-the-keys = {
          expr = declared (derive t.str (tagged // { key = 1; })) (derive t.str (tagged // { key = 2; }));
          expectedError = refusal "^gen-merge: option `o' is declared with types that do not merge \\(the derivation `tagged' of `string' and the derivation `tagged' of `string', whose keys differ\\); declared in <gen-merge>, <gen-merge>$";
        };
        # A foreign container crosses the import boundary with no constructor to rebuild it over, and
        # the vocabulary refuses it by name (the inherited round-trip residue, den-hoag-un50q).
        test-a-foreign-container-base-is-refused-by-the-vocabulary = {
          expr = force (derive (nixpkgsLib.types.listOf t.str) tagged).name;
          expectedError = refusal "^gen-merge: the structural type `listOf' carries a parameter but does not supply `recarry'; a type that carries something answers for it rather than inheriting a leaf's answers$";
        };
        # LIVE CONTROL, same run: the same declaration of one derivation twice evaluates.
        test-control-one-derivation-declared-twice-evaluates = {
          expr =
            let
              d = derive t.str tagged;
            in
            (gm.evalModuleTree {
              modules = [
                { options.o = gm.mkOption { type = d; }; }
                { options.o = gm.mkOption { type = d; }; }
                { o = "a"; }
              ];
            }).config.o;
          expected = "a";
        };
      };
  };
}
