# The THREADED half of nested trees as `nta` children (den-hoag-n6dh7 Unit 2.2, spec
# `2026-09-22-gen-scope-nta-spec.md` v9): each fold's `threaded` sibling, the export bridge, the
# homing of a type bound to a position, and the import refusal with its stated price.
#
# Until the switch (Unit 2.4) the engine still folds by the CALLED fold, and the accessor a
# `threaded` fold reads is the BRIDGE: one root evaluation per nested tree. So threaded ≡ called,
# byte for byte, is a cell here (U2.2-a), and every value below is today's except where a ruling
# moves it (U2-i's stated price, OQ11 (d)'s refusals, S2's opt-out). `ci/tests-error.nix`'s
# `nesting-threaded` suite pins the refusals' text.
{
  evalRequest,
  genMerge,
  genMergeCore,
  interface,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib.types;
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;

  sub = t.submodule { options.x = gm.mkOption { type = t.int; }; };
  # A tree whose value reads its `name` and a caller's argument, so a moved `loc` or a dropped
  # argument shows in the value.
  named = t.submodule (
    { name, ... }:
    {
      options.x = gm.mkOption {
        type = t.int;
        default = 0;
      };
      options.n = gm.mkOption {
        type = t.str;
        default = name;
      };
    }
  );
  withArgs =
    (t.submodule (
      { name, tag, ... }:
      {
        options.v = gm.mkOption {
          type = t.str;
          default = "${tag}-${name}";
        };
      }
    )).withArgs
      { tag = "w"; };
  # The tree record, lax, and its called mode `{ false; false; }`.
  tree =
    (gm.evalModuleTree { check = false; } [ { options.x = gm.mkOption { type = t.int; }; } ]).type;
  cfg = mods: (gm.evalModuleTree { } mods).config;
  opt =
    type: def:
    (cfg [
      {
        options.h = gm.mkOption { inherit type; };
        config.h = def;
      }
    ]).h;
  fwd =
    type: def:
    (nixpkgsLib.evalModules {
      modules = [
        { options.h = nixpkgsLib.mkOption { inherit type; }; }
        { config.h = def; }
      ];
    }).config.h;
  defsOf = map (v: {
    file = "/f";
    value = v;
  });

  # U2.2-a's fixtures: every nesting shape gen-merge's suites fold, each as `{ type; loc; defs; }`.
  fixtures = {
    sub = {
      type = named;
      loc = [
        "h"
        "a"
      ];
      defs = defsOf [ { x = 1; } ];
    };
    sub-two-defs = {
      type = named;
      loc = [ "s" ];
      defs = defsOf [
        { x = 1; }
        { n = "set"; }
      ];
    };
    sub-at-root = {
      type = named;
      loc = [ ];
      defs = defsOf [ { x = 2; } ];
    };
    sub-with-args = {
      type = withArgs;
      loc = [ "k" ];
      defs = defsOf [ { } ];
    };
    attrs = {
      type = t.attrsOf named;
      loc = [ "h" ];
      defs = defsOf [
        {
          a.x = 1;
          b.x = 2;
        }
        { c = gm.mkIf false { x = 3; }; }
      ];
    };
    lazy-attrs = {
      type = t.lazyAttrsOf named;
      loc = [ "h" ];
      defs = defsOf [
        { a.x = 1; }
        { b = { }; }
      ];
    };
    list-two-defs = {
      type = t.listOf named;
      loc = [ "l" ];
      defs = defsOf [
        [ { x = 1; } ]
        [ { x = 2; } ]
      ];
    };
    list-dropped = {
      type = t.listOf named;
      loc = [ "l" ];
      defs = defsOf [
        [
          (gm.mkIf false { x = 0; })
          { x = 1; }
        ]
      ];
    };
    null-or = {
      type = t.nullOr named;
      loc = [ "o" ];
      defs = defsOf [ { x = 5; } ];
    };
    null-or-null = {
      type = t.nullOr named;
      loc = [ "o" ];
      defs = defsOf [ null ];
    };
    either-member = {
      type = t.either t.str named;
      loc = [ "e" ];
      defs = defsOf [ { x = 6; } ];
    };
    either-str = {
      type = t.either t.str named;
      loc = [ "e" ];
      defs = defsOf [ "s" ];
    };
    one-of = {
      type = t.oneOf [
        t.int
        t.str
        named
      ];
      loc = [ "e" ];
      defs = defsOf [ { x = 7; } ];
    };
    nested = {
      type = t.attrsOf (t.listOf named);
      loc = [ "h" ];
      defs = defsOf [ { a = [ { x = 1; } ]; } ];
    };
    tree = {
      type = tree;
      loc = [ "t" ];
      defs = defsOf [ { x = 1; } ];
    };
  };
  threadedOf = f: f.type.mergeDefs.threaded interface.bridge f.loc f.defs;
  calledOf = f: f.type.mergeDefs f.loc f.defs;

  # The accessor a REPORTING site reads the tree record through: the bridge's door, in the reported
  # mode of a lax carrier (`{ true; false; }`, what the rich fold's `.reported false` evaluates in).
  reportedEv = {
    position = [ ];
    containerNodes = false;
    child = genMergeCore.nestedTreeAt {
      carried = true;
      inherited = false;
    };
  };
  bogusDefs = defsOf [
    {
      x = 1;
      bogus = 2;
    }
  ];
  paths = r: r // { undeclared = map (u: u.path) r.undeclared; };

  # nixpkgs' `types.json` shape: self-referential under three recognised containers.
  valueType = np.nullOr (
    np.oneOf [
      np.str
      (np.attrsOf valueType)
      (np.listOf valueType)
    ]
  );
  # gen-schema's `refined`, as a record copy through `mkOptionType` (the RECORD-COPY class).
  refinedLike =
    b:
    gm.mkOptionType (
      removeAttrs b [
        "functor"
        "typeMerge"
      ]
      // {
        name = "refined";
      }
    );
  forwarding = gm.mkOptionType {
    name = "fwd";
    merge = loc: defs: sub.merge loc defs;
  };
in
{
  # U2.2-a: through the bridge, each nesting shape's `threaded` fold gives its called fold's value
  # byte for byte, over the fixtures above. The called fold refuses since the switch (Unit 2.4, item
  # 1), so its values are pinned as the literals it gave at the switch's parent (gen-merge 193a18d),
  # with a list element's name since taken as nixpkgs `listOf` names it, `[definition n-entry m]`.
  flake.tests.nesting-threaded-bridge = {
    test-threaded-through-the-bridge-is-the-called-fold = {
      expr = builtins.mapAttrs (_: threadedOf) fixtures;
      expected = {
        attrs = {
          a = {
            n = "a";
            x = 1;
          };
          b = {
            n = "b";
            x = 2;
          };
        };
        either-member = {
          n = "e";
          x = 6;
        };
        either-str = "s";
        lazy-attrs = {
          a = {
            n = "a";
            x = 1;
          };
          b = {
            n = "b";
            x = 0;
          };
        };
        list-dropped = [
          {
            n = "[definition 1-entry 2]";
            x = 1;
          }
        ];
        list-two-defs = [
          {
            n = "[definition 1-entry 1]";
            x = 1;
          }
          {
            n = "[definition 2-entry 1]";
            x = 2;
          }
        ];
        nested = {
          a = [
            {
              n = "[definition 1-entry 1]";
              x = 1;
            }
          ];
        };
        null-or = {
          n = "o";
          x = 5;
        };
        null-or-null = null;
        one-of = {
          n = "e";
          x = 7;
        };
        sub = {
          n = "a";
          x = 1;
        };
        sub-at-root = {
          n = "";
          x = 2;
        };
        sub-two-defs = {
          n = "set";
          x = 1;
        };
        sub-with-args = {
          v = "w-k";
        };
        tree = {
          x = 1;
        };
      };
    };
    # The fixtures reach every constructor that nests, and each reads the name nixpkgs gives it: a
    # list element reads nixpkgs `listOf`'s `[definition n-entry m]`, `n` the definition's ordinal
    # and `m` its index within that definition, taken before the drop.
    test-the-fixtures-read-their-loc = {
      expr = {
        sub = (threadedOf fixtures.sub).n;
        root = (threadedOf fixtures.sub-at-root).n;
        args = (threadedOf fixtures.sub-with-args).v;
        list = map (e: e.n) (threadedOf fixtures.list-two-defs);
        dropped = map (e: e.n) (threadedOf fixtures.list-dropped);
        attrs = builtins.attrNames (threadedOf fixtures.attrs);
      };
      expected = {
        sub = "a";
        root = "";
        args = "w-k";
        list = [
          "[definition 1-entry 1]"
          "[definition 2-entry 1]"
        ];
        dropped = [ "[definition 1-entry 2]" ];
        attrs = [
          "a"
          "b"
        ];
      };
    };
    # The tree record refuses a finding through the bridge exactly where its called form does.
    test-a-tree-finding-is-refused-through-the-bridge-as-called = {
      expr = {
        threaded = refused (tree.mergeDefs.threaded interface.bridge [ "t" ] bogusDefs);
        called = refused (tree.mergeDefs [ "t" ] bogusDefs);
      };
      expected = {
        threaded = true;
        called = true;
      };
    };
  };

  # Which folds carry the sibling, and what each nesting type states about its tree's `name`.
  flake.tests.nesting-threaded-siblings = {
    test-every-nesting-and-container-fold-carries-threaded = {
      expr = builtins.mapAttrs (_: ty: ty ? mergeDefs.threaded) {
        inherit sub tree;
        listOf = t.listOf t.str;
        attrsOf = t.attrsOf t.str;
        lazyAttrsOf = t.lazyAttrsOf t.str;
        nullOr = t.nullOr t.str;
        either = t.either t.str t.int;
        str = t.str;
      };
      expected = {
        sub = true;
        tree = true;
        listOf = true;
        attrsOf = true;
        lazyAttrsOf = true;
        nullOr = true;
        either = true;
        str = false;
      };
    };
    test-only-the-tree-record-carries-threaded-reported = {
      expr = {
        tree = tree ? mergeDefs.threadedReported;
        sub = sub ? mergeDefs.threadedReported;
      };
      expected = {
        tree = true;
        sub = false;
      };
    };
    # The name is the engine's, not a nesting type's: no nesting type states a `name` channel, and
    # the placeholder every nested tree over no definitions reads is nixpkgs' `mkOptionDefault "‹name›"`.
    test-the-name-is-the-engines-not-a-nesting-types = {
      expr = {
        typeStates = builtins.filter (k: sub.nests ? ${k} || tree.nests ? ${k}) [
          "named"
          "namesByModule"
        ];
        placeholder = {
          inherit (genMergeCore.namePlaceholder._module.args.name) _type priority content;
        };
      };
      expected = {
        typeStates = [ ];
        placeholder = {
          _type = "override";
          priority = 1500;
          content = "‹name›";
        };
      };
    };
  };

  # U2-o: the report mode is the site's. The three sites' answers, unchanged, and the tree record's
  # two fold forms through `threaded` as through their twins.
  flake.tests.nesting-threaded-mode = {
    test-the-three-sites-answer-as-today = {
      expr =
        let
          rep =
            check: type: def:
            let
              r = gm.evalModuleTree { check = check; } [
                {
                  options.t = gm.mkOption { inherit type; };
                  config.t = def;
                }
              ];
            in
            {
              inherit (r.config) t;
              undeclared = map (u: u.path) r.undeclared;
            };
          bogus = {
            x = 1;
            bogus = 2;
          };
        in
        {
          mode-carried = rep false tree bogus;
          mode-element = refused (rep false (t.attrsOf tree) { a = bogus; });
          mode-inherited = refused (rep true tree bogus).t;
        };
      expected = {
        mode-carried = {
          t.x = 1;
          undeclared = [
            [
              "t"
              "bogus"
            ]
          ];
        };
        mode-element = true;
        mode-inherited = true;
      };
    };
    test-the-tree-record-reports-through-threaded-as-through-reported = {
      expr = {
        threaded = paths (tree.mergeDefs.threadedReported reportedEv false [ ] bogusDefs);
        # The called `.reported` refuses since the switch (Unit 2.4, item 1); its value at the
        # switch's parent was `threaded`'s, below.
        reported = refused (tree.mergeDefs.reported false [ ] bogusDefs);
        called = refused (tree.mergeDefs.threaded interface.bridge [ ] bogusDefs);
      };
      expected = {
        threaded = {
          value.x = 1;
          undeclared = [ [ "bogus" ] ];
        };
        reported = true;
        called = true;
      };
    };
  };

  # U2-i and importType's re-homing: a stock foreign container over a gen nesting type is folded as
  # gen's own, where it is bound to its position and where it crosses whole.
  flake.tests.nesting-threaded-rehome = {
    test-a-recognised-foreign-container-folds-as-gen-s-own = {
      expr = {
        np-attrs = opt (np.attrsOf sub) {
          a.x = 1;
          b.x = 2;
        };
        # nixpkgs' `types.json` shape is recognised all the way down and keeps its value.
        np-json = opt valueType {
          a = [
            "x"
            { b = null; }
          ];
        };
      };
      expected = {
        np-attrs = {
          a.x = 1;
          b.x = 2;
        };
        np-json = {
          a = [
            "x"
            { b = null; }
          ];
        };
      };
    };
    # ★ THE STATED PRICE, asserted as the value it produces (owner, 2026-09-25, den-hoag-n6dh7): a
    # stock container whose `merge` was overridden is re-homed silently and loses the override. A
    # build that detected overrides would red this cell and send the price back to the owner. Over
    # no nesting element nothing is re-homed, so there the override stands (*defaulted, reversible*).
    test-a-re-homed-container-loses-its-override = {
      expr = {
        np-attrs-override = opt (np.attrsOf sub // { merge = _: _: "overridden"; }) { a.x = 1; };
        flat-override = opt (np.attrsOf np.int // { merge = _: _: "overridden"; }) { a = 1; };
      };
      expected = {
        np-attrs-override.a.x = 1;
        flat-override = "overridden";
      };
    };
    test-a-record-crossing-whole-is-re-homed-where-it-may-nest = {
      expr =
        let
          nesting = gm.mkOptionType (np.attrsOf sub);
          flat = gm.mkOptionType (np.attrsOf np.int);
        in
        {
          nesting = {
            inherit (nesting) name;
            gen = nesting ? split;
            value = opt nesting { a.x = 1; };
          };
          flat = flat ? split;
        };
      expected = {
        nesting = {
          name = "attrsOf";
          gen = true;
          value.a.x = 1;
        };
        flat = false;
      };
    };
    # An unrecognised declaring container threads through its own `substSubModules` rebuild
    # (den-hoag-f8mgj arm (T)) and gives nixpkgs' value; `coercedTo` keeps its `coerceFunc`, and a
    # stock `unique` over the bare tree is decided stock and served. `ci/tests-error.nix` pins the
    # refusals that remain.
    test-an-unrecognised-declaring-container-threads = {
      expr = {
        placeholder = opt (np.attrsWith {
          elemType = sub;
          placeholder = "host";
        }) { a.x = 1; };
        coerced = opt (np.coercedTo np.int (x: { inherit x; }) sub) 7;
        uniq-tree = opt (np.uniq tree) { x = 1; };
        attr-list = opt (np.attrListOf sub) { a.x = 1; };
        # A hand-rolled container whose rebuild forwards its argument, as nixpkgs' own do (F2 α: one
        # that drops it is refused by name, `ci/tests-error.nix`).
        forwards =
          let
            fwdT =
              elem:
              nixpkgsLib.mkOptionType {
                name = "fwd";
                check = _: true;
                merge = loc: defs: elem.merge loc defs;
                nestedTypes.elemType = elem;
                inherit (elem) getSubOptions getSubModules;
                substSubModules = m: fwdT (elem.substSubModules m);
              };
          in
          opt (fwdT sub) { x = 1; };
        # `functionTo` folds its element inside the function it returns; a member that reads no
        # tree there still answers (a tree read is refused by name, `ci/tests-error.nix`).
        function-body-string = (opt (np.functionTo (t.either tree t.str)) (_: "s")) null;
      };
      expected = {
        placeholder.a.x = 1;
        coerced.x = 7;
        uniq-tree.x = 1;
        attr-list = [ { a.x = 1; } ];
        forwards.x = 1;
        function-body-string = "s";
      };
    };
  };

  # U2-n: the bridge keeps the forward mount working, the import refusal fires at construction, and
  # the stated price is visible as a value.
  flake.tests.nesting-threaded-export = {
    test-the-forward-mount-keeps-working-through-the-bridge = {
      expr = {
        fwd-ctl = fwd t.int 6;
        fwd-sub = fwd sub { x = 4; };
        fwd-attrs = fwd (t.attrsOf sub) {
          a.x = 1;
          b.x = 2;
        };
        fwd-list = fwd (t.listOf sub) [ { x = 1; } ];
        # The presence arm: a leaf and a `mkOptionType` fold carry no sibling and export as before.
        exp-str = fwd t.str "a";
        exp-hand = fwd (gm.mkOptionType {
          name = "h";
          merge = _loc: defs: (builtins.head defs).value;
        }) "a";
      };
      expected = {
        fwd-ctl = 6;
        fwd-sub.x = 4;
        fwd-attrs = {
          a.x = 1;
          b.x = 2;
        };
        fwd-list = [ { x = 1; } ];
        exp-str = "a";
        exp-hand = "a";
      };
    };
    test-a-declaring-hand-rolled-container-is-refused-at-construction = {
      expr =
        let
          protocol = {
            inherit (sub) getSubOptions getSubModules;
            substSubModules = _: sub;
          };
        in
        {
          decl =
            refused
              (gm.mkOptionType (
                {
                  name = "fwd";
                  merge = loc: defs: sub.merge loc defs;
                  nestedTypes.elemType = sub;
                }
                // protocol
              )).name;
          payload =
            refused
              (gm.mkOptionType (
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
              )).name;
        };
      expected = {
        decl = true;
        payload = true;
      };
    };
    # ★ THE STATED PRICE OF OQ11 (d), asserted as values: a foreign fold forwarding to a gen nesting
    # type it does not declare, and a record copy of one, evaluate their tree standalone. The copy
    # keeps `nests` and loses the sibling, so it is not a nesting type.
    test-an-undeclared-forward-is-the-stated-price = {
      expr = {
        handrolled = opt forwarding { x = 3; };
        refined-sub = opt (refinedLike sub) { x = 9; };
        refined-copies-nests = (refinedLike sub) ? nests;
        refined-is-nesting = interface.isNesting (refinedLike sub);
      };
      expected = {
        handrolled.x = 3;
        refined-sub.x = 9;
        refined-copies-nests = true;
        refined-is-nesting = false;
      };
    };
  };

  # THE FENCE MOVED, ON THE RECORD. gen's eval over nixpkgs `attrsOf (either T str)`, `T` the tree
  # type, refused before the threaded half (`tree-type`'s fence cell, reading the union's published
  # face). The decision that moves it is the spec's F2 elaboration (OQ2 RULED α: a recognised
  # nixpkgs container is re-homed at the realizer as gen's own) and OQ11 (d): the stock container is
  # gen's `attrsOf` here, and it answers what nixpkgs over its own types answers,
  # `{ k = { a = 5; }; }`. An UNRECOGNISED container now threads through its own rebuild and gives
  # the same value (`ci/tests-error.nix`, `tree-type.test-an-unrecognised-foreign-container-over-a-gen-union-…`).
  flake.tests.nesting-threaded-fence = {
    test-a-stock-foreign-container-over-a-gen-union-folds-in-gen = {
      expr =
        let
          family = import ./_fixtures/tree-union-family.nix { inherit evalRequest genMerge nixpkgsLib; };
        in
        family.gen (np.attrsOf (t.either family.T t.str)) { k.a = 5; };
      expected = {
        k.a = 5;
      };
    };
  };

  # THE STOCK SIX OVER THE BARE TREE (den-hoag-4ifgb M0). A stock nixpkgs container over the tree
  # record is re-homed as gen's own, and nixpkgs over its own types gives each value below. The
  # disagreement
  # that test exists for is still refused (`ci/tests-error.nix`, `nesting-threaded`, the tree cells).
  flake.tests.nesting-threaded-stock-six-over-tree =
    let
      strictTree =
        (gm.evalModuleTree { } [
          {
            options.a = gm.mkOption {
              type = t.int;
              default = 0;
            };
          }
        ]).type;
    in
    {
      test-the-stock-six-over-the-tree-give-values = {
        expr = {
          attrsOf = opt (np.attrsOf strictTree) { k.a = 5; };
          lazyAttrsOf = opt (np.lazyAttrsOf strictTree) { k.a = 5; };
          listOf = opt (np.listOf strictTree) [ { a = 5; } ];
          listOfEmpty = opt (np.listOf strictTree) [ ];
          nullOr = opt (np.nullOr strictTree) { a = 5; };
          either = opt (np.either strictTree np.int) { a = 5; };
          oneOf = opt (np.oneOf [
            strictTree
            np.int
          ]) { a = 5; };
        };
        expected = {
          attrsOf.k.a = 5;
          lazyAttrsOf.k.a = 5;
          listOf = [ { a = 5; } ];
          listOfEmpty = [ ];
          nullOr.a = 5;
          either.a = 5;
          oneOf.a = 5;
        };
      };
    };

  # U2-q: S2 (i) at the engine's site. An unmarked self-referential element under an unrecognised
  # container is refused at import (its text is `ci/tests-error.nix`'s); the declared opt-out takes
  # the type at its word and restores the standalone evaluation, its stated price.
  flake.tests.nesting-threaded-opt-out = {
    test-the-opt-out-restores-the-standalone-evaluation = {
      expr = {
        unmarked = refused (opt (np.uniq valueType) "x");
        marked = opt (np.uniq valueType // { declaresNesting = false; }) "x";
      };
      expected = {
        unmarked = true;
        marked = "x";
      };
    };
  };

  # 4zvc9 G1-B: a union over a foreign wrapper of a submodule under `lazyAttrsOf` gives nixpkgs'
  # value. The walk's container node is the node the fold reads: `memberChain` stops at the record
  # that states it minted one, so the fold never reads a tree with no `value`. One test per cell, so
  # an uncatchable abort errors its own cell only.
  flake.tests.nesting-threaded-union-wrapper =
    let
      npSub = np.submodule { options.x = nixpkgsLib.mkOption { type = np.int; }; };
      unions = {
        either = u: e: u.either e np.str;
        oneOf =
          u: e:
          u.oneOf [
            e
            np.str
          ];
        npEither = _: e: np.either e np.str;
      };
      wrappers = {
        uniq = _: s: np.uniq s;
        coercedTo = _: s: np.coercedTo np.str (_: throw "unused") s;
      };
      cell =
        un: wn:
        let
          lazy = T: w: T.lazyAttrsOf w;
        in
        {
          expr = opt (unions.${un} t (lazy t (wrappers.${wn} t sub))) { k.x = 5; };
          expected = fwd (unions.${un} np (lazy np (wrappers.${wn} np npSub))) { k.x = 5; };
        };
    in
    builtins.listToAttrs (
      builtins.concatMap
        (
          un:
          map
            (wn: {
              name = "test-${un}-lazy-${wn}";
              value = cell un wn;
            })
            [
              "uniq"
              "coercedTo"
            ]
        )
        [
          "either"
          "oneOf"
          "npEither"
        ]
    );

  # 4zvc9 Unit 2 (lazy position walk): a union holding a container member is keyed where it is READ.
  # Every `expected` is nixpkgs' evalModules over the same types and definitions, never a literal.
  # One test per cell, so an uncatchable abort errors its own cell only.
  flake.tests.nesting-threaded-union-lazy-walk =
    let
      npSub = np.submodule { options.x = nixpkgsLib.mkOption { type = np.int; }; };
      optDefs =
        type: defs:
        (cfg ([ { options.h = gm.mkOption { inherit type; }; } ] ++ map (d: { config.h = d; }) defs)).h;
      fwdDefs =
        type: defs:
        (nixpkgsLib.evalModules {
          modules = [
            { options.h = nixpkgsLib.mkOption { inherit type; }; }
          ]
          ++ map (d: { config.h = d; }) defs;
        }).config.h;
      # gen and nixpkgs spell the same type from one builder `T: S: …` (`T` the types, `S` the submodule)
      pair = mk: defs: read: {
        expr = read (optDefs (mk t sub) defs);
        expected = read (fwdDefs (mk np npSub) defs);
      };
      # a refusal stays catchable where nixpkgs refuses: the cell reads `tryEval`'s verdict on both
      caught = mk: defs: read: {
        expr = (builtins.tryEval (builtins.deepSeq (read (optDefs (mk t sub) defs)) true)).success;
        expected = (builtins.tryEval (builtins.deepSeq (read (fwdDefs (mk np npSub) defs)) true)).success;
      };
      forced = _: throw "4zvc9: a sibling's coercion was forced";
      unions = {
        either = T: e: T.either e np.str;
        oneOf =
          T: e:
          T.oneOf [
            e
            np.str
          ];
        npEither = _: e: np.either e np.str;
      };
      wrappers = {
        uniq = s: np.uniq s;
        coercedTo = s: np.coercedTo np.str (_: throw "unused") s;
      };
      # G1: the 90's shape — a union over a foreign wrapper of a submodule, at an option's root and as
      # an exact container's element.
      sites = {
        root = {
          ty = _: u: u;
          d = {
            x = 5;
          };
        };
        attrsOf = {
          ty = T: u: T.attrsOf u;
          d = {
            k.x = 5;
          };
        };
        listOf = {
          ty = T: u: T.listOf u;
          d = [ { x = 5; } ];
        };
      };
      g1 = builtins.listToAttrs (
        builtins.concatMap (
          un:
          builtins.concatMap (
            wn:
            map (sn: {
              name = "test-${un}-${wn}-${sn}";
              value = pair (T: S: sites.${sn}.ty T (unions.${un} T (wrappers.${wn} S))) [ sites.${sn}.d ] (v: v);
            }) (builtins.attrNames sites)
          ) (builtins.attrNames wrappers)
        ) (builtins.attrNames unions)
      );
      aw =
        S:
        np.attrsWith {
          elemType = S;
          placeholder = "p";
        };
    in
    g1
    // {
      # G2: reading one position runs no sibling's member code (gate v1 C1, v0 C1). Each reads a
      # nested sibling `b`.
      test-an-unchosen-foreign-container-never-merges-a-sibling =
        pair (T: S: T.attrsOf (T.either S (aw S)))
          [
            {
              a = "s";
              b.x = 5;
            }
          ]
          (v: v.b);
      test-an-unchosen-foreign-container-never-merges-a-sibling-int =
        pair (T: S: T.attrsOf (T.either S (aw S)))
          [
            {
              a = 5;
              b.x = 5;
            }
          ]
          (v: v.b);
      test-a-sibling-coercion-is-not-forced =
        pair (T: S: T.attrsOf (T.either (np.coercedTo np.str forced S) S))
          [
            {
              a = "hello";
              b.x = 5;
            }
          ]
          (v: v.b);
      test-a-sibling-coercion-is-not-forced-across-definitions =
        pair (T: S: T.attrsOf (T.either (np.coercedTo np.str forced S) S))
          [
            { b.x = 5; }
            { a = "hello"; }
            { b = { }; }
          ]
          (v: v.b);
      test-a-sibling-coercion-is-not-forced-second-member =
        pair (T: S: T.attrsOf (T.either S (np.coercedTo np.str forced S)))
          [
            {
              a = "hello";
              b.x = 5;
            }
          ]
          (v: v.b);
      test-a-sibling-wrapper-merge-is-not-run = pair (T: S: T.attrsOf (T.either (np.uniq S) np.str)) [
        {
          a = "s";
          b.x = 5;
        }
        { a = "s"; }
      ] (v: v.b);
      test-a-nested-union-is-keyed-where-read =
        pair (T: S: T.attrsOf (T.either (T.either (np.uniq S) np.int) np.str))
          [
            {
              a = "s";
              b.x = 5;
            }
          ]
          (v: v.b);
      # the coerce function reads a sibling through `config`: forcing it at key time is a cycle
      test-a-coercion-reading-its-sibling-is-not-a-cycle =
        let
          mods = mkOption: T: S: [
            (
              { config, ... }:
              {
                options.h = mkOption {
                  type = T.attrsOf (
                    T.either (np.coercedTo np.str (_: if config.h.b.x > 0 then { x = 1; } else { }) S) S
                  );
                };
                config.h = {
                  a = "hello";
                  b.x = 5;
                };
              }
            )
          ];
        in
        {
          expr = (cfg (mods gm.mkOption t sub)).h.b;
          expected = (nixpkgsLib.evalModules { modules = mods nixpkgsLib.mkOption np npSub; }).config.h.b;
        };
      # the read position's own choice is nixpkgs' (gate v1 prices 1 and 2: both serve)
      test-an-unchosen-wrapper-over-a-list-keeps-the-tree-member =
        pair (T: S: T.either (np.uniq (T.listOf S)) (T.either S np.str))
          [
            { x = 5; }
          ]
          (v: v);
      test-a-coerced-member-evaluates-the-coerced-definition =
        pair (T: S: T.attrsOf (T.either (np.coercedTo np.str (s: { x = builtins.stringLength s; }) S) S))
          [
            { a = "hello"; }
            { b.x = 5; }
          ]
          (v: v);
      test-a-union-over-a-list-of-coercions-serves =
        pair (T: S: T.listOf (T.either (np.coercedTo np.str (s: { x = builtins.stringLength s; }) S) S))
          [
            [
              "hello"
              { x = 5; }
            ]
          ]
          (v: v);
      # gate v1 P1: an unchosen foreign wrapper over a FOREIGN container holding a tree
      test-an-unchosen-wrapper-over-a-foreign-container-serves-a-sibling =
        pair (T: S: T.attrsOf (T.either S (np.uniq (np.attrsOf S))))
          [
            {
              a = "s";
              b.x = 5;
            }
          ]
          (v: v.b);
      test-an-unchosen-coercion-over-a-foreign-list-serves-a-sibling =
        pair (T: S: T.attrsOf (T.either (np.coercedTo np.str forced (np.listOf S)) S))
          [
            {
              a = "hello";
              b.x = 5;
            }
          ]
          (v: v.b);
      # G4: where nixpkgs refuses, the refusal is catchable (never an abort)
      test-a-read-position-outside-every-member-refuses-catchably =
        caught (T: S: T.attrsOf (T.either S (aw S)))
          [
            { b = "s"; }
          ]
          (v: v.b);
      test-a-root-outside-every-member-refuses-catchably = caught (T: S: T.either S (aw S)) [ "s" ] (
        v: v
      );
    };

  # 0hew4: the threaded channel's parity residue gives nixpkgs' value. A rebuild states its marked
  # element one container further in (`uniq (attrsOf sub)`), read at any depth; a payload-null copy
  # of a stock submodule, or one given an element it never folds, is mounted as nixpkgs'
  # `fixupOptionType` mounts it, rebuilt over its own module set. One test per cell, so an
  # uncatchable abort errors its own cell only.
  flake.tests.nesting-threaded-parity-residue =
    let
      # a payload-null copy (`mkOptionType`'s default functor) of a stock submodule, every other
      # field kept
      copy =
        s:
        nixpkgsLib.mkOptionType {
          name = "submodule";
          inherit (s)
            check
            merge
            getSubOptions
            getSubModules
            substSubModules
            nestedTypes
            emptyValue
            description
            ;
        };
      freeform = np.submodule { freeformType = np.attrsOf sub; };
      cell = type: def: {
        expr = opt type def;
        expected = fwd type def;
      };
    in
    {
      test-a-marked-element-two-containers-in-threads = cell (np.uniq (np.attrsOf sub)) { a.x = 1; };
      test-a-marked-element-under-a-coercion-threads = cell (np.coercedTo np.int (x: {
        a.x = x;
      }) (np.attrsOf sub)) 7;
      test-a-copied-submodule-is-mounted-as-fixed-up = cell (copy freeform) { k.x = 1; };
      test-a-copied-submodule-under-a-container-is-mounted-as-fixed-up = cell (np.uniq (copy freeform)) {
        k.x = 1;
      };
      test-a-submodule-given-an-unfolded-element-is-mounted-as-fixed-up = cell (
        np.submodule { options.x = gm.mkOption { type = t.int; }; } // { elemType = sub; }
      ) { x = 1; };
      # At the ROOT the record is mounted as its rebuild, not by its own merge, as nixpkgs mounts it.
      test-a-root-is-mounted-as-its-rebuild-not-its-own-merge = cell (nixpkgsLib.mkOptionType {
        name = "own";
        check = builtins.isAttrs;
        merge = _: _: "OWN-MERGE";
        getSubModules = [ ];
        substSubModules = _: np.submodule { options.x = gm.mkOption { type = t.int; }; };
        nestedTypes.elemType = sub;
      }) { x = 2; };
    };

  # den-hoag-i2xjs: a FOREIGN container (one `homedAt` threads rather than re-homes:
  # `uniq`, `unique`, `coercedTo`, `attrsWith` with a placeholder) at an EXACT container's element is
  # keyed where it is READ, so no sibling's read runs its merge. Every `expected` is nixpkgs'
  # evalModules over the same types and definitions, never a literal. One test per cell, so an
  # uncatchable abort errors its own cell only.
  flake.tests.nesting-threaded-foreign-keyed-on-read =
    let
      npSub = np.submodule { options.x = nixpkgsLib.mkOption { type = np.int; }; };
      optDefs =
        type: defs:
        (cfg ([ { options.h = gm.mkOption { inherit type; }; } ] ++ map (d: { config.h = d; }) defs)).h;
      fwdDefs =
        type: defs:
        (nixpkgsLib.evalModules {
          modules = [
            { options.h = nixpkgsLib.mkOption { inherit type; }; }
          ]
          ++ map (d: { config.h = d; }) defs;
        }).config.h;
      # gen and nixpkgs spell the same type from one builder `T: S: …` (`T` the six, `S` the submodule)
      pair = mk: defs: read: {
        expr = read (optDefs (mk t sub) defs);
        expected = read (fwdDefs (mk np npSub) defs);
      };
      # a refusal stays catchable where nixpkgs refuses: the cell reads `tryEval`'s verdict on both
      caught = mk: defs: read: {
        expr = (builtins.tryEval (builtins.deepSeq (read (optDefs (mk t sub) defs)) true)).success;
        expected = (builtins.tryEval (builtins.deepSeq (read (fwdDefs (mk np npSub) defs)) true)).success;
      };
      ctT = S: np.coercedTo np.str (_: throw "i2xjs: a sibling's coercion was forced") S;
      ctOk = S: np.coercedTo np.str (s: { x = builtins.stringLength s; }) S;
      awP =
        S:
        np.attrsWith {
          elemType = S;
          placeholder = "p";
        };
      awLP =
        S:
        np.attrsWith {
          elemType = S;
          lazy = true;
          placeholder = "p";
        };
      uq = S: np.unique { message = "m"; } S;
      # nixpkgs <= 24.05 spells `listOf`'s functor `defaultFunctor name // { wrapped = elemType; }`
      oldListOf =
        S:
        let
          l = np.listOf S;
        in
        l
        // {
          functor = l.functor // {
            payload = null;
            wrapped = S;
          };
        };
      # `attrsWith` with the default placeholder, and a payload key re-homing does not know
      awExtra =
        S:
        let
          a = np.attrsOf S;
        in
        a
        // {
          functor = a.functor // {
            payload = a.functor.payload // {
              extra = true;
            };
          };
        };
      freeform = T: S: [
        { freeformType = T.attrsOf (ctOk S); }
        { k.x = 1; }
        { n = 5; }
      ];
      ab = x: [
        {
          a = x;
          b.x = 5;
        }
      ];
      twice = [
        {
          a.x = 1;
          b.x = 5;
        }
        { a.x = 2; }
      ];
      b = v: v.b;
      a = v: v.a;
      i1 = v: builtins.elemAt v 1;
      all = v: v;
    in
    {
      # the sibling's read serves nixpkgs' value: the foreign merge at `a` is never run
      test-attrsOf-coercedTo-throwing-sibling = pair (T: S: T.attrsOf (ctT S)) (ab "hello") b;
      test-attrsOf-coercedTo-sibling-outside-the-domain = pair (T: S: T.attrsOf (ctOk S)) (ab 5) b;
      test-attrsOf-uniq-sibling-defined-twice = pair (T: S: T.attrsOf (np.uniq S)) twice b;
      test-attrsOf-unique-sibling-defined-twice = pair (T: S: T.attrsOf (uq S)) twice b;
      test-attrsOf-attrsWith-placeholder-sibling-not-a-set = pair (T: S: T.attrsOf (awP S)) [
        {
          a = 5;
          b.k.x = 5;
        }
      ] b;
      test-attrsOf-lazy-attrsWith-placeholder-sibling-not-a-set = pair (T: S: T.attrsOf (awLP S)) [
        {
          a = 5;
          b.k.x = 5;
        }
      ] (v: v.b.k);
      test-listOf-coercedTo-throwing-sibling = pair (T: S: T.listOf (ctT S)) [
        [
          "hello"
          { x = 5; }
        ]
      ] i1;
      test-listOf-coercedTo-sibling-outside-the-domain = pair (T: S: T.listOf (ctOk S)) [
        [
          5
          { x = 5; }
        ]
      ] i1;
      test-listOf-attrsWith-placeholder-sibling-not-a-set = pair (T: S: T.listOf (awP S)) [
        [
          5
          { k.x = 5; }
        ]
      ] i1;
      test-nullOr-under-attrsOf-coercedTo-throwing-sibling = pair (
        T: S: T.attrsOf (T.nullOr (ctT S))
      ) (ab "hello") b;
      test-nullOr-under-attrsOf-uniq-sibling-defined-twice = pair (
        T: S: T.attrsOf (T.nullOr (np.uniq S))
      ) twice b;
      test-uniq-over-coercedTo-throwing-sibling = pair (T: S: T.attrsOf (np.uniq (ctT S))) (ab "hello") b;
      test-coercedTo-over-coercedTo-throwing-sibling = pair (
        T: S: T.attrsOf (np.coercedTo np.str (_: throw "i2xjs: forced") (np.coercedTo np.int toString S))
      ) (ab "hello") b;
      test-coercedTo-over-attrsWith-throwing-sibling =
        pair (T: S: T.attrsOf (np.coercedTo np.str (_: throw "i2xjs: forced") (awP S)))
          [
            {
              a = "hello";
              b.k.x = 5;
            }
          ]
          b;
      test-attrsOf-attrsOf-coercedTo-sibling-in-the-inner-container =
        pair (T: S: T.attrsOf (T.attrsOf (ctT S)))
          [
            {
              p.a = "hello";
              p.b.x = 5;
            }
          ]
          (v: v.p.b);
      test-attrsOf-attrsOf-coercedTo-sibling-across-outer-keys =
        pair (T: S: T.attrsOf (T.attrsOf (ctT S)))
          [
            {
              q.a = "hello";
              p.b.x = 5;
            }
          ]
          (v: v.p.b);
      test-attrsOf-listOf-coercedTo-sibling-across-outer-keys =
        pair (T: S: T.attrsOf (T.listOf (ctT S)))
          [
            {
              q = [ "hello" ];
              p = [ { x = 5; } ];
            }
          ]
          (v: builtins.elemAt v.p 0);
      # the position outside the domain still refuses, catchably, where it is read
      test-attrsOf-coercedTo-throwing-position-refuses = caught (T: S: T.attrsOf (ctT S)) (ab "hello") a;
      test-attrsOf-coercedTo-position-outside-the-domain-refuses = caught (
        T: S: T.attrsOf (ctOk S)
      ) (ab 5) a;
      test-attrsOf-uniq-position-defined-twice-refuses = caught (T: S: T.attrsOf (np.uniq S)) twice a;
      test-attrsOf-attrsWith-placeholder-position-not-a-set-refuses = caught (T: S: T.attrsOf (awP S)) [
        {
          a = 5;
          b.k.x = 5;
        }
      ] a;
      # served today, served after: the whole value equals nixpkgs'
      test-attrsOf-coercedTo-value = pair (T: S: T.attrsOf (ctOk S)) [
        {
          a = "hello";
          b.x = 5;
        }
      ] all;
      test-attrsOf-uniq-value = pair (T: S: T.attrsOf (np.uniq S)) [
        {
          a.x = 1;
          b.x = 5;
        }
      ] all;
      test-attrsOf-attrsWith-placeholder-value = pair (T: S: T.attrsOf (awP S)) [
        {
          a.k.x = 1;
          b = { };
        }
      ] all;
      test-listOf-coercedTo-value = pair (T: S: T.listOf (ctOk S)) [
        [
          "hello"
          { x = 5; }
        ]
      ] all;
      test-nullOr-under-attrsOf-coercedTo-value = pair (T: S: T.attrsOf (T.nullOr (ctOk S))) [
        {
          a = null;
          b = "hi";
        }
      ] all;
      test-attrsOf-attrsOf-coercedTo-value = pair (T: S: T.attrsOf (T.attrsOf (ctOk S))) [
        {
          p.a = "hello";
          q.b.x = 2;
        }
      ] all;
      test-attrsOf-coercedTo-priority-removes-the-coerced-definition = pair (T: S: T.attrsOf (ctT S)) [
        { a = nixpkgsLib.mkDefault "hello"; }
        { a.x = 3; }
      ] a;
      test-attrsOf-coercedTo-conflict-refuses = caught (T: S: T.attrsOf (ctOk S)) [
        { a = "hello"; }
        { b.x = 5; }
        { b.x = 6; }
      ] all;
      # a stock-NAMED record re-homing does not recognise is threaded, so it is marked: the mark reads
      # re-homing's own recognition (`recognitionDoor`), never the functor name alone
      test-attrsOf-pre-elemTypeFunctor-listOf-value = pair (T: S: T.attrsOf (oldListOf S)) [
        {
          a = [ { x = 1; } ];
          b = [ { x = 2; } ];
        }
      ] b;
      test-listOf-pre-elemTypeFunctor-listOf-value = pair (T: S: T.listOf (oldListOf S)) [
        [
          [ { x = 1; } ]
          [ { x = 2; } ]
        ]
      ] i1;
      test-attrsOf-attrsWith-name-placeholder-unrecognised-payload-value =
        pair (T: S: T.attrsOf (awExtra S))
          [
            {
              a.k.x = 1;
              b.k.x = 2;
            }
          ]
          b;
      # a freeform plane typed by an exact container keys its elements as that container does
      test-freeform-attrsOf-coercedTo-sibling-outside-the-domain = {
        expr = (cfg (freeform t sub)).k;
        expected =
          (nixpkgsLib.evalModules {
            modules = freeform np npSub;
          }).config.k;
      };
    };

  # gijly: a foreign root that states a module set and declares NO gen nesting element is mounted
  # as nixpkgs' `fixupOptionType` mounts it, as its rebuild over that set, whose merge is the one
  # served; a stock nixpkgs root stating a module set is served the value it was served before.
  flake.tests.nesting-threaded-root-fixup =
    let
      own = nixpkgsLib.mkOptionType {
        name = "own";
        check = builtins.isAttrs;
        merge = _: _: "OWN-MERGE";
        getSubModules = [ ];
        substSubModules = _: np.submodule { options.x = gm.mkOption { type = t.int; }; };
      };
      ySub = np.submodule { options.x = nixpkgsLib.mkOption { type = np.int; }; };
      cell = type: def: {
        expr = opt type def;
        expected = fwd type def;
      };
    in
    {
      test-a-root-with-no-gen-element-is-mounted-as-its-rebuild-not-its-own-merge = cell own { x = 2; };
      test-a-forwarding-root-with-no-gen-element-is-mounted-as-its-rebuild = cell (np.uniq own) {
        x = 2;
      };
      test-a-stock-submodule-root-is-served-as-before = cell ySub { x = 2; };
      test-a-stock-attrsof-submodule-root-is-served-as-before = cell (np.attrsOf ySub) { a.x = 2; };
      # A stock record is mounted as its rebuild too: a `//` override of its `merge`, or of its
      # `substSubModules`, is served what nixpkgs serves, never the record's own fold.
      test-a-stock-record-s-overridden-merge-is-mounted-as-its-rebuild = cell (
        ySub // { merge = _: _: "OVR"; }
      ) { x = 2; };
      test-a-stock-record-s-overridden-rebuild-is-mounted = cell (
        ySub
        // {
          substSubModules =
            _:
            np.submodule {
              options.x = nixpkgsLib.mkOption { type = np.int; };
              options.z = nixpkgsLib.mkOption {
                type = np.int;
                default = 3;
              };
            };
        }
      ) { x = 2; };
      # the record's own `check` rides on a gen rebuild and admits what it accepts
      test-a-root-s-own-check-on-a-gen-rebuild-admits-what-it-accepts = cell (np.addCheck (
        nixpkgsLib.mkOptionType
          {
            name = "ownG";
            check = builtins.isAttrs;
            merge = nixpkgsLib.mergeOneOption;
            getSubModules = [ ];
            substSubModules = _: t.submodule { options.x = gm.mkOption { type = t.int; }; };
          }
      ) (v: (v.x or 9) > 5)) { x = 7; };
      # A freeform type is no option's root: nixpkgs never fixes it up, and gen does not either.
      test-a-freeform-type-is-not-mounted-as-its-rebuild = {
        expr =
          (cfg [
            { freeformType = np.attrsOf own; }
            { a.x = 2; }
          ]).a;
        expected =
          (nixpkgsLib.evalModules {
            modules = [
              { freeformType = np.attrsOf own; }
              { a.x = 2; }
            ];
          }).config.a;
      };
      test-a-stock-deferred-module-root-stores-as-many-modules = {
        expr =
          builtins.length
            (opt (np.deferredModuleWith {
              staticModules = [ { options.x = gm.mkOption { type = t.int; }; } ];
            }) { config.x = 2; }).imports;
        expected =
          builtins.length
            (fwd (np.deferredModuleWith {
              staticModules = [ { options.x = gm.mkOption { type = t.int; }; } ];
            }) { config.x = 2; }).imports;
      };
    };

  # den-hoag-mda6f: gen's OWN container (or a stock one re-homed as gen's) at an EXACT container's
  # element is keyed where it is READ, as a union and a foreign container are, so no sibling's read
  # splits or forces that sibling's definitions: an attribute-keyed one over-approximately, by its
  # definitions' attribute names, and any other one (an `attrsOf` over a container among them) as a
  # container node. Every `expected` is nixpkgs' evalModules over the
  # same types and definitions, never a literal. One test per cell, so an uncatchable abort errors
  # its own cell only.
  flake.tests.nesting-threaded-native-keyed-on-read =
    let
      npSub = np.submodule { options.x = nixpkgsLib.mkOption { type = np.int; }; };
      optDefs =
        type: defs:
        (cfg ([ { options.h = gm.mkOption { inherit type; }; } ] ++ map (d: { config.h = d; }) defs)).h;
      fwdDefs =
        type: defs:
        (nixpkgsLib.evalModules {
          modules = [
            { options.h = nixpkgsLib.mkOption { inherit type; }; }
          ]
          ++ map (d: { config.h = d; }) defs;
        }).config.h;
      pair = mk: defs: read: {
        expr = read (optDefs (mk t sub) defs);
        expected = read (fwdDefs (mk np npSub) defs);
      };
      caught = mk: defs: read: {
        expr = (builtins.tryEval (builtins.deepSeq (read (optDefs (mk t sub) defs)) true)).success;
        expected = (builtins.tryEval (builtins.deepSeq (read (fwdDefs (mk np npSub) defs)) true)).success;
      };
      forced = throw "mda6f: a sibling's definition was forced";
      bk = v: v.b.k;
      b0 = v: builtins.elemAt v.b 0;
      i1k = v: (builtins.elemAt v 1).k;
      i10 = v: builtins.elemAt (builtins.elemAt v 1) 0;
      all = v: v;
      nodesOf =
        mk: def:
        let
          r = genMergeCore.evalModuleTreeExposed {
            modules = [
              { options.h = gm.mkOption { type = mk t sub; }; }
              { config.h = def; }
            ];
          };
          g = (r._evaluation.get "module-tree" "positions").nested."[\"h\"]";
        in
        builtins.deepSeq r.config.h (
          builtins.filter (k: (g.${k}.mode or null) == "container") (builtins.attrNames g)
        );
    in
    {
      # the sibling outside the inner container's domain: nixpkgs serves the read beside it
      test-attrsOf-attrsOf-sibling-not-a-set = pair (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a = 5;
          b.k.x = 5;
        }
      ] bk;
      test-attrsOf-lazyAttrsOf-sibling-not-a-set = pair (T: S: T.attrsOf (T.lazyAttrsOf S)) [
        {
          a = 5;
          b.k.x = 5;
        }
      ] bk;
      test-attrsOf-listOf-sibling-not-a-list = pair (T: S: T.attrsOf (T.listOf S)) [
        {
          a = 5;
          b = [ { x = 5; } ];
        }
      ] b0;
      test-attrsOf-stock-listOf-sibling-not-a-list = pair (T: S: T.attrsOf (np.listOf S)) [
        {
          a = 5;
          b = [ { x = 5; } ];
        }
      ] b0;
      test-listOf-attrsOf-sibling-not-a-set = pair (T: S: T.listOf (T.attrsOf S)) [
        [
          5
          { k.x = 5; }
        ]
      ] i1k;
      test-listOf-listOf-sibling-not-a-list = pair (T: S: T.listOf (T.listOf S)) [
        [
          5
          [ { x = 5; } ]
        ]
      ] i10;
      test-attrsOf-nullOr-attrsOf-sibling-not-a-set = pair (T: S: T.attrsOf (T.nullOr (T.attrsOf S))) [
        {
          a = 5;
          b.k.x = 5;
        }
      ] bk;
      test-attrsOf-attrsOf-attrsOf-sibling-one-level-down =
        pair (T: S: T.attrsOf (T.attrsOf (T.attrsOf S)))
          [
            {
              b.a = 5;
              b.c.d.x = 5;
            }
          ]
          (v: v.b.c.d);
      # a sibling's inner element is not forced: nixpkgs merges it only where it is read
      test-attrsOf-attrsOf-sibling-element-not-forced = pair (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a.k = forced;
          b.k.x = 5;
        }
      ] bk;
      test-listOf-listOf-sibling-element-not-forced = pair (T: S: T.listOf (T.listOf S)) [
        [
          [ forced ]
          [ { x = 5; } ]
        ]
      ] i10;
      # the position outside the domain still refuses, catchably, where it is read
      test-attrsOf-attrsOf-position-not-a-set-refuses = caught (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a = 5;
          b.k.x = 5;
        }
      ] (v: v.a);
      test-listOf-attrsOf-position-not-a-set-refuses = caught (T: S: T.listOf (T.attrsOf S)) [
        [
          5
          { k.x = 5; }
        ]
      ] (v: builtins.elemAt v 0);
      # served today, served after: the whole value equals nixpkgs'
      test-attrsOf-attrsOf-value = pair (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a.k.x = 1;
          b.k.x = 5;
          b.j.x = 2;
        }
      ] all;
      test-attrsOf-listOf-value = pair (T: S: T.attrsOf (T.listOf S)) [
        {
          a = [ { x = 1; } ];
          b = [ { x = 5; } ];
        }
      ] all;
      test-listOf-attrsOf-value = pair (T: S: T.listOf (T.attrsOf S)) [
        [
          { k.x = 1; }
          { k.x = 5; }
        ]
      ] all;
      test-attrsOf-attrsOf-attrsOf-value = pair (T: S: T.attrsOf (T.attrsOf (T.attrsOf S))) [
        {
          a.c.d.x = 1;
          b.c.d.x = 5;
          b.e = { };
        }
      ] all;
      # depth 3: an `attrsOf` over a container is a node, one per outer element
      test-attrsOf-attrsOf-attrsOf-sibling-not-a-set = pair (T: S: T.attrsOf (T.attrsOf (T.attrsOf S))) [
        {
          a = 5;
          b.c.d.x = 5;
        }
      ] (v: v.b.c.d);
      test-attrsOf-listOf-attrsOf-sibling-not-a-list = pair (T: S: T.attrsOf (T.listOf (T.attrsOf S))) [
        {
          a = 5;
          b = [ { d.x = 5; } ];
        }
      ] (v: (builtins.elemAt v.b 0).d);
      # the container-node mark (`interface.mayFoldNested`): an `attrsOf` whose element may be a
      # container is marked, through a stock middle container, a foreign element and `nullOr`;
      # served at base, served after
      test-attrsOf-stock-attrsOf-attrsOf-value = pair (T: S: T.attrsOf (np.attrsOf (T.attrsOf S))) [
        {
          a.c.d.x = 1;
          b.c.d.x = 5;
        }
      ] all;
      test-attrsOf-stock-attrsOf-stock-attrsOf-value =
        pair (T: S: T.attrsOf (np.attrsOf (np.attrsOf S)))
          [
            {
              a.c.d.x = 1;
              b.c.d.x = 5;
            }
          ]
          all;
      test-attrsOf-attrsOf-nullOr-attrsOf-value =
        pair (T: S: T.attrsOf (T.attrsOf (T.nullOr (T.attrsOf S))))
          [
            {
              a.c = null;
              b.c.d.x = 5;
              b.e.d.x = 1;
            }
          ]
          all;
      # an `attrsOf` over a list-keyed element keys over-approximately, and each element is a node
      test-attrsOf-attrsOf-nullOr-listOf-value =
        pair (T: S: T.attrsOf (T.attrsOf (T.nullOr (T.listOf S))))
          [
            {
              a.c = null;
              b.c = [ { x = 5; } ];
              b.e = [
                { x = 1; }
                { x = 5; }
              ];
            }
          ]
          all;
      test-attrsOf-attrsOf-nullOr-listOf-sibling-element-not-forced =
        pair (T: S: T.attrsOf (T.attrsOf (T.nullOr (T.listOf S))))
          [
            {
              a.c = [ forced ];
              b.c = [ { x = 5; } ];
            }
          ]
          (v: builtins.elemAt v.b.c 0);
      test-attrsOf-attrsOf-nullOr-listOf-inner-sibling-not-forced =
        pair (T: S: T.attrsOf (T.attrsOf (T.nullOr (T.listOf S))))
          [
            {
              b.a = [ forced ];
              b.c = [ { x = 5; } ];
            }
          ]
          (v: builtins.elemAt v.b.c 0);
      # an over-approximated position's elements key without forcing their definitions
      test-attrsOf-attrsOf-nullOr-sibling-element-not-forced =
        pair (T: S: T.attrsOf (T.attrsOf (T.nullOr S)))
          [
            {
              a.c = forced;
              b.c.x = 5;
            }
          ]
          (v: v.b.c);
      # candidate keys: an over-approximated key whose definitions all discharge is never read
      test-attrsOf-attrsOf-sibling-element-mkIf-false = pair (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a.k = nixpkgsLib.mkIf false { x = 1; };
          a.j.x = 2;
          b.k.x = 5;
        }
      ] all;
      test-attrsOf-attrsOf-sibling-element-mkIf-false-not-forced = pair (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a.k = nixpkgsLib.mkIf false forced;
          b.k.x = 5;
        }
      ] bk;
      test-attrsOf-attrsOf-sibling-overridden-not-a-set = pair (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a = nixpkgsLib.mkForce { k.x = 1; };
          b.k.x = 5;
        }
        { a = 5; }
      ] all;
      test-attrsOf-attrsOf-sibling-element-overridden = pair (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a.k = nixpkgsLib.mkForce { x = 1; };
          b.k.x = 5;
        }
        {
          a.k.x = 2;
          a.j.x = 3;
        }
      ] all;
      test-attrsOf-attrsOf-sibling-mkMerge-not-a-set = pair (T: S: T.attrsOf (T.attrsOf S)) [
        {
          a = nixpkgsLib.mkMerge [
            { k.x = 1; }
            5
          ];
          b.k.x = 5;
        }
      ] bk;
      # THE GRANULARITY: which of the root's positions are container nodes, read off the positions
      # record (`nesting-placement.nix`'s `.mode` idiom). No nixpkgs reference states a node set, and
      # every value below is equal under N3p's coarser predicate too, so the node set is the oracle:
      # an `attrsOf` over a node-kind element mints one node per INNER element and none at the outer
      # one, and `attrsOf^k S` at an exact element is a node exactly where k is even.
      test-node-set-attrsOf-attrsOf-listOf = {
        expr = nodesOf (T: S: T.attrsOf (T.attrsOf (T.listOf S))) {
          p.a = [ { x = 1; } ];
          p.b = [ { x = 2; } ];
          q.a = [ { x = 3; } ];
        };
        expected = [
          "[\"p\",\"a\"]"
          "[\"p\",\"b\"]"
          "[\"q\",\"a\"]"
        ];
      };
      test-node-set-attrsOf-depth-3 = {
        expr = nodesOf (T: S: T.attrsOf (T.attrsOf (T.attrsOf S))) {
          p.a.m.x = 1;
          p.b.m.x = 2;
          q.a.m.x = 3;
        };
        expected = [
          "[\"p\"]"
          "[\"q\"]"
        ];
      };
      test-node-set-attrsOf-depth-4 = {
        expr = nodesOf (T: S: T.attrsOf (T.attrsOf (T.attrsOf (T.attrsOf S)))) {
          p.a.m.n.x = 1;
          p.b.m.n.x = 2;
          q.a.m.n.x = 3;
        };
        expected = [
          "[\"p\",\"a\"]"
          "[\"p\",\"b\"]"
          "[\"q\",\"a\"]"
        ];
      };
      # THE WALK AND THE FOLD AGREE AT THE DOOR: the walk keys an over-approximated position by
      # `admitsAll` over the container's `admits`, the fold's door (`refusingOutside`) spells the same
      # quantifier inline, and the two give one verdict on every definition list here, over every
      # structural container's own `admits`. The definitions are every pair (and every single, and
      # none) of values spanning each domain's split. LIVE CONTROL in the same cell: every member
      # both admits and refuses some list, so the agreement is not over one verdict.
      test-walk-and-fold-door-agree =
        let
          values = [
            { }
            { a = 1; }
            [ ]
            [ 1 ]
            5
            "s"
            "/p/m.nix"
            ./.
            (x: x)
            null
            true
          ];
          defsOf = map (v: {
            file = "/p/F.nix";
            value = v;
          });
          lists = [
            [ ]
          ]
          ++ map (v: defsOf [ v ]) values
          ++ concatMap (
            a:
            map (
              b:
              defsOf [
                a
                b
              ]
            ) values
          ) values;
          concatMap = f: l: builtins.concatLists (map f l);
          members = {
            submodule = sub;
            listOf = t.listOf t.int;
            attrsOf = t.attrsOf t.int;
            lazyAttrsOf = t.lazyAttrsOf t.int;
            attrs = t.attrs;
            deferredModule = t.deferredModule;
          };
          walk = ty: genMergeCore.admitsAll ty.admits;
          fold =
            ty: defs:
            (builtins.tryEval (genMergeCore.refusingOutside "t" ty.admits (_: _: true) [ "o" ] defs)).success;
        in
        {
          expr = builtins.mapAttrs (_: ty: {
            disagree = builtins.length (builtins.filter (defs: walk ty defs != fold ty defs) lists);
            bothVerdicts =
              builtins.length (builtins.filter (walk ty) lists) != 0
              && builtins.length (builtins.filter (defs: !(walk ty defs)) lists) != 0;
          }) members;
          expected = builtins.mapAttrs (_: _: {
            disagree = 0;
            bothVerdicts = true;
          }) members;
        };
    };

  # 6yfat: a record built through gen's own `mkOptionType` door whose author stated its fold apart
  # from its rebuild is mounted as that rebuild at an option root, as nixpkgs mounts the same exported
  # record; a door record whose fold is its rebuild's is served the value it was served before.
  flake.tests.nesting-threaded-gen-door =
    let
      ySub = np.submodule { options.x = nixpkgsLib.mkOption { type = np.int; }; };
      door =
        extra:
        let
          self = gm.mkOptionType (
            {
              name = "own";
              check = builtins.isAttrs;
              merge = _: _: "OWN-MERGE";
              getSubOptions = ySub.getSubOptions;
              getSubModules = [ ];
              substSubModules = _: ySub;
              functor = nixpkgsLib.types.defaultFunctor "own" // {
                binOp = a: _: a;
                payload = { };
                type = _: self;
              };
            }
            // extra
          );
        in
        self;
      own = door { };
      cell = type: def: {
        expr = opt type def;
        expected = fwd type def;
      };
    in
    {
      test-a-door-root-is-mounted-as-its-rebuild-not-its-own-merge = cell own { x = 2; };
      test-a-door-root-under-a-gen-container-is-mounted-as-its-rebuild = cell (t.attrsOf own) {
        a.x = 2;
      };
      # the reference mounts the record inside nixpkgs' own submodule: one inside gen's would run
      # gen's code and move with this tree
      test-a-door-root-inside-a-gen-submodule-is-mounted-as-its-rebuild = {
        expr = opt (t.submodule { options.i = gm.mkOption { type = own; }; }) { i.x = 2; };
        expected = fwd (np.submodule { options.i = nixpkgsLib.mkOption { type = own; }; }) { i.x = 2; };
      };
      # a descriptor in gen's own vocabulary, stating its `substructure` beside its fold
      test-a-gen-vocabulary-door-root-is-mounted-as-its-rebuild = cell (gm.mkOptionType {
        name = "ownG";
        mergeDefs = _: _: "OWN-MERGE";
        substructure = {
          declares = ySub.getSubOptions;
          modules = [ ];
          rebuild = _: ySub;
        };
      }) { x = 2; };
      test-a-door-root-whose-fold-is-its-rebuild-s-is-served-as-before = cell (door {
        merge = loc: defs: ySub.merge loc defs;
      }) { x = 2; };
      test-a-door-record-stating-no-module-set-keeps-its-own-merge = cell (door {
        getSubModules = null;
      }) { x = 2; };
      # a crossed record whose module set is nulled by `//` keeps the mark its crossing stated; the
      # class is re-tested where it is read, so under a gen container it keeps its own merge, as
      # nixpkgs' own `attrsOf` over the same record serves it (nixpkgs fixes up no record stating no
      # module set). The reference is nixpkgs' container, not gen's exported one: gen's `attrsOf`
      # states its element's `substructure.modules`, which the `//` left in place.
      test-a-gen-container-over-a-door-record-whose-module-set-is-nulled-keeps-its-own-merge = {
        expr = opt (t.attrsOf (own // { getSubModules = null; })) { a.x = 2; };
        expected = fwd (np.attrsOf (own // { getSubModules = null; })) { a.x = 2; };
      };
      # the mount carries the record's own `check` (`homedRootFixed` reads `mountOf`, never the bare
      # `substSubModules`): under a gen container the definition the check rejects is refused, where
      # nixpkgs' fix-up erases the check and serves it (the parity exception keeps the refusal)
      test-a-door-root-s-own-check-rides-on-its-mount-under-a-gen-container = {
        expr =
          (builtins.tryEval (
            builtins.deepSeq (opt (t.attrsOf (door {
              check = v: builtins.isAttrs v && (v.x or 0) > 1;
            })) { a.x = 0; }) null
          )).success;
        expected = false;
      };
    };
}
