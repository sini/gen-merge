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
    (gm.evalModuleTree {
      modules = [ { options.x = gm.mkOption { type = t.int; }; } ];
      check = false;
    }).type;
  cfg = mods: (gm.evalModuleTree { modules = mods; }).config;
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
    test-a-nesting-type-states-whether-its-tree-is-named = {
      expr = {
        sub = sub.nests.named;
        tree = tree.nests.named;
      };
      expected = {
        sub = true;
        tree = false;
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
              r = gm.evalModuleTree {
                modules = [
                  {
                    options.t = gm.mkOption { inherit type; };
                    config.t = def;
                  }
                ];
                inherit check;
              };
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
          family = import ./_fixtures/tree-union-family.nix { inherit genMerge nixpkgsLib; };
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
}
