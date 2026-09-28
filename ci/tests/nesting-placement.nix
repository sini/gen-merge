# PLACEMENT: nested trees are children of the one evaluation (den-hoag-n6dh7 Unit 2.4; spec
# `2026-09-22-gen-scope-nta-spec.md` v11 items 1, 2, 4, 5, cells U2-g, U2-l, U2-o, U2-r, U2-s).
#
# Since the switch every nested tree is an `nta` child of the ROOT evaluation that holds it, and the
# fold reads it through that evaluation's accessor: `evalModuleTree` is one `scope.eval`. The values
# below are the called folds' values at the switch's parent (gen-merge 193a18d), unless a ruling
# moves them; the evaluation COUNT is the per-process cell `one-eval-*` (`ci/tests-process.nix`),
# which counts `scope.eval` calls. `ci/tests-error.nix`'s `nesting-placement` suite pins the texts.
{
  genMerge,
  genMergeCore,
  genScope,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;

  evalExposed = modules: genMergeCore.evalModuleTreeExposed { inherit modules; };
  # The ROOT's own nested children, `{ <group> = [ <key> … ]; }`, off the root's own product.
  rootChildrenOf =
    r:
    let
      groups = (r._evaluation.get "module-tree" "nta-children").nested;
    in
    builtins.mapAttrs (_: builtins.attrNames) (
      builtins.removeAttrs groups (builtins.filter (g: groups.${g} == { }) (builtins.attrNames groups))
    );
  childId = genScope.mintNtaId "module-tree" "nested";

  sub = t.submodule { options.x = gm.mkOption { type = t.int; }; };
  named = t.submodule (
    { name, ... }:
    {
      options.n = gm.mkOption {
        type = t.str;
        default = name;
      };
      options.x = gm.mkOption {
        type = t.int;
        default = 0;
      };
    }
  );
  host =
    type: defs:
    [
      { options.o = gm.mkOption { inherit type; }; }
    ]
    ++ map (d: { config.o = d; }) defs;
  row =
    type: defs:
    let
      r = evalExposed (host type defs);
    in
    {
      value = r.config.o;
      keys = rootChildrenOf r;
    };
in
{
  # U2-g: each nested tree is a child of the one evaluation, with its value unchanged.
  flake.tests.nesting-placement-children = {
    test-each-shape-folds-its-children-to-the-called-value = {
      expr = {
        sub-one = (gm.evalModuleTree { modules = host sub [ { x = 2; } ]; }).config.o;
        attrs-two =
          (gm.evalModuleTree {
            modules = host (t.attrsOf sub) [
              {
                a.x = 1;
                b.x = 2;
              }
            ];
          }).config.o;
        list-two =
          (gm.evalModuleTree {
            modules = host (t.listOf sub) [
              [
                { x = 1; }
                { x = 2; }
              ]
            ];
          }).config.o;
        sub-empty =
          (gm.evalModuleTree {
            modules = host (t.submodule {
              options.x = gm.mkOption {
                type = t.int;
                default = 0;
              };
            }) [ ];
          }).config.o;
        list-two-defs =
          map (e: e.n)
            (gm.evalModuleTree {
              modules = host (t.listOf named) [
                [ { } ]
                [ { } ]
              ];
            }).config.o;
      };
      expected = {
        sub-one.x = 2;
        attrs-two = {
          a.x = 1;
          b.x = 2;
        };
        list-two = [
          { x = 1; }
          { x = 2; }
        ];
        sub-empty.x = 0;
        list-two-defs = [
          "0"
          "0"
        ];
      };
    };
    # A tree nested in a tree is a child of the child: both are nodes of the one evaluation, and
    # the grandchild is minted under its host's own identifier.
    test-a-grandchild-is-a-node-of-the-one-evaluation = {
      expr =
        let
          r = evalExposed (
            host (t.attrsOf (t.submodule { options.i = gm.mkOption { type = t.attrsOf sub; }; })) [
              { a.i.b.x = 5; }
            ]
          );
          child = childId "[\"o\"]" "[\"a\"]";
        in
        {
          value = r.config.o;
          grandchild = builtins.elem (genScope.mintNtaId child "nested" "[\"i\"]"
            "[\"b\"]"
          ) r._evaluation.allNodeIds;
        };
      expected = {
        value.a.i.b.x = 5;
        grandchild = true;
      };
    };
    # The tree record (`evalModuleTree`'s `.type`) nests the same way.
    test-the-tree-record-is-a-child-too = {
      expr =
        let
          tree =
            (gm.evalModuleTree {
              modules = [ { options.x = gm.mkOption { type = t.int; }; } ];
            }).type;
          r = evalExposed (host tree [ { x = 3; } ]);
        in
        {
          value = r.config.o;
          keys = rootChildrenOf r;
        };
      expected = {
        value.x = 3;
        keys."[\"o\"]" = [ "[]" ];
      };
    };
  };

  # U2-r (v10): a union whose nesting member is a CONTAINER is walked member by member at its own
  # position, a container member only where every definition has its shape, and the fold reads the
  # children the walk minted. Values are the called folds' at 193a18d.
  flake.tests.nesting-placement-unions = {
    test-a-union-over-an-attribute-container-keys-its-elements = {
      expr = row (t.either (t.attrsOf sub) t.str) [
        {
          a.x = 1;
          b.x = 2;
        }
      ];
      expected = {
        value = {
          a.x = 1;
          b.x = 2;
        };
        keys."[\"o\"]" = [
          "[\"a\"]"
          "[\"b\"]"
        ];
      };
    };
    # The shape filter: a string definition is not the container's shape, so nothing is keyed.
    test-a-union-over-a-container-keys-nothing-for-another-shape = {
      expr = row (t.either (t.attrsOf sub) t.str) [ "s" ];
      expected = {
        value = "s";
        keys = { };
      };
    };
    test-a-union-over-a-list-keys-its-elements = {
      expr = row (t.either (t.listOf sub) t.str) [
        [
          { x = 1; }
          { x = 2; }
        ]
      ];
      expected = {
        value = [
          { x = 1; }
          { x = 2; }
        ];
        keys."[\"o\"]" = [
          "[0,0]"
          "[0,1]"
        ];
      };
    };
    # Under an exact container, each element is its own union position (gate P5): `q`'s string
    # is not the container's shape, so it keys nothing, though `canNest` holds there.
    test-a-union-element-over-a-container-keys-only-its-own-shape = {
      expr = row (t.attrsOf (t.either (t.attrsOf sub) t.str)) [
        {
          p.a.x = 1;
          q = "s";
        }
      ];
      expected = {
        value = {
          p.a.x = 1;
          q = "s";
        };
        keys."[\"o\"]" = [ "[\"p\",\"a\"]" ];
      };
    };
    # Under a lazy container a union's container member is S1's class (a), RULED (iii): refused.
    test-a-union-over-a-strict-container-under-a-lazy-one-is-refused = {
      expr = refused (row (t.lazyAttrsOf (t.either (t.attrsOf sub) t.str)) [ { p.a.x = 1; } ]);
      expected = true;
    };
    # The control: a nesting member keys the union's own position.
    test-a-union-over-a-tree-keys-its-own-position = {
      expr = row (t.either sub t.str) [ { x = 1; } ];
      expected = {
        value.x = 1;
        keys."[\"o\"]" = [ "[]" ];
      };
    };
    # The member is the one the fold's `split` chain reaches, with `choose` applied (gate C4): both
    # members key `[ k ]`, and the definitions are `subA`'s, which `choose` takes first.
    test-a-position-two-members-key-evaluates-under-the-member-the-fold-chose = {
      expr =
        let
          subA = t.submodule { options.x = gm.mkOption { type = t.int; }; };
          subB = t.submodule { options.y = gm.mkOption { type = t.int; }; };
        in
        row (t.either (t.attrsOf subA) (t.attrsOf subB)) [ { k.x = 1; } ];
      expected = {
        value.k.x = 1;
        keys."[\"o\"]" = [ "[\"k\"]" ];
      };
    };
  };

  # U2-l: an over-approximated child the host's fold never SELECTED is a CANDIDATE. It is a node of
  # the evaluation, and only its `result` refuses, by name, before any of its member's modules is
  # applied; the host's own value is unchanged.
  flake.tests.nesting-placement-candidates = {
    test-a-candidate-is-enumerated-and-its-result-refuses = {
      expr =
        let
          r = evalExposed (
            host (t.lazyAttrsOf (t.either sub t.str)) [
              {
                foo = "s";
                bar.x = 1;
              }
            ]
          );
          cand = childId "[\"o\"]" "[\"foo\"]";
        in
        {
          value = r.config.o;
          enumerated = builtins.elem cand r._evaluation.allNodeIds;
          record = (r._evaluation.node cand).parent;
          result = refused (r._evaluation.get cand "result").config;
          selected = (r._evaluation.get (childId "[\"o\"]" "[\"bar\"]") "result").config;
        };
      expected = {
        value = {
          foo = "s";
          bar.x = 1;
        };
        enumerated = true;
        record = "module-tree";
        result = true;
        selected.x = 1;
      };
    };
  };

  # U2-o: the report mode is a property of the SITE, carried into the child on its position record.
  # One tree type, `check = false` in the tree and an undeclared `bogus` in the definition.
  flake.tests.nesting-placement-mode =
    let
      tree =
        (gm.evalModuleTree {
          check = false;
          modules = [ { options.x = gm.mkOption { type = t.int; }; } ];
        }).type;
      at =
        check: type: def:
        gm.evalModuleTree {
          inherit check;
          modules = [
            { options.t = gm.mkOption { inherit type; }; }
            { config.t = def; }
          ];
        };
      bogus = {
        x = 1;
        bogus = 2;
      };
    in
    {
      test-each-site-evaluates-its-child-in-its-own-mode = {
        expr = {
          mode-carried =
            let
              r = at false tree bogus;
            in
            {
              inherit (r.config) t;
              undeclared = map (u: u.path) r.undeclared;
            };
          mode-element = refused (at false (t.attrsOf tree) { a = bogus; }).config.t;
          mode-inherited = refused (at true tree bogus).config.t;
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
      # What each site's child receives on its position record, and so evaluates in: the reported
      # pair where the rich fold carries a report, else the member's CALLED mode. The tree record's
      # strict fold refuses a finding whatever its child's mode, so the values above cannot tell a
      # carried child from a called one; the record can.
      test-each-sites-child-receives-its-sites-mode = {
        expr =
          let
            modeAt =
              check: type: def: key:
              let
                r = genMergeCore.evalModuleTreeExposed {
                  inherit check;
                  modules = [
                    { options.t = gm.mkOption { inherit type; }; }
                    { config.t = def; }
                  ];
                };
              in
              (r._evaluation.get "module-tree" "positions").nested."[\"t\"]".${key}.mode;
          in
          {
            carried = modeAt false tree bogus "[]";
            element = modeAt false (t.attrsOf tree) { a = bogus; } "[\"a\"]";
            inherited = modeAt true tree bogus "[]";
            elementCalled = tree.nests.calledMode;
          };
        expected = {
          carried = {
            carried = true;
            inherited = false;
          };
          element = "called";
          inherited = {
            carried = true;
            inherited = true;
          };
          elementCalled = {
            carried = false;
            inherited = false;
          };
        };
      };
    };

  # U2-s (v11): OQ15's default (c), *defaulted, reversible*. A nesting type that holds itself, on
  # an option left undefined, grows undefined trees without end; the walk refuses past its fuel
  # (`importedTypeWalkFuel`, 32) by name. A read shallower than the fuel still answers.
  flake.tests.nesting-placement-empty-growth =
    let
      recsub = t.submodule {
        options.x = gm.mkOption { type = recsub; };
        options.v = gm.mkOption {
          type = t.int;
          default = 7;
        };
      };
      r = gm.evalModuleTree { modules = host recsub [ ]; };
      down = d: v: if d == 0 then v else down (d - 1) v.x;
    in
    {
      test-a-read-shallower-than-the-fuel-answers = {
        expr = {
          read3 = r.config.o.x.x.v;
          deepest = (down 31 r.config.o).v;
        };
        expected = {
          read3 = 7;
          deepest = 7;
        };
      };
      test-growth-past-the-fuel-refuses = {
        expr = refused (down 32 r.config.o);
        expected = true;
      };
      # The enumeration clause: enumerating the node set reaches the refusal and is refused within a
      # bounded time, rather than growing without end (it needs gen-scope's per-level host
      # resolution, `c93a5c0`, to reach depth 33 at all).
      test-enumerating-the-growth-refuses = {
        expr =
          (builtins.tryEval (builtins.length (evalExposed (host recsub [ ]))._evaluation.allNodeIds)).success;
        expected = false;
      };
      # The control: an undefined two-level nesting that does not recurse enumerates.
      test-an-undefined-nesting-that-does-not-recurse-enumerates = {
        expr =
          let
            leafB = t.submodule {
              options.w = gm.mkOption {
                type = t.int;
                default = 1;
              };
            };
            r2 = evalExposed (host (t.submodule { options.b = gm.mkOption { type = leafB; }; }) [ ]);
          in
          {
            nodes = builtins.length r2._evaluation.allNodeIds;
            w = r2.config.o.b.w;
          };
        expected = {
          nodes = 3;
          w = 1;
        };
      };
    };
}
