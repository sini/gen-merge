# The DECLARATION half of nested trees as `nta` children (den-hoag-n6dh7 Unit 2.1, spec
# `2026-09-22-gen-scope-nta-spec.md` v9): what a type SAYS about the nested trees its value holds,
# before any evaluation reads it. The discharge twin and its addresses (U2-j), each container's
# `split` and the position step it states, the nesting predicates (`isNesting`, `canNest`,
# `declaresNesting` with its declared opt-out, U2-q's declaration half), the nesting types' `nests`,
# the report mode a position carries, and the recognition of a stock foreign container.
#
# Every cell here is additive: the called folds still evaluate every nested tree, so nothing below
# moves a value. `ci/tests-error.nix`'s `nesting-declaration` suite pins the refusals' text.
{
  genMerge,
  genMergeCore,
  interface,
  nixpkgsLib,
  prelude,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib.types;
  priority = import ../../lib/priority.nix { inherit prelude; };
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;

  # gen-scope's `walkAddress` read (Unit 1 item 2), restated: an attribute name selects, a list
  # index selects, and anything else is not found. gen-scope does not publish it, so the cell reads
  # its two step kinds here rather than importing the binding.
  walk =
    v: steps:
    if steps == [ ] then
      {
        found = true;
        value = v;
      }
    else
      let
        s = builtins.head steps;
        rest = builtins.tail steps;
      in
      if builtins.isString s && builtins.isAttrs v && v ? ${s} then
        walk v.${s} rest
      else if builtins.isInt s && builtins.isList v && s < builtins.length v then
        walk (builtins.elemAt v s) rest
      else
        { found = false; };

  # The priority suite's definition shapes (`ci/tests/merge.nix`): bare, `mkMerge`, `mkIf` both
  # ways, `mkDefault`, `mkForce`, an order marker, and nestings of them.
  priorityFixtures = [
    "a"
    (gm.mkMerge [ "a" ])
    (gm.mkIf false "no")
    (gm.mkIf true "yes")
    (gm.mkDefault "lo")
    (gm.mkForce "forced")
    (gm.mkBefore "b")
    (gm.mkMerge [
      (gm.mkIf true "x")
      (gm.mkMerge [
        "y"
        (gm.mkIf false "z")
      ])
      (gm.mkForce "w")
    ])
    (gm.mkIf true (
      gm.mkMerge [
        "p"
        (gm.mkDefault "q")
      ]
    ))
    { k = gm.mkIf false 1; }
  ];

  # A NESTING TYPE, stood in: it states its tree (`nests`) and carries the threaded sibling on its
  # fold. No gen type carries the sibling until the threaded half lands, so the predicates' `true`
  # arms are read on this record.
  standIn = {
    name = "standIn";
    nests = { };
    mergeDefs = {
      __functor =
        _: _loc: defs:
        (builtins.head defs).value;
      threaded =
        _ev: _loc: defs:
        (builtins.head defs).value;
    };
  };
  # The same record copied the way a wrapper copies it (`refined`'s `removeAttrs`): `nests` kept, the
  # fold a bare lambda, so the sibling is gone.
  copied = standIn // {
    mergeDefs = _loc: defs: (builtins.head defs).value;
  };
  # A chain of `n` gen containers over `x`.
  deep = n: x: if n == 0 then x else t.attrsOf (deep (n - 1) x);

  # nixpkgs' `types.json` shape: a self-referential element, under an unrecognised container.
  valueType = np.nullOr (
    np.oneOf [
      np.str
      (np.attrsOf valueType)
      (np.listOf valueType)
    ]
  );

  tree =
    (gm.evalModuleTree { } [
      {
        options.x = gm.mkOption {
          type = t.int;
          default = 0;
        };
      }
    ]).type;
  subMods = [
    (
      { name, ... }:
      {
        options.x = gm.mkOption { type = t.int; };
        options.n = gm.mkOption {
          type = t.str;
          default = name;
        };
      }
    )
  ];
  sub = t.submodule subMods;
  entryDef = {
    file = "/d.nix";
    value = {
      x = 3;
    };
  };

  splitOf =
    ty: loc: defs:
    map (e: { inherit (e) step loc defs; }) (ty.split loc defs);
  twoDefs = [
    {
      file = "/a.nix";
      value = [ "a" ];
    }
    {
      file = "/b.nix";
      value = [ "b" ];
    }
  ];
  steps = ty: defs: map (e: e.step) (ty.split [ "o" ] defs);
  distinct =
    xs:
    builtins.length (
      builtins.attrNames (
        builtins.listToAttrs (
          map (x: {
            name = builtins.toJSON x;
            value = null;
          }) xs
        )
      )
    );

  hostLax = {
    carried = true;
    strict = false;
  };
  hostStrict = {
    carried = true;
    strict = true;
  };
  hostUncarried = {
    carried = false;
    strict = false;
  };
  position =
    host: ty: key:
    genMergeCore.nestedPosition host ty {
      inherit key;
      address = {
        attr = "definitions";
        def = 0;
        at = [
          0
          "value"
        ];
      };
      loc = [ "o" ] ++ key;
    };
in
{
  # ── U2-j: the discharge twin ──────────────────────────────────────────────────────────────────
  flake.tests.nesting-declaration-discharge-twin = {
    # Its values are the value path's, fixture for fixture.
    test-the-twin-discharges-to-the-same-values = {
      expr = map (v: map (x: x.value) (priority.dischargePropertiesAt v)) priorityFixtures;
      expected = map (v: map (x: x.value) (priority.dischargeProperties v)) priorityFixtures;
    };
    test-the-twin-keeps-the-same-priorities = {
      expr = map (v: map (x: x.priority) (priority.dischargePropertiesAt v)) priorityFixtures;
      expected = map (v: map (x: x.priority) (priority.dischargeProperties v)) priorityFixtures;
    };
    # And each path is an address: walked from the definition, it reaches exactly that value.
    test-every-path-resolves-to-its-value = {
      expr = builtins.all (
        v:
        builtins.all (
          x:
          let
            r = walk v x.path;
          in
          r.found && r.value == x.value
        ) (priority.dischargePropertiesAt v)
      ) priorityFixtures;
      expected = true;
    };
    test-the-paths-name-the-merge-index-and-the-content-step = {
      expr = map (x: x.path) (
        priority.dischargePropertiesAt (
          gm.mkMerge [
            "a"
            (gm.mkIf true (gm.mkForce "b"))
          ]
        )
      );
      expected = [
        [
          "contents"
          0
        ]
        [
          "contents"
          1
          "content"
          "content"
        ]
      ];
    };
    # An override's content stays LAZY, as the value path keeps it: a losing default that throws is
    # discharged without being forced.
    test-an-override-content-is-not-forced = {
      expr = builtins.length (priority.dischargePropertiesAt (gm.mkDefault (throw "forced")));
      expected = 1;
    };
  };

  # ── the split: each container states its element positions once ───────────────────────────────
  flake.tests.nesting-declaration-split = {
    # U2-g's `lt-two-defs` shape. The step `[ d i ]` names the two elements twice, and the `loc`
    # segment is the same position in nixpkgs `listOf`'s spelling, `[definition n-entry m]`.
    test-list-two-definitions-give-two-positions = {
      expr = {
        steps = steps (t.listOf t.str) twoDefs;
        distinct = distinct (steps (t.listOf t.str) twoDefs);
        locs = map (e: e.loc) ((t.listOf t.str).split [ "o" ] twoDefs);
      };
      expected = {
        steps = [
          [
            0
            0
          ]
          [
            1
            0
          ]
        ];
        distinct = 2;
        locs = [
          [
            "o"
            "[definition 1-entry 1]"
          ]
          [
            "o"
            "[definition 2-entry 1]"
          ]
        ];
      };
    };
    # Control, `lt-one-def`: one definition of two elements.
    test-list-one-definition-gives-its-indices = {
      expr = steps (t.listOf t.str) [
        {
          file = "/a.nix";
          value = [
            "a"
            "b"
          ];
        }
      ];
      expected = [
        [
          0
          0
        ]
        [
          0
          1
        ]
      ];
    };
    # The index is taken BEFORE a discharged element is dropped, as the fold's own index is, and as
    # nixpkgs `listOf`'s `[definition n-entry m]` takes `m`.
    test-list-index-is-taken-before-the-drop = {
      expr =
        splitOf (t.listOf t.str)
          [ "o" ]
          [
            {
              file = "/a.nix";
              value = [
                (gm.mkIf false "x")
                "y"
              ];
            }
          ];
      expected = [
        {
          step = [
            0
            1
          ];
          loc = [
            "o"
            "[definition 1-entry 2]"
          ];
          defs = [
            {
              file = "/a.nix";
              value = "y";
            }
          ];
        }
      ];
    };
    # `attrsOf` drops a key whose every definition was discharged; `lazyAttrsOf` keeps it.
    test-attribute-containers-step-by-key = {
      expr =
        let
          defs = [
            {
              file = "/a.nix";
              value = {
                a = 1;
                gone = gm.mkIf false 2;
              };
            }
            {
              file = "/b.nix";
              value = {
                a = 3;
              };
            }
          ];
        in
        {
          strict = map (e: {
            inherit (e) step loc;
            n = builtins.length e.defs;
          }) ((t.attrsOf t.int).split [ "o" ] defs);
          lazy = map (e: e.step) ((t.lazyAttrsOf t.int).split [ "o" ] defs);
        };
      expected = {
        strict = [
          {
            step = [ "a" ];
            loc = [
              "o"
              "a"
            ];
            n = 2;
          }
        ];
        lazy = [
          [ "a" ]
          [ "gone" ]
        ];
      };
    };
    # `lazyAttrsOf`'s fold is the split's TWIN (the wideFreeform hot path, `lib/types.nix`): its
    # keys and per-key values are the split's elements folded, over definitions carrying a
    # discharged key, an override and a key only one definition states.
    test-lazy-fold-is-the-split's = {
      expr =
        let
          ty = t.lazyAttrsOf (t.listOf t.str);
          defs = [
            {
              file = "/a.nix";
              value = {
                a = [ "x" ];
                gone = gm.mkIf false [ "y" ];
                b = gm.mkForce [ "z" ];
              };
            }
            {
              file = "/b.nix";
              value = {
                a = [ "w" ];
                b = [ "lost" ];
                c = [ ];
              };
            }
          ];
          viaSplit = builtins.listToAttrs (
            map (e: {
              name = builtins.head e.step;
              value = builtins.tryEval (gm.mergeDefs e.loc e.type e.defs);
            }) (ty.split [ "o" ] defs)
          );
          viaFold = builtins.mapAttrs (_: builtins.tryEval) (ty.mergeDefs [ "o" ] defs);
        in
        {
          same = viaSplit == viaFold;
          keys = builtins.attrNames viaFold;
        };
      expected = {
        same = true;
        keys = [
          "a"
          "b"
          "c"
          "gone"
        ];
      };
    };
    test-nullable-and-union-add-no-step = {
      expr = {
        # null beside a value has no element to merge through: the position's member is `null`.
        nullOrMember =
          (builtins.head (
            (t.nullOr t.int).split
              [ "o" ]
              [
                {
                  file = "/a.nix";
                  value = null;
                }
                {
                  file = "/b.nix";
                  value = 1;
                }
              ]
          )).type;
        nullOr =
          splitOf (t.nullOr t.int)
            [ "o" ]
            [
              {
                file = "/a.nix";
                value = null;
              }
              {
                file = "/b.nix";
                value = 1;
              }
            ];
        allNull =
          (t.nullOr t.int).split
            [ "o" ]
            [
              {
                file = "/a.nix";
                value = null;
              }
            ];
        either =
          map
            (e: {
              inherit (e) step loc;
              type = e.type.name;
            })
            (
              (t.either t.int t.str).split
                [ "o" ]
                [
                  {
                    file = "/a.nix";
                    value = "s";
                  }
                ]
            );
      };
      expected = {
        nullOrMember = null;
        nullOr = [
          {
            step = [ ];
            loc = [ "o" ];
            defs = [
              {
                file = "/a.nix";
                value = null;
              }
              {
                file = "/b.nix";
                value = 1;
              }
            ];
          }
        ];
        allNull = [ ];
        either = [
          {
            step = [ ];
            loc = [ "o" ];
            type = "string";
          }
        ];
      };
    };
    # `either`'s member choice is ONE binding, read by its split: the member accepting every
    # definition, `null` when neither does.
    test-either-states-its-choice-once = {
      expr = {
        left = ((t.either t.int t.str).choose [ ] [ { value = 1; } ]).name;
        right = ((t.either t.int t.str).choose [ ] [ { value = "s"; } ]).name;
        none =
          (t.either t.int t.str).choose
            [ ]
            [
              { value = 1; }
              { value = "s"; }
            ];
        empty = ((t.either t.int t.str).choose [ ] [ ]).name;
      };
      expected = {
        left = "int";
        right = "string";
        none = null;
        empty = "string";
      };
    };
  };

  # ── the nesting predicates ─────────────────────────────────────────────────────────────────────
  flake.tests.nesting-declaration-predicates = {
    # One binding: `nests` AND the threaded sibling. A copy that kept `nests` and lost the sibling
    # is not a nesting type.
    test-is-nesting-reads-nests-and-the-sibling = {
      expr = {
        standIn = interface.isNesting standIn;
        copied = interface.isNesting copied;
        copiedNests = copied ? nests;
        leaf = interface.isNesting t.str;
        notARecord = interface.isNesting 1;
      };
      expected = {
        standIn = true;
        copied = false;
        copiedNests = true;
        leaf = false;
        notARecord = false;
      };
    };
    # gen's own nesting types state their tree and, since the threaded half (Unit 2.2), carry the
    # sibling: both are nesting types.
    test-the-nesting-types-state-their-tree-and-the-sibling = {
      expr = {
        subNests = sub ? nests;
        treeNests = tree ? nests;
        sub = interface.isNesting sub;
        tree = interface.isNesting tree;
      };
      expected = {
        subNests = true;
        treeNests = true;
        sub = true;
        tree = true;
      };
    };
    # MAY nest: through what each container carries, in either vocabulary, and `true` at exhaustion.
    test-can-nest-walks-what-a-type-carries = {
      expr = {
        attrs = interface.canNest (t.attrsOf standIn);
        union = interface.canNest (t.either t.str (t.listOf standIn));
        foreign = interface.canNest (np.attrsOf standIn);
        flat = interface.canNest (t.attrsOf t.str);
        leaf = interface.canNest t.str;
        exhausted = interface.canNest (deep 33 t.str);
        withinFuel = interface.canNest (deep 31 t.str);
      };
      expected = {
        attrs = true;
        union = true;
        foreign = true;
        flat = false;
        leaf = false;
        exhausted = true;
        withinFuel = false;
      };
    };
  };

  # ── U2-q's declaration half: `declaresNesting`, S2 RULED (i), and the declared opt-out ─────────
  flake.tests.nesting-declaration-declares = {
    # Transitive over what a type declares: an unrecognised container over a stock container over
    # a nesting type declares it one level down.
    test-declares-nesting-is-transitive = {
      expr = {
        direct = interface.declaresNesting (np.uniq standIn);
        transitive = interface.declaresNesting (np.uniq (np.attrsOf standIn));
        flat = interface.declaresNesting (np.uniq (np.attrsOf np.str));
        coerced = interface.declaresNesting (np.coercedTo np.str (x: x) standIn);
      };
      expected = {
        direct = true;
        transitive = true;
        flat = false;
        coerced = true;
      };
    };
    # A payload answers only what a type merges on, so a payload stating an element where no carrying
    # spelling does declares nothing. Where the element it OFFERS declares a nesting type, the walk
    # refuses the record by name (OQ1 arm (ii-a)), at the top and one level down; a flat offer is
    # `false`. `ci/tests-error.nix` pins the text.
    test-a-payload-offering-a-nesting-element-is-refused = {
      expr =
        let
          handrolled = elemType: {
            name = "handrolled";
            functor = {
              name = "handrolled";
              payload = { inherit elemType; };
            };
          };
        in
        {
          offered = refused (interface.declaresNesting (handrolled standIn));
          below = refused (interface.declaresNesting (np.uniq (handrolled standIn)));
          members = refused (
            interface.declaresNesting (handrolled [
              np.str
              standIn
            ])
          );
          flat = interface.declaresNesting (handrolled np.str);
        };
      expected = {
        offered = true;
        below = true;
        members = true;
        flat = false;
      };
    };
    # At exhaustion the walk REFUSES (S2 (i)): `types.json`'s shape cannot be told from a deep one.
    test-a-self-referential-element-is-refused-at-exhaustion = {
      expr = {
        json = refused (interface.declaresNesting (np.uniq valueType));
        deep = refused (interface.declaresNesting (np.uniq (deep 40 t.str)));
        withinFuel = interface.declaresNesting (np.uniq (deep 30 t.str));
      };
      expected = {
        json = true;
        deep = true;
        withinFuel = false;
      };
    };
    # The declared opt-out: `false` on the container or on the self-referential element answers
    # `false` with no walk. Control: the unmarked arm above refuses.
    test-the-declared-opt-out-answers-false-without-a-walk = {
      expr = {
        container = interface.declaresNesting (np.uniq valueType // { declaresNesting = false; });
        element = interface.declaresNesting (np.uniq (valueType // { declaresNesting = false; }));
        nesting = interface.declaresNesting (np.uniq standIn // { declaresNesting = false; });
      };
      expected = {
        container = false;
        element = false;
        nesting = false;
      };
    };
    # Any other value is refused, where the walk meets it and at `mkOptionType`.
    test-a-marker-other-than-false-is-refused = {
      expr = {
        walkTrue = refused (interface.declaresNesting (np.uniq np.str // { declaresNesting = true; }));
        walkString = refused (interface.declaresNesting (np.uniq np.str // { declaresNesting = "no"; }));
        importTrue = refused (
          gm.mkOptionType {
            name = "marked";
            declaresNesting = true;
          }
        );
        importFalse =
          (gm.mkOptionType {
            name = "marked";
            declaresNesting = false;
          }).declaresNesting;
      };
      expected = {
        walkTrue = true;
        walkString = true;
        importTrue = true;
        importFalse = false;
      };
    };
  };

  # ── the nesting types state their tree as data ────────────────────────────────────────────────
  flake.tests.nesting-declaration-nests = {
    test-called-modes = {
      expr = {
        submodule = sub.nests.calledMode;
        tree = tree.nests.calledMode;
      };
      expected = {
        submodule = {
          carried = true;
          inherited = false;
        };
        tree = {
          carried = false;
          inherited = false;
        };
      };
    };
    test-entries-read-a-definition-as-todays-call-does = {
      expr = {
        submodule = sub.nests.entry entryDef;
        tree = tree.nests.entry entryDef;
      };
      expected = {
        submodule = {
          _file = "/d.nix";
          config.x = 3;
        };
        tree = {
          _file = "/d.nix";
          imports = [ { x = 3; } ];
        };
      };
    };
    # Field for field: the tree `nests` states, evaluated through the published door, is the value
    # the called fold gave. The called fold refuses since the switch (Unit 2.4, item 1), so its value
    # is pinned as the literal it gave at the switch's parent (gen-merge 193a18d).
    test-a-submodule-tree-from-nests-equals-the-called-fold = {
      expr =
        let
          n = sub.nests;
          loc = [
            "o"
            "k"
          ];
        in
        (gm.evalModuleTree {
          prefix = loc;
          specialArgs = n.specialArgs // {
            name = "k";
          };
          check = n.check;
        } (n.modules ++ map n.entry [ entryDef ])).config;
      expected = {
        n = "k";
        x = 3;
      };
    };
    test-the-empty-arguments-are-the-when-empty-call = {
      expr = {
        inherit (sub.nests.empty) prefix check;
        # `‹name›` is the engine's placeholder module (`namePlaceholder`), not an argument.
        name = sub.nests.empty.specialArgs ? name;
        treePrefix = tree.nests.empty.prefix;
      };
      expected = {
        prefix = [ ];
        check = true;
        name = false;
        treePrefix = [ ];
      };
    };
  };

  # ── the report mode a position carries ────────────────────────────────────────────────────────
  flake.tests.nesting-declaration-position-mode = {
    # One tree type, three sites: typed directly under a carried lax host, as a container element,
    # typed directly under a carried strict host.
    test-the-site-decides-the-mode = {
      expr = {
        carried = genMergeCore.positionChildMode tree (position hostLax tree [ ]);
        element = genMergeCore.positionChildMode tree (position hostLax tree [ "a" ]);
        inherited = genMergeCore.positionChildMode tree (position hostStrict tree [ ]);
        uncarried = genMergeCore.positionChildMode tree (position hostUncarried tree [ ]);
        subElement = genMergeCore.positionChildMode sub (position hostLax sub [ "a" ]);
        subDirect = genMergeCore.positionChildMode sub (position hostLax sub [ ]);
      };
      expected = {
        carried = {
          carried = true;
          inherited = false;
        };
        element = {
          carried = false;
          inherited = false;
        };
        inherited = {
          carried = true;
          inherited = true;
        };
        uncarried = {
          carried = false;
          inherited = false;
        };
        subElement = {
          carried = true;
          inherited = false;
        };
        subDirect = {
          carried = true;
          inherited = false;
        };
      };
    };
    test-the-record-carries-key-address-and-loc = {
      expr = builtins.removeAttrs (position hostLax tree [ "a" ]) [ "mode" ];
      expected = {
        key = [ "a" ];
        address = {
          attr = "definitions";
          def = 0;
          at = [
            0
            "value"
          ];
        };
        loc = [
          "o"
          "a"
        ];
      };
    };
  };

  # ── re-homing: which stock foreign container a record is ───────────────────────────────────────
  flake.tests.nesting-declaration-rehome = {
    test-the-six-are-recognised = {
      expr =
        let
          r =
            ty:
            let
              x = interface.importedRehome ty;
            in
            if x == null then
              null
            else
              builtins.removeAttrs x [
                "element"
                "alternatives"
              ];
        in
        {
          attrsOf = r (np.attrsOf np.str);
          lazyAttrsOf = r (np.lazyAttrsOf np.str);
          listOf = r (np.listOf np.str);
          nullOr = r (np.nullOr np.str);
          either = r (np.either np.str np.int);
          oneOf = r (
            np.oneOf [
              np.str
              np.int
              np.bool
            ]
          );
          # nixpkgs folds `oneOf` LEFT, so the nested `either` is the first member.
          oneOfNested =
            (interface.importedRehome (
              builtins.elemAt
                (interface.importedRehome (
                  np.oneOf [
                    np.str
                    np.int
                    np.bool
                  ]
                )).alternatives
                0
            )).container;
        };
      expected = {
        attrsOf.container = "attrsOf";
        lazyAttrsOf.container = "lazyAttrsOf";
        listOf.container = "listOf";
        nullOr.container = "nullOr";
        either.container = "either";
        oneOf.container = "either";
        oneOfNested = "either";
      };
    };
    test-the-element-is-carried = {
      expr = (interface.importedRehome (np.attrsOf np.int)).element.name;
      expected = "int";
    };
    test-others-are-not = {
      expr = {
        placeholder = interface.importedRehome (
          np.attrsWith {
            elemType = np.str;
            placeholder = "host";
          }
        );
        uniq = interface.importedRehome (np.uniq np.str);
        submodule = interface.importedRehome (np.submodule { });
        gen = interface.importedRehome (t.attrsOf t.str);
        tree = interface.importedRehome tree;
      };
      expected = {
        placeholder = null;
        uniq = null;
        submodule = null;
        gen = null;
        tree = null;
      };
    };
  };
}
