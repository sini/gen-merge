# The KEY WALK and the MINTING of nested trees as `nta` children (den-hoag-n6dh7 Unit 2.4, first
# half; spec `2026-09-22-gen-scope-nta-spec.md` v9.1 item 2, cells U2-g and U2-k): which positions
# of a root evaluation's option values are nested trees, the Unit 1 identifier each is minted
# under, and the addresses of the definitions each one's seed carries.
#
# In this state a root evaluation MINTS its nested positions and the nested trees are still
# evaluated by their types' called folds, so every value below is today's. What is read is the
# evaluation's node set (`_evaluation`, `evalModuleTreeExposed`), and what enumerating it forces.
{
  genMerge,
  genMergeCore,
  genScope,
  interface,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib.types;
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;

  evalExposed = modules: genMergeCore.evalModuleTreeExposed { inherit modules; };
  # The ROOT's own nested children, as `childrenOf` reads them, off the root's own product rather than
  # the whole node set: since placement (Unit 2.4) a child is a host in turn, so enumerating every
  # node evaluates every child's definitions to find its own children. A group with no key is absent.
  rootChildrenOf =
    r:
    let
      groups = (r._evaluation.get "module-tree" "nta-children").nested;
    in
    builtins.mapAttrs (_: builtins.attrNames) (
      builtins.removeAttrs groups (builtins.filter (g: groups.${g} == { }) (builtins.attrNames groups))
    );
  # The minted NESTED children of a root evaluation, as `{ <group> = [ <key> … ]; }`, read off its node
  # set and decoded. Enumerating is what forces every group's key set. Scoped to the `nested` family:
  # every tree also mints its module graph (`modules`, den-hoag-470xp), which is not this suite's
  # subject.
  childrenOf =
    r:
    let
      decoded = builtins.filter (d: d != null && d.name == "nested") (
        map genScope.decodeNta r._evaluation.allNodeIds
      );
    in
    builtins.mapAttrs (_: ds: map (d: d.key) ds) (builtins.groupBy (d: d.group) decoded);
  seedOf =
    r: group: key:
    (r._evaluation.node (
      genScope.mintNtaId {
        host = "module-tree";
        name = "nested";
        group = group;
        key = key;
      }
    )).decls.seed;
  addressesOf =
    r: group: key:
    map (e: e.address.at) (seedOf r group key);
  valuesOf =
    r: group: key:
    map (e: e.value) (seedOf r group key);

  sub = t.submodule { options.x = gm.mkOption { type = t.int; }; };
  named = t.submodule (
    { name, ... }:
    {
      options.n = gm.mkOption {
        type = t.str;
        default = name;
      };
    }
  );
  host =
    type: defs:
    [
      { options.o = gm.mkOption { inherit type; }; }
    ]
    ++ map (d: { config.o = d; }) defs;
in
{
  # U2-g's key clauses. One child per nesting position, keyed by the POSITION path, minted with
  # Unit 1's identifier: the host's coordinates, the NTA `nested`, the option path as the group.
  flake.tests.nesting-keys-children = {
    # Two definitions of one list element each: the names are nixpkgs `listOf`'s segments, one per
    # definition, and the two elements are two children, `[ d i ]` apart.
    test-two-definitions-of-one-list-element-each-are-two-children = {
      expr =
        let
          r = evalExposed (
            host (t.listOf named) [
              [ { } ]
              [ { } ]
            ]
          );
        in
        {
          names = map (e: e.n) r.config.o;
          children = childrenOf r;
        };
      expected = {
        names = [
          "[definition 1-entry 1]"
          "[definition 2-entry 1]"
        ];
        children."[\"o\"]" = [
          "[0,0]"
          "[1,0]"
        ];
      };
    };
    # The control: one definition of two elements, named as nixpkgs `listOf` names them.
    test-one-definition-of-two-list-elements-is-two-children-by-index = {
      expr =
        let
          r = evalExposed (
            host (t.listOf named) [
              [
                { }
                { }
              ]
            ]
          );
        in
        {
          names = map (e: e.n) r.config.o;
          children = childrenOf r;
        };
      expected = {
        names = [
          "[definition 1-entry 1]"
          "[definition 1-entry 2]"
        ];
        children."[\"o\"]" = [
          "[0,0]"
          "[0,1]"
        ];
      };
    };
    test-an-attribute-container-keys-its-children-by-name = {
      expr = childrenOf (
        evalExposed (
          host (t.attrsOf sub) [
            {
              a.x = 1;
              b.x = 2;
            }
          ]
        )
      );
      expected."[\"o\"]" = [
        "[\"a\"]"
        "[\"b\"]"
      ];
    };
    # A tree typed directly on the option is the position `[ ]`, with no definitions as with some.
    test-a-tree-typed-on-the-option-is-the-empty-position-defined-or-not = {
      expr = {
        defined = childrenOf (evalExposed (host sub [ { x = 1; } ]));
        undefined = childrenOf (evalExposed (host sub [ ]));
        undefinedSeed = seedOf (evalExposed (host sub [ ])) "[\"o\"]" "[]";
      };
      expected = {
        defined."[\"o\"]" = [ "[]" ];
        undefined."[\"o\"]" = [ "[]" ];
        undefinedSeed = [ ];
      };
    };
    # `attrsOf`'s key set drops a key whose every definition is discharged, and the walk reads that
    # key set: a discharged key is not a child.
    test-a-discharged-key-is-not-a-child = {
      expr = childrenOf (
        evalExposed (
          host (t.attrsOf sub) [
            {
              a.x = 1;
              b = gm.mkIf false { x = 2; };
            }
          ]
        )
      );
      expected."[\"o\"]" = [ "[\"a\"]" ];
    };
    # A stock nixpkgs container over a gen tree is homed as gen's own where it is bound to its
    # position, so the walk reads gen's split: its positions are children (U2-i's `np-attrs`).
    test-a-stock-foreign-container-is-homed-and-keyed = {
      expr = childrenOf (
        evalExposed (
          host (np.attrsOf sub) [
            {
              a.x = 1;
              b.x = 2;
            }
          ]
        )
      );
      expected."[\"o\"]" = [
        "[\"a\"]"
        "[\"b\"]"
      ];
    };
    test-a-leaf-option-keys-nothing = {
      expr = childrenOf (evalExposed (host t.int [ 3 ]));
      expected = { };
    };
    # A nested position of the freeform plane is a child of the reserved group `freeform`.
    test-a-freeform-plane-position-is-a-child-of-the-freeform-group = {
      expr = childrenOf (evalExposed [
        {
          freeformType = t.lazyAttrsOf sub;
          config.k.x = 1;
        }
      ]);
      expected.freeform = [ "[\"k\"]" ];
    };
    # Every minted identifier decodes to its coordinates and re-mints to itself.
    test-every-minted-identifier-round-trips = {
      expr =
        let
          r = evalExposed (
            host (t.attrsOf sub) [
              {
                a.x = 1;
                b.x = 2;
              }
            ]
          );
          ids = builtins.filter (i: genScope.decodeNta i != null) r._evaluation.allNodeIds;
        in
        {
          # the two families counted apart, so a regression in either shows on its own
          nested = builtins.length (builtins.filter (i: (genScope.decodeNta i).name == "nested") ids);
          modules = builtins.length (builtins.filter (i: (genScope.decodeNta i).name == "modules") ids);
          roundTrips = builtins.all (
            i:
            let
              d = genScope.decodeNta i;
            in
            genScope.mintNtaId d == i
          ) ids;
        };
      expected = {
        nested = 2;
        # two per tree: the root's declaration and definition, and in each nested tree `a` and `b`
        # the submodule's module and the one definition it receives
        modules = 6;
        roundTrips = true;
      };
    };
  };

  # A seed is the ADDRESSES of the definitions its tree's fold receives: into the host attribute
  # `definitions` (one list per group, the option's own definitions after discharge, priority and
  # order), then the definition's index, `value`, and the steps down to the position.
  flake.tests.nesting-keys-seeds = {
    test-a-seed-addresses-each-definition-of-its-position = {
      expr =
        let
          r = evalExposed (
            host (t.attrsOf sub) [
              { a.x = 1; }
              { a.y = 2; }
            ]
          );
        in
        {
          at = addressesOf r "[\"o\"]" "[\"a\"]";
          values = valuesOf r "[\"o\"]" "[\"a\"]";
        };
      expected = {
        at = [
          [
            0
            "value"
            "a"
          ]
          [
            1
            "value"
            "a"
          ]
        ];
        values = [
          { y = 2; }
          { x = 1; }
        ];
      };
    };
    # The element's own discharge steps are part of its address, and the priority pass drops what
    # it drops for the fold.
    test-a-seed-carries-the-discharge-path-and-the-priority-pass = {
      expr =
        let
          r = evalExposed (
            host (t.attrsOf sub) [
              { a = gm.mkIf true { x = 1; }; }
              { a = gm.mkForce { x = 2; }; }
            ]
          );
        in
        {
          at = addressesOf r "[\"o\"]" "[\"a\"]";
          values = valuesOf r "[\"o\"]" "[\"a\"]";
          value = r.config.o.a.x;
        };
      expected = {
        at = [
          [
            0
            "value"
            "a"
            "content"
          ]
        ];
        values = [ { x = 2; } ];
        value = 2;
      };
    };
    test-a-list-element-is-addressed-by-its-index-in-its-definition = {
      expr = addressesOf (evalExposed (
        host (t.listOf sub) [
          [
            { x = 1; }
            { x = 2; }
          ]
        ]
      )) "[\"o\"]" "[0,1]";
      expected = [
        [
          0
          "value"
          1
        ]
      ];
    };
  };

  # U2-k's forcing arms, at the built rev, with the key set of every group of the host FORCED (its
  # own children enumerated) before the value is read. A sibling definition that would abort if forced
  # is the trace: the walk over a LAZY container keys every position without reading it, and the
  # union's member is never chosen there (S1 (ii)); under `attrsOf` the key set already reads it.
  flake.tests.nesting-keys-forcing =
    let
      enumerated =
        r:
        builtins.seq (builtins.deepSeq (rootChildrenOf r) null) builtins.deepSeq r.config.o.foo
          r.config.o.foo;
      sibling =
        type:
        evalExposed (
          host type [
            {
              foo.x = 1;
              bar = throw "sibling forced";
            }
          ]
        );
    in
    {
      test-a-lazy-union-position-keys-without-forcing-its-sibling = {
        expr = enumerated (sibling (t.lazyAttrsOf (t.either t.str sub)));
        expected.x = 1;
      };
      # The control: `attrsOf`'s key set forces each element's definition, as its fold does.
      test-a-strict-container-forces-its-sibling-to-key-it = {
        expr = refused (enumerated (sibling (t.attrsOf (t.either t.str sub))));
        expected = true;
      };
      test-a-lazy-tree-position-keys-without-forcing-its-sibling = {
        expr = enumerated (sibling (t.lazyAttrsOf sub));
        expected.x = 1;
      };
      # `o.foo = config.o.bar` under a lazy container: the alias answers, because keying the group
      # reads no position's definition.
      test-an-alias-between-lazy-positions-answers-with-its-group-keyed = {
        expr = enumerated (evalExposed [
          (
            { config, ... }:
            {
              options.o = gm.mkOption { type = t.lazyAttrsOf sub; };
              config.o.foo = config.o.bar;
              config.o.bar.x = 5;
            }
          )
        ]);
        expected.x = 5;
      };
      test-a-nullable-tree-under-a-lazy-container-is-keyed-without-reading-it = {
        expr = rootChildrenOf (sibling (t.lazyAttrsOf (t.nullOr sub)));
        expected."[\"o\"]" = [
          "[\"bar\"]"
          "[\"foo\"]"
        ];
      };
    };

  # S1 class (a), arm (v) (den-hoag-9d80v): a container that keys its elements by reading them,
  # holding nested trees, under `lazyAttrsOf`, is a CONTAINER NODE at the lazy position, whose own
  # `container` group keys its elements over its own definitions only, so no sibling is read to key
  # it. Below a step under any other over-approximating container it is a container node too
  # (`nesting-keys-stepped-container`). A lazy container under an exact one is keyed.
  flake.tests.nesting-keys-lazy-over-strict = {
    test-a-strict-container-of-trees-under-a-lazy-one-is-a-container-node = {
      expr = childrenOf (evalExposed (host (t.lazyAttrsOf (t.attrsOf sub)) [ { j.k.x = 1; } ]));
      expected = {
        "[\"o\"]" = [ "[\"j\"]" ];
        container = [ "[\"k\"]" ];
      };
    };
    test-a-container-node-keys-without-forcing-its-sibling = {
      expr =
        let
          r = evalExposed (
            host (t.lazyAttrsOf (t.attrsOf sub)) [
              {
                foo.a.x = 1;
                bar = throw "sibling forced";
              }
            ]
          );
        in
        builtins.seq (builtins.deepSeq (rootChildrenOf r) null) r.config.o.foo;
      expected.a.x = 1;
    };
    # The control: under an exact container the sibling is read to key it.
    test-a-strict-container-of-trees-under-a-strict-one-forces-its-sibling = {
      expr = refused (
        rootChildrenOf (
          evalExposed (
            host (t.attrsOf (t.attrsOf sub)) [
              {
                foo.a.x = 1;
                bar = throw "sibling forced";
              }
            ]
          )
        )
      );
      expected = true;
    };
    test-a-lazy-container-of-trees-under-a-strict-one-is-keyed = {
      expr = childrenOf (evalExposed (host (t.attrsOf (t.lazyAttrsOf sub)) [ { j.k.x = 1; } ]));
      expected."[\"o\"]" = [ "[\"j\",\"k\"]" ];
    };
  };

  # den-hoag-t1j4z Build 1 (ADR-0039, the serve half): a container that keys its elements by reading
  # them, holding nested trees, under a container that ADDS NO STEP (`unique`, `coercedTo`), at the
  # walk's own root (an option's position, or a container node's), is walked as the root is and serves
  # nixpkgs' value. The expected values are nixpkgs' own, read off `lib.evalModules` over the same
  # declaration in nixpkgs' types. Below a step the refusal stands (`testsError.nesting-keys`).
  flake.tests.nesting-keys-step-free-wrapper =
    let
      cfgOf = modules: (gm.evalModuleTree { } modules).config.o;
      opt = type: { options.o = gm.mkOption { inherit type; }; };
    in
    {
      test-an-attrs-container-of-trees-under-unique-serves = {
        expr = cfgOf (host (np.uniq (t.attrsOf sub)) [ { j.x = 1; } ]);
        expected.j.x = 1;
      };
      test-a-list-of-trees-under-coercedTo-serves-the-coerced-definition = {
        expr = cfgOf (
          host (np.coercedTo np.str (_: [ { x = 2; } ]) (t.listOf sub)) [
            [ { x = 1; } ]
            "s"
          ]
        );
        # nixpkgs' order: the later module's definition first
        expected = [
          { x = 2; }
          { x = 1; }
        ];
      };
      test-a-lazy-container-of-trees-under-unique-serves = {
        expr = cfgOf (host (np.uniq (t.lazyAttrsOf sub)) [ { j.x = 1; } ]);
        expected.j.x = 1;
      };
      # A union holding a container member, at the wrapper's root, keys the member its `choose` takes,
      # as at any root.
      test-a-unions-container-member-under-unique-serves = {
        expr = cfgOf (host (np.uniq (t.either (t.attrsOf sub) t.str)) [ { j.x = 1; } ]);
        expected.j.x = 1;
      };
      test-a-unions-string-member-under-unique-serves-beside-a-nested-sibling = {
        expr =
          let
            o = cfgOf (
              host (t.attrsOf (np.uniq (t.either (t.attrsOf sub) t.str))) [
                {
                  p = "s";
                  q.j.x = 5;
                }
              ]
            );
          in
          [
            o.p
            o.q.j.x
          ];
        expected = [
          "s"
          5
        ];
      };
      # Enumerating the node set forces the group's key walk: the string definition takes the union's
      # string member, so no container member is walked over it.
      test-a-unions-string-definition-under-unique-enumerates-its-node-set = {
        expr =
          let
            ids =
              (evalExposed (host (np.uniq (t.either (t.attrsOf sub) t.str)) [ "s" ]))._evaluation.allNodeIds;
          in
          (builtins.tryEval (builtins.deepSeq ids ids)).success;
        expected = true;
      };
      # The sibling-forcing reason, at the root: a sibling's key set reads the read element's nested
      # config. nixpkgs keys a lazy container without reading it, and so does the walk.
      test-a-siblings-key-set-reading-the-read-tree-serves-under-unique = {
        expr =
          (gm.evalModuleTree { } [
            (opt (np.uniq (t.lazyAttrsOf (t.attrsOf sub))))
            (
              { config, ... }:
              {
                config.o = {
                  foo.k.x = 1;
                  bar = if config.o.foo.k.x == 1 then { k.x = 2; } else { };
                };
              }
            )
          ]).config.o.foo.k.x;
        expected = 1;
      };
    };

  # den-hoag-t1j4z Case B (ADR-0039, the serve half): a container that keys its elements by reading
  # them, holding nested trees, BELOW A STEP under an over-approximating container, is a CONTAINER
  # NODE (S1 arm (v) generalized), and its own threaded fold reads it off its node wherever the walk
  # minted one: the evaluation's accessor states what the walk minted (`readsMintedNode`,
  # den-hoag-o3oz5). Three such containers: `lazyAttrsOf` under another name, whose fold marks its
  # elements itself; a consumer's `defineType` container, whose fold sets no mark; and nixpkgs' lazy
  # `attrsWith` under `uniq`, whose threaded fold is the import's. Only the second and third
  # discriminate the fold's half (`overRoot` reads every node a walk mints, through its own mark).
  # The expected values are nixpkgs' own, read off `lib.evalModules` mounting the same declaration.
  flake.tests.nesting-keys-stepped-container =
    let
      cfgOf = modules: (gm.evalModuleTree { } modules).config.o;
      overRoot = e: t.lazyAttrsOf e // { name = "overRoot"; };
      # A consumer's stepped container through gen's `defineType` door, as gen-aspects'
      # `aspectsRootWith` is built: each element re-rooted at `[ k ]`, folded through the threaded
      # twin over the accessor it was handed, extended by the key. `acc` is what the consumer does to
      # that accessor before handing it on.
      stepRoot = stepRootWith (ev: ev);
      stepRootWith =
        acc: elemType:
        let
          split =
            _loc: defs:
            map (k: {
              step = [ k ];
              loc = [ k ];
              defs = builtins.concatMap (
                d:
                nixpkgsLib.optional (d.value ? ${k}) {
                  inherit (d) file;
                  value = d.value.${k};
                }
              ) defs;
              type = elemType;
            }) (builtins.attrNames (builtins.foldl' (acc: d: acc // d.value) { } defs));
          foldWith =
            foldElement: loc: defs:
            builtins.listToAttrs (
              map (e: {
                name = builtins.head e.step;
                value = foldElement e;
              }) (split loc defs)
            );
        in
        t.defineType {
          name = "stepRoot";
          inherit elemType split;
          carries.element = elemType;
          recarry = c: stepRootWith acc c.element;
          substructure = {
            declares = prefix: elemType.getSubOptions (prefix ++ [ "<name>" ]);
            modules = elemType.getSubModules or null;
            rebuild =
              m: stepRootWith acc (if elemType ? substSubModules then elemType.substSubModules m else elemType);
          };
          mergeDefs = {
            __functor = _: foldWith (e: gm.mergeDefs e.loc e.type e.defs);
            threaded =
              ev:
              foldWith (
                e:
                gm.mergeDefs e.loc (
                  if builtins.isAttrs e.type && e.type ? mergeDefs.threaded then
                    e.type
                    // {
                      mergeDefs = e.type.mergeDefs.threaded (acc (ev // { position = ev.position ++ e.step; }));
                    }
                  else
                    e.type
                ) e.defs
              );
          };
        };
      # The sibling-forcing reason: `bar`'s key set reads the read element's nested tree.
      keysDep = type: [
        { options.o = gm.mkOption { inherit type; }; }
        (
          { config, ... }:
          {
            config.o = {
              foo.k.x = 1;
              bar = if config.o.foo.k.x == 1 then { k.x = 2; } else { };
            };
          }
        )
      ];
    in
    {
      # Enumerating the node set keys the inner container at its node, and the value is nixpkgs'.
      test-a-strict-container-of-trees-below-a-step-is-a-container-node-and-serves = {
        expr =
          let
            r = evalExposed (host (overRoot (t.attrsOf sub)) [ { j.k.x = 1; } ]);
          in
          builtins.seq (builtins.deepSeq (childrenOf r) null) r.config.o;
        expected.j.k.x = 1;
      };
      test-a-strict-container-of-trees-below-a-step-serves-without-reading-its-sibling = {
        expr =
          (cfgOf (
            host (overRoot (t.attrsOf sub)) [
              {
                j.k.x = 1;
                bar = throw "sibling read";
              }
            ]
          )).j.k.x;
        expected = 1;
      };
      test-a-siblings-key-set-reading-the-read-tree-below-a-step-serves = {
        expr = (gm.evalModuleTree { } (keysDep (overRoot (t.attrsOf sub)))).config.o.foo.k.x;
        expected = 1;
      };
      test-a-unions-strict-container-below-a-step-serves = {
        expr = cfgOf (host (overRoot (t.either (t.attrsOf sub) t.str)) [ { p.a.x = 1; } ]);
        expected.p.a.x = 1;
      };
      test-a-lazy-container-of-trees-below-a-step-serves = {
        expr = cfgOf (host (overRoot (t.lazyAttrsOf sub)) [ { j.k.x = 1; } ]);
        expected.j.k.x = 1;
      };
      test-a-list-of-trees-below-a-step-serves = {
        expr = cfgOf (host (overRoot (t.listOf sub)) [ { j = [ { x = 1; } ]; } ]);
        expected.j = [ { x = 1; } ];
      };
      # THE FOLD'S HALF, under a consumer's container whose fold sets no mark: the element's own
      # fold reads the node the walk minted.
      test-a-consumer-containers-strict-element-serves-beside-a-key-dependent-sibling = {
        expr = (gm.evalModuleTree { } (keysDep (stepRoot (t.attrsOf sub)))).config.o.foo.k.x;
        expected = 1;
      };
      test-a-consumer-containers-list-element-serves = {
        expr = cfgOf (host (stepRoot (t.listOf sub)) [ { j = [ { x = 1; } ]; } ]);
        expected.j = [ { x = 1; } ];
      };
      test-a-consumer-containers-union-element-serves = {
        expr = cfgOf (
          host (stepRoot (t.either (t.attrsOf sub) t.str)) [
            {
              p.a.x = 1;
              q = "s";
            }
          ]
        );
        expected = {
          p.a.x = 1;
          q = "s";
        };
      };
      test-a-consumer-containers-nullable-element-serves = {
        expr = cfgOf (
          host (stepRoot (t.nullOr (t.attrsOf sub))) [
            {
              p.a.x = 1;
              q = null;
            }
          ]
        );
        expected = {
          p.a.x = 1;
          q = null;
        };
      };
      # THE FOREIGN HALF: nixpkgs' lazy `attrsWith` (a placeholder, so not re-homed) under `uniq`; its
      # threaded fold is the import's, and the gen element's own fold reads its node. A sibling whose
      # key set reads the read tree is served too, since the foreign split is keyed by the chain's
      # stated step (`nesting-keys-foreign-chain`, den-hoag-fozin).
      test-a-foreign-lazy-containers-strict-element-serves-under-unique = {
        expr = cfgOf (
          host
            (np.uniq (
              np.attrsWith {
                elemType = t.attrsOf sub;
                lazy = true;
                placeholder = "p";
              }
            ))
            [
              {
                foo.k.x = 1;
                bar.k.x = 2;
              }
            ]
        );
        expected = {
          foo.k.x = 1;
          bar.k.x = 2;
        };
      };
      # THE ACCESSOR'S QUERY IS OUT OF BAND: a consumer accessor that adds its own fields to the site
      # it forwards (here `minted`, the query's natural name) is conformant, and nixpkgs serves it;
      # the walk's answer rides on a key reserved to gen-merge, so the fields cannot collide.
      test-a-consumer-accessor-adding-its-own-site-fields-serves = {
        expr =
          (gm.evalModuleTree { } (
            keysDep (
              stepRootWith (ev: ev // { child = site: ev.child (site // { minted = true; }); }) (t.attrsOf sub)
            )
          )).config.o.foo.k.x;
        expected = 1;
      };
      # A RECORD RENAMED AFTER IT IS BUILT (`// { name = … }`) reads as another type to the walk, and
      # the fold reads what the walk minted, never what the record was built as. A consumer
      # container renamed `attrsOf` is keyed exactly, so its elements fold inline, as at base.
      test-a-consumer-container-renamed-after-it-is-built-serves-as-the-walk-keyed-it = {
        expr =
          (cfgOf (
            host (stepRoot (t.attrsOf sub) // { name = "attrsOf"; }) [
              {
                foo.k.x = 1;
                bar.k.x = 2;
              }
            ]
          )).foo.k.x;
        expected = 1;
      };
      # An `attrsOf` renamed is keyed over-approximately, so its inner container is a node, which
      # the inner fold reads although no mark was set.
      test-an-attrs-container-renamed-after-it-is-built-reads-its-elements-nodes = {
        expr =
          (cfgOf (
            host (t.attrsOf (t.attrsOf sub) // { name = "renamed"; }) [
              {
                foo.k.x = 1;
                bar.k.x = 2;
              }
            ]
          )).foo.k.x;
        expected = 1;
      };
    };

  # den-hoag-fozin (ADR-0039, the serve half; ADR-0025 item 1): a FOREIGN chain whose only step is a
  # lazy `attrsWith` (any placeholder), bare or under step-free foreign wrappers (`unique`,
  # `coercedTo`), above a gen element that may nest, is keyed by the step its functors state: the
  # split reads the fold's attribute names and an element's capture site only when that element is
  # read, so a sibling whose key set reads the read tree is never forced to key it. The expected
  # values are nixpkgs' own, read off `lib.evalModules` mounting the same declaration.
  flake.tests.nesting-keys-foreign-chain =
    let
      cfgOf = modules: (gm.evalModuleTree { } modules).config.o;
      aw =
        e:
        np.attrsWith {
          elemType = e;
          lazy = true;
          placeholder = "p";
        };
      keysDep = type: [
        { options.o = gm.mkOption { inherit type; }; }
        (
          { config, ... }:
          {
            config.o = {
              foo.k.x = 1;
              bar = if config.o.foo.k.x == 1 then { k.x = 2; } else { };
            };
          }
        )
      ];
      # a lazy `attrsWith` whose merge rearranges its result at the stated depth (`g` maps the stock
      # result), its rebuild included
      reshapeOf =
        g: a:
        a
        // {
          merge = loc: defs: g (a.merge loc defs);
          substSubModules =
            m:
            let
              r = a.substSubModules m;
            in
            r // { merge = loc: defs: g (r.merge loc defs); };
        };
      two = [
        {
          foo.k.x = 1;
          bar.k.x = 2;
        }
      ];
      alias = type: [
        { options.o = gm.mkOption { inherit type; }; }
        (
          { config, ... }:
          {
            config.o = {
              foo.k.x = 1;
              bar = config.o.foo;
            };
          }
        )
      ];
    in
    {
      test-a-bare-placeholder-attrsWith-serves-a-key-dependent-sibling = {
        expr = (cfgOf (keysDep (aw (t.attrsOf sub)))).foo.k.x;
        expected = 1;
      };
      test-a-placeholder-attrsWith-under-unique-serves-a-key-dependent-sibling = {
        expr = (cfgOf (keysDep (np.uniq (aw (t.attrsOf sub))))).foo.k.x;
        expected = 1;
      };
      test-a-stock-lazy-attrsOf-under-coercedTo-serves-an-alias-sibling = {
        expr =
          (cfgOf (alias (np.coercedTo np.str (_: throw "unused") (np.lazyAttrsOf (t.attrsOf sub))))).foo.k.x;
        expected = 1;
      };
      # a step-free foreign wrapper BELOW the step as well: the capture site is still one key down
      test-a-wrapper-below-the-step-serves-a-key-dependent-sibling = {
        expr = (cfgOf (keysDep (np.uniq (aw (np.uniq (t.attrsOf sub)))))).foo.k.x;
        expected = 1;
      };
      # den-hoag-t1j4z OQ2(a), dissolved by Case B (gen-merge f26e1c8): the bare chain's plain read
      test-a-bare-placeholder-attrsWith-plain-read-serves = {
        expr = cfgOf (
          host (aw (t.attrsOf sub)) [
            {
              foo.k.x = 1;
              bar.k.x = 2;
            }
          ]
        );
        expected = {
          foo.k.x = 1;
          bar.k.x = 2;
        };
      };
      # the key survives where every definition of its element is discharged away: nixpkgs' lazy
      # `attrsWith` keeps it, at the element's empty value
      test-a-discharged-element-keeps-its-key-at-the-empty-value = {
        expr = cfgOf (
          host (np.uniq (aw (t.attrsOf sub))) [
            {
              foo.k.x = 1;
              bar = gm.mkIf false { k.x = 2; };
            }
          ]
        );
        expected = {
          foo.k.x = 1;
          bar = { };
        };
      };
      # den-hoag-fozin C1: the run, not the functor, says which tree sits at which key. A merge that
      # duplicates or drops a key's tree serves nixpkgs' value; one that moves a tree to another key
      # is refused by name (`testsError.nesting-keys-foreign-chain`).
      test-a-merge-duplicating-a-keys-tree-serves-nixpkgs-value = {
        expr =
          (cfgOf (host (np.uniq (reshapeOf (r: r // { bar = r.foo; }) (aw (t.attrsOf sub)))) two)).bar.k.x;
        expected = 1;
      };
      # a merge whose result is not an attrset is off the stated step's domain and keeps the eager
      # walk, so it serves nixpkgs' value rather than abort on the key read
      test-a-merge-returning-a-list-of-the-trees-serves-nixpkgs-value = {
        expr =
          (builtins.head (
            cfgOf (
              host (np.uniq (
                reshapeOf (r: [
                  r.foo
                  r.bar
                ]) (aw (t.attrsOf sub))
              )) two
            )
          )).k.x;
        expected = 1;
      };
      test-a-merge-dropping-a-keys-tree-serves-nixpkgs-value = {
        expr = cfgOf (
          host (np.uniq (reshapeOf (r: builtins.removeAttrs r [ "bar" ]) (aw (t.attrsOf sub)))) two
        );
        expected = {
          foo.k.x = 1;
        };
      };
    };

  # den-hoag-rlskz (ADR-0039, the serve half; ADR-0025 item 1): a FOREIGN chain whose lazy `attrsWith`
  # holds, at each key, a record that is itself a chain (a second container step: `lazyAttrsOf`,
  # `attrsOf`, `listOf`, `nullOr`) is keyed one key at a time: each key is a container node whose own
  # walk is that record's, read off the fold's result at that key only, so a sibling whose key set or
  # `mkIf` reads the read tree is never forced to key it. The expected values are nixpkgs' own, read
  # off `lib.evalModules` mounting the same declaration.
  # den-hoag-rlskz: a foreign chain's node keys its elements in the regime of the record its step
  # states (`interface.keysExactly`). Below `lazyAttrsOf`, a stock `attrsOf` keys exactly, so its gen
  # `attrsOf` elements are keyed over-approximately inline in the node's own group, as gen's own
  # `attrsOf (attrsOf sub)` keys them: the node holds trees, and no second node is minted per key.
  flake.tests.nesting-keys-foreign-chain-node-regime =
    let
      r = genMergeCore.evalModuleTreeExposed {
        modules = [
          { options.o = gm.mkOption { type = np.uniq (np.lazyAttrsOf (np.attrsOf (t.attrsOf sub))); }; }
          { config.o.foo.j.k.x = 1; }
        ];
      };
      nodeId = genScope.mintNtaId {
        host = "module-tree";
        name = "nested";
        group = "[\"o\"]";
        key = "[\"foo\"]";
      };
      modesAt =
        id: group: builtins.mapAttrs (_: p: p.mode) (r._evaluation.get id "positions").nested.${group};
    in
    {
      test-a-node-over-an-exact-stock-container-holds-trees-not-nodes = {
        expr = {
          root = modesAt "module-tree" "[\"o\"]";
          node = modesAt nodeId "container";
          value = r.config.o.foo.j.k.x;
        };
        expected = {
          root."[\"foo\"]" = "container";
          node."[\"j\",\"k\"]" = "called";
          value = 1;
        };
      };
    };

  flake.tests.nesting-keys-foreign-chain-nested =
    let
      cfgOf = modules: (gm.evalModuleTree { } modules).config.o;
      aw =
        e:
        np.attrsWith {
          elemType = e;
          lazy = true;
          placeholder = "p";
        };
      # `bar`'s key set reads the read tree, below the chain's second step (`d` builds a key's value)
      keysDep = type: d: read: [
        { options.o = gm.mkOption { inherit type; }; }
        (
          { config, ... }:
          {
            config.o = {
              foo = d 1;
              bar = if read config.o.foo == 1 then d 2 else { };
            };
          }
        )
      ];
      inJ = v: { j.k.x = v; };
      readJ = x: x.j.k.x;
    in
    {
      test-a-lazy-step-over-a-lazy-attrsOf-under-unique-serves-a-key-dependent-sibling = {
        expr =
          readJ
            (cfgOf (keysDep (np.uniq (np.lazyAttrsOf (np.lazyAttrsOf (t.attrsOf sub)))) inJ readJ)).foo;
        expected = 1;
      };
      test-a-lazy-step-over-an-attrsOf-under-unique-serves-a-key-dependent-sibling = {
        expr =
          readJ
            (cfgOf (keysDep (np.uniq (np.lazyAttrsOf (np.attrsOf (t.attrsOf sub)))) inJ readJ)).foo;
        expected = 1;
      };
      test-a-lazy-step-over-a-listOf-under-unique-serves-a-key-dependent-sibling = {
        expr =
          (builtins.head
            (cfgOf (
              keysDep (np.uniq (np.lazyAttrsOf (np.listOf (t.attrsOf sub)))) (v: [ { k.x = v; } ]) (
                x: (builtins.head x).k.x
              )
            )).foo
          ).k.x;
        expected = 1;
      };
      test-a-lazy-step-over-a-nullOr-under-unique-serves-a-key-dependent-sibling = {
        expr =
          (cfgOf (
            keysDep (np.uniq (np.lazyAttrsOf (np.nullOr (t.attrsOf sub)))) (v: { k.x = v; }) (x: x.k.x)
          )).foo.k.x;
        expected = 1;
      };
      test-a-bare-placeholder-attrsWith-over-a-lazy-attrsOf-serves-a-key-dependent-sibling = {
        expr = readJ (cfgOf (keysDep (aw (np.lazyAttrsOf (t.attrsOf sub))) inJ readJ)).foo;
        expected = 1;
      };
      # three steps, under `coercedTo`: each lazy step is a level of nodes
      test-three-steps-under-coercedTo-serve-a-key-dependent-sibling = {
        expr =
          (cfgOf (
            keysDep (np.coercedTo np.str (_: throw "unused") (
              np.lazyAttrsOf (np.lazyAttrsOf (np.attrsOf (t.attrsOf sub)))
            )) (v: { j.i.k.x = v; }) (x: x.j.i.k.x)
          )).foo.j.i.k.x;
        expected = 1;
      };
      # one step below the node: an inner LAZY step keys its own keys where read, so a second key
      # that is `mkIf` on the read tree serves (nixpkgs forces it only where it is read)
      test-an-inner-lazy-step-serves-an-mkIf-sibling-below-the-node = {
        expr =
          readJ
            (cfgOf [
              { options.o = gm.mkOption { type = np.uniq (np.lazyAttrsOf (np.lazyAttrsOf (t.attrsOf sub))); }; }
              (
                { config, ... }:
                {
                  config.o.foo = {
                    j.k.x = 1;
                    i = gm.mkIf (config.o.foo.j.k.x == 1) { k.x = 2; };
                  };
                }
              )
            ]).foo;
        expected = 1;
      };
      # the whole value, every key and element, and a key whose every definition is discharged away
      test-the-whole-value-of-a-two-step-chain-is-nixpkgs-value = {
        expr = cfgOf (
          host (np.uniq (np.lazyAttrsOf (np.attrsOf (t.attrsOf sub)))) [
            {
              foo.j.k.x = 1;
              foo.i.k.x = 3;
              bar.j.k.x = 2;
              baz = gm.mkIf false { j.k.x = 4; };
            }
          ]
        );
        expected = {
          foo.j.k.x = 1;
          foo.i.k.x = 3;
          bar.j.k.x = 2;
          baz = { };
        };
      };
      # the whole value under siblings that add keys at the node's exact level and at the gen level
      # below it, `mkIf` on a sibling's tree (a whole definition and an inner key), a key whose only
      # definition discharges away, and `baz`, whose key set reads `foo`'s tree (the class trigger):
      # the node keys every key nixpkgs keeps, and none it drops
      test-the-whole-value-under-key-adding-and-mkIf-siblings-is-nixpkgs-value = {
        expr =
          let
            ab = t.submodule {
              options.a = gm.mkOption {
                type = t.int;
                default = 0;
              };
              options.b = gm.mkOption {
                type = t.int;
                default = 0;
              };
            };
          in
          cfgOf [
            { options.o = gm.mkOption { type = np.uniq (np.lazyAttrsOf (np.attrsOf (t.attrsOf ab))); }; }
            (
              { config, ... }:
              let
                barA = config.o.bar.j.k.a;
              in
              {
                config.o = {
                  foo = gm.mkMerge [
                    { j.k.a = 1; }
                    { j.k2.a = 2; }
                    { j2.k.a = 3; }
                    (gm.mkIf (barA == 5) { j.k3.a = 4; })
                    { j.k5 = gm.mkIf (barA == 5) { b = 7; }; }
                    { j.k6.a = gm.mkIf false 9; }
                  ];
                  bar.j.k.a = 5;
                  baz = if config.o.foo.j.k.a == 1 then { j.k.a = 8; } else { };
                };
              }
            )
          ];
        expected = {
          foo.j = {
            k = {
              a = 1;
              b = 0;
            };
            k2 = {
              a = 2;
              b = 0;
            };
            k3 = {
              a = 4;
              b = 0;
            };
            k5 = {
              a = 0;
              b = 7;
            };
            k6 = {
              a = 0;
              b = 0;
            };
          };
          foo.j2.k = {
            a = 3;
            b = 0;
          };
          bar.j.k = {
            a = 5;
            b = 0;
          };
          baz.j.k = {
            a = 8;
            b = 0;
          };
        };
      };
      # a head over the lazy step that is not a level's wrapper (`addCheck`, `either`, `nullOr`): the
      # option's own record is keyed by the eager walk, and the lazy step below it is a level of nodes
      test-an-addCheck-head-over-a-lazy-step-over-an-attrsOf-serves-a-key-dependent-sibling = {
        expr =
          readJ
            (cfgOf (keysDep (np.addCheck (aw (np.attrsOf (t.attrsOf sub))) (_: true)) inJ readJ)).foo;
        expected = 1;
      };
      test-an-either-head-over-a-lazy-step-over-a-listOf-serves-a-key-dependent-sibling = {
        expr =
          (builtins.head
            (cfgOf (
              keysDep (np.either (aw (np.listOf (t.attrsOf sub))) np.str) (v: [ { k.x = v; } ]) (
                x: (builtins.head x).k.x
              )
            )).foo
          ).k.x;
        expected = 1;
      };
      test-a-nullOr-head-over-a-lazy-step-over-a-lazy-attrsOf-serves-an-mkIf-sibling = {
        expr =
          readJ
            (cfgOf [
              { options.o = gm.mkOption { type = np.nullOr (aw (np.lazyAttrsOf (t.attrsOf sub))); }; }
              (
                { config, ... }:
                {
                  config.o = {
                    foo.j.k.x = 1;
                    bar = gm.mkIf (config.o.foo.j.k.x == 1) { j.k.x = 2; };
                  };
                }
              )
            ]).foo;
        expected = 1;
      };
    };

  # den-hoag-rlskz: `modules.nix` `keyWalk` reads `interface.keysExactly` inline rather than through a
  # call, so the predicate has two copies. The inline copy is read off the source and evaluated, and
  # the two answer alike on gen's exact containers, its lazy one, and a record stating its own answer.
  flake.tests.nesting-keys-keys-exactly-census =
    let
      lines = builtins.filter builtins.isString (
        builtins.split "\n" (builtins.readFile ../../lib/modules.nix)
      );
      found = builtins.filter (m: m != null) (
        map (builtins.match " *exact = (t[.]keysExactly or .*);") lines
      );
      inline = import (
        builtins.toFile "keys-exactly-inline.nix" "t: let name = t.name or null; in ${builtins.head (builtins.head found)}"
      );
      records = {
        attrsOf = t.attrsOf sub;
        listOf = t.listOf sub;
        nullOr = t.nullOr sub;
        lazyAttrsOf = t.lazyAttrsOf sub;
        statesExact = t.lazyAttrsOf sub // {
          keysExactly = true;
        };
        statesOver = t.attrsOf sub // {
          keysExactly = false;
        };
      };
      answers = {
        attrsOf = true;
        listOf = true;
        nullOr = true;
        lazyAttrsOf = false;
        statesExact = true;
        statesOver = false;
      };
    in
    {
      test-keyWalk-holds-one-inline-copy = {
        expr = builtins.length found;
        expected = 1;
      };
      test-the-binding-and-the-inline-copy-answer-alike = {
        expr = {
          binding = builtins.mapAttrs (_: interface.keysExactly) records;
          inline = builtins.mapAttrs (_: inline) records;
        };
        expected = {
          binding = answers;
          inline = answers;
        };
      };
    };

  # ONE DISCHARGE (den-hoag-i4c0n C1, with L5f's freeform half): the walk reads the fold's own
  # `typeDefs` off the option's merge record, except where forcing that record would meet the "used
  # but not defined" guard. `testsError.nesting-keys` pins the message the guard arm keeps.
  flake.tests.nesting-keys-one-discharge =
    let
      unionUndef = evalExposed [ { options.o = gm.mkOption { type = t.either sub t.str; }; } ];
      subX = t.submodule {
        options.x = gm.mkOption {
          type = t.bool;
          default = true;
        };
      };
      childA =
        modules:
        (evalExposed modules)._evaluation.get (genScope.mintNtaId {
          host = "module-tree";
          name = "nested";
          group = "[\"a\"]";
          key = "[]";
        }) "result";
    in
    {
      # An undefined, default-less union with a nesting member: its child's read refuses (the
      # message is pinned in `testsError`).
      test-an-undefined-union-childs-read-is-refused = {
        expr = refused (
          (unionUndef._evaluation.get (genScope.mintNtaId {
            host = "module-tree";
            name = "nested";
            group = "[\"o\"]";
            key = "[]";
          }) "result").config
        );
        expected = true;
      };
      # The root's product has no `freeform` group where the tree declares no freeform type; before
      # L5f's freeform half it carried `freeform = [ ]`.
      test-a-tree-with-no-freeform-type-mints-no-freeform-group = {
        expr = builtins.mapAttrs (
          _: builtins.attrNames
        ) (unionUndef._evaluation.get "module-tree" "nta-children").nested;
        expected."[\"o\"]" = [ "[]" ];
      };
      # A sibling whose declared TYPE reads `config` through a nested child: the group set is not a
      # function of any option's type, so crossing into `a` does not force `b`'s. A `canNest` filter
      # over the option groups recurses here without end.
      test-a-sibling-typed-through-config-reads-its-nested-child = {
        expr =
          let
            r = evalExposed [
              {
                options.a = gm.mkOption {
                  type = t.submodule {
                    options.x = gm.mkOption {
                      type = t.bool;
                      default = true;
                    };
                  };
                };
              }
              (
                { config, ... }:
                {
                  options.b = gm.mkOption {
                    type = if config.a.x then t.int else t.str;
                    default = 1;
                  };
                }
              )
              { config.a = { }; }
            ];
          in
          {
            inherit (r.config) b;
            ax = r.config.a.x;
          };
        expected = {
          ax = true;
          b = 1;
        };
      };
      # A nesting option whose `readOnly` is read through its own child: the child's read forces no
      # `readOnly`, as the walk before the one discharge forced none.
      test-a-childs-read-forces-no-readonly-written-through-config = {
        expr =
          (childA [
            (
              { config, ... }:
              {
                options.a = gm.mkOption {
                  type = subX;
                  readOnly = config.a.x;
                };
              }
            )
            { config.a = { }; }
          ]).config;
        expected.x = true;
      };
      # A freeform type written through `config`: an option group's child read forces no freeform
      # type, because the freeform group is decided by the key's presence.
      test-a-childs-read-forces-no-freeform-type-written-through-config = {
        expr =
          (childA [
            { options.a = gm.mkOption { type = subX; }; }
            (
              { config, ... }:
              {
                freeformType = if config.a.x then t.attrsOf t.int else t.attrsOf t.str;
              }
            )
            { config.a = { }; }
          ]).config;
        expected.x = true;
      };
    };

  # den-hoag-q6d1z: the read check at a node level serves a key whose tree is another key's, where
  # that key holds its own tree, as nixpkgs does (a duplicate, a graft below a new key).
  flake.tests.nesting-keys-foreign-chain-read-key =
    let
      sub = t.submodule {
        options.a = gm.mkOption {
          type = t.int;
          default = 0;
        };
      };
      cfgOf =
        g: m:
        (gm.evalModuleTree { } [
          {
            options.s = gm.mkOption {
              type = np.uniq (
                let
                  a = np.lazyAttrsOf (np.attrsOf (t.attrsOf sub));
                in
                a
                // {
                  merge = loc: defs: g (a.merge loc defs);
                  substSubModules =
                    m:
                    let
                      r = a.substSubModules m;
                    in
                    r // { merge = loc: defs: g (r.merge loc defs); };
                }
              );
            };
          }
          m
        ]).config.s;
      two = {
        s.foo.j.k.a = 1;
        s.bar.j.k.a = 2;
      };
    in
    {
      test-a-key-serving-a-duplicate-of-another-keys-tree-reads-it = {
        expr = (cfgOf (r: r // { bar = r.foo; }) two).bar.j.k.a;
        expected = 1;
      };
      test-a-key-serving-another-keys-tree-below-a-new-key-reads-it = {
        expr =
          (cfgOf (
            r:
            r
            // {
              foo = r.foo // {
                g = r.bar.j;
              };
            }
          ) two).foo.g.k.a;
        expected = 2;
      };
      # the read reaches no element, so a swapped key's own record serves, as nixpkgs serves it
      test-a-swapped-keys-record-names-its-keys-where-no-element-is-read = {
        expr =
          builtins.attrNames
            (cfgOf (
              r:
              r
              // {
                foo = r.bar;
                bar = r.foo;
              }
            ) two).foo;
        expected = [ "j" ];
      };
    };

  # den-hoag-q6d1z: a read of a node's record that reaches no element forces only what nixpkgs
  # forces for it, so a sibling one lazy step below, `mkIf` on the read tree, is not forced (a
  # stock merge; a strict `attrsOf`, a `listOf` or a `nullOr` over a lazy step).
  flake.tests.nesting-keys-foreign-chain-read-shape =
    let
      sub = t.submodule {
        options.a = gm.mkOption {
          type = t.int;
          default = 0;
        };
      };
      cfgOf =
        rec_: m:
        (gm.evalModuleTree { } [
          {
            options.s = gm.mkOption {
              type = np.uniq (np.lazyAttrsOf (rec_ (np.lazyAttrsOf (t.attrsOf sub))));
            };
          }
          m
        ]).config.s;
      mk =
        { config, ... }:
        {
          s.foo.j.x.k.a = 1;
          s.foo.j.y = gm.mkIf (config.s.foo.j.x.k.a == 1) { k.a = 5; };
        };
    in
    {
      test-a-strict-records-keys-read-without-its-lazy-siblings = {
        expr = builtins.attrNames (cfgOf np.attrsOf mk).foo;
        expected = [ "j" ];
      };
      test-a-lazy-record-below-a-strict-one-names-its-keys-without-forcing-them = {
        expr = builtins.attrNames (cfgOf np.attrsOf mk).foo.j;
        expected = [
          "x"
          "y"
        ];
      };
      test-a-lists-length-read-without-its-lazy-siblings = {
        expr =
          builtins.length
            (cfgOf np.listOf (
              { config, ... }:
              {
                s.foo = [
                  {
                    x.k.a = 1;
                    y = gm.mkIf ((builtins.elemAt config.s.foo 0).x.k.a == 1) { k.a = 5; };
                  }
                ];
              }
            )).foo;
        expected = 1;
      };
      test-a-null-or-records-keys-read-without-its-lazy-siblings = {
        expr =
          builtins.attrNames
            (cfgOf np.nullOr (
              { config, ... }:
              {
                s.foo.x.k.a = 1;
                s.foo.y = gm.mkIf (config.s.foo.x.k.a == 1) { k.a = 5; };
              }
            )).foo;
        expected = [
          "x"
          "y"
        ];
      };
    };

  # den-hoag-q6d1z: the reads of a foreign chain below a node whose merge reshapes what each key
  # holds (`_fixtures/foreign-chain-reshaped.nix`) that serve, each the value nixpkgs serves. Their
  # refused twins are `testsError.nesting-keys-foreign-chain-reshaped`.
  flake.tests.nesting-keys-foreign-chain-reshaped =
    let
      fx = import ./_fixtures/foreign-chain-reshaped.nix { inherit gm nixpkgsLib; };
    in
    nixpkgsLib.mapAttrs'
      (
        n: expected:
        nixpkgsLib.nameValuePair "test-${n}" {
          expr = fx.readOf fx.cells.${n};
          inherit expected;
        }
      )
      {
        swapTopNames = [
          "bar"
          "foo"
        ];
        dupFoo = 1;
        dupKd = 1;
        dupSelf = 1;
        graftBar = 2;
        stockAll = {
          bar = {
            j = {
              k = {
                a = 2;
              };
            };
          };
          baz = {
            j = {
              k = {
                a = 3;
              };
            };
          };
          foo = {
            j = {
              k = {
                a = 1;
              };
            };
          };
        };
        kdStock = 2;
        swap3FooJNames = [ "j" ];
        deep7SwapNames = [ "j" ];
        deep7Stock = 1;
        deep8SwapNames = [ "i" ];
        deep8Stock = 1;
        strictLazyMkTop = [ "foo" ];
        twoNmTop = [
          "bar"
          "foo"
        ];
        stockNNames = [ "k" ];
        dupNNames = [ "k" ];
        rmJNames = [ "j2" ];
        rmJLeaf = 3;
        filtKeyLeaf = 1;
        filtKeyTop = [ "foo" ];
        toListLen = 2;
        toListLeaf = 2;
        addConstLeaf = 9;
        addConstFoo = 1;
        inDupLeaf = 1;
        inDupNames = [
          "j"
          "j2"
        ];
        mapValTop = [
          "bar"
          "foo"
        ];
        catLLen = 3;
        catL1 = 2;
        revLBar0 = 3;
        swapLLen = 2;
        stockLmkLen = 1;
        mixLen = [
          1
          2
        ];
        mix11 = 3;
        mixDropLen = [ 2 ];
        mixDrop01 = 3;
        mixSwapLen = [
          2
          1
        ];
        mixSwap01 = 3;
      };
}
