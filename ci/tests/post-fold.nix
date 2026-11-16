# `types.postFold g e`: a post-fold reshape at any position, `g ∘ fold`. Each cell reads one case
# (`_fixtures/post-fold-cases.nix`) on three planes in the same run: gen's engine (`native`), the same gen declaration
# mounted in nixpkgs' `evalModules` (`mount`), and nixpkgs' own spelling, the `//` override of `e`'s merge (`ref`, the
# twin). Where the planes agree the cell holds all three to one value; where they differ by law (a foreign `addCheck`
# gen enforces and nixpkgs drops, a redeclaration nixpkgs silently serves, the empty fold the override shim leaves
# unreshaped), the cell states each plane's value. The refusals are error-plane cells (`ci/tests-error-post-fold.nix`).
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  planes = nixpkgsLib.genAttrs [ "native" "mount" "ref" ] (
    import ./_fixtures/post-fold-cases.nix { inherit genMerge genTypes nixpkgsLib; }
  );
  # every plane's value of case `c`, forced
  at =
    ps: c:
    nixpkgsLib.genAttrs ps (
      p:
      let
        v = c planes.${p};
      in
      builtins.deepSeq v v
    );
  all3 = at [
    "native"
    "mount"
    "ref"
  ];
  gen2 = at [
    "native"
    "mount"
  ];
  same = v: {
    native = v;
    mount = v;
    ref = v;
  };
  same2 = v: {
    native = v;
    mount = v;
  };
  cell = expr: expected: { inherit expr expected; };
  foo = [ "foo" ];
  added = {
    added.j.k.a = 7;
  };
in
{
  flake.tests.post-fold = {
    # ── nested wrappers: every one serves the twin's value on both engines
    test-postfold-in-postfold-at-the-root = cell (all3 (c: c.wrapNested2)) (same foo);
    test-postfold-in-postfold-nested = cell (all3 (c: c.wrapNested2Nested)) (same foo);
    test-under-nixpkgs-nullor = cell (all3 (c: c.wrapUnderNullOr)) (same foo);
    test-under-gen-nullor = cell (all3 (c: c.wrapUnderGenNullOr)) (same foo);
    test-under-coercedto = cell (all3 (c: c.wrapUnderCoerced)) (same foo);
    test-under-either = cell (all3 (c: c.wrapUnderEither)) (same foo);
    test-under-addcheck = cell (all3 (c: c.wrapAddCheck)) (same foo);
    test-over-gen-containers = cell (all3 (c: c.wrapOverGen)) (same foo);
    test-over-gen-containers-nested = cell (all3 (c: c.wrapOverGenNested)) (same foo);
    test-over-a-leaf = cell (all3 (c: c.wrapLeaf)) (same 2);
    test-over-listof = cell (all3 (c: c.wrapListLeaf)) (same {
      x = [
        3
        2
      ];
    });
    # ── priorities: `foo` is kept iff the winning definition is 1, beside a `bar` that `g` drops; a dropped `g` reads
    # `[ "bar" "foo" ]`, a lost priority `[ ]`
    test-mkforce-wins-before-g = cell (all3 (c: c.prioForce)) (same foo);
    test-mkdefault-loses-before-g = cell (all3 (c: c.prioDefault)) (same foo);
    test-mkoverride-orders-before-g = cell (all3 (c: c.prioOverride)) (same foo);
    test-mkforce-on-the-whole-element = cell (all3 (c: c.prioWhole)) (same [ "bar" ]);
    test-mkif-false-sibling = cell (all3 (c: c.prioIfFalse)) (same foo);
    # ── checks: the post-fold value is not checked, as neither nixpkgs spelling checks it
    test-a-post-fold-value-outside-the-element-is-served =
      cell (all3 (c: c.checkPostValueOutside))
        (same {
          x = "notASet";
        });
    test-a-post-fold-leaf-value-outside-the-leaf-is-served = cell (all3 (c: c.checkLeafPostOutside)) (
      same "str"
    );
    # an `addCheck` over the constructor: nixpkgs drops it (on the twin and mounted), as it drops it with no
    # constructor at all (ADR-0039 "Not covered"); gen enforces it (the error plane)
    test-an-addcheck-over-the-constructor-is-nixpkgs-dropped =
      cell (at [ "mount" "ref" ] (c: c.checkAddCheckRejects))
        {
          mount = foo;
          ref = foo;
        };
    test-an-addcheck-without-the-constructor-is-nixpkgs-dropped-too =
      cell (at [ "mount" "ref" ] (c: c.checkAddCheckRejectsCtl))
        {
          mount = [
            "bar"
            "foo"
          ];
          ref = [
            "bar"
            "foo"
          ];
        };
    # ── the doors under the constructor
    test-types-mkoptiontype = cell (all3 (c: c.doorTypes)) (same 6);
    test-top-level-mkoptiontype = cell (all3 (c: c.doorTop)) (same 6);
    test-a-raw-nixpkgs-mkoptiontype = cell (all3 (c: c.doorRaw)) (same 6);
    test-definetype = cell (gen2 (c: c.doorDefine)) (same2 6);
    # ── identity is the declaring position: the tree `g` moves to `foo` keeps the name `bar` it was declared at
    test-a-moved-tree-keeps-its-declaring-name-nested = cell (all3 (c: c.identDeclPos)) (same {
      a = 2;
      n = "bar";
    });
    test-a-moved-tree-keeps-its-declaring-name-at-the-root = cell (all3 (c: c.identDeclPosRoot)) (same {
      a = 2;
      n = "bar";
    });
    # ── `g` is handed the folded value, never the definitions: a definition rewrite is inexpressible
    test-g-sees-the-folded-set = cell (all3 (c: c.gSeesFolded)) (same {
      x = "set";
    });
    test-g-sees-the-folded-list = cell (all3 (c: c.gSeesFoldedList)) (same "list");
    # ── the empty fold serves `g` of the element's empty value: `apply`'s value at the root and in a submodule
    # option. The override twin leaves it unreshaped (`ref`); it is no nixpkgs value for this constructor, which has no
    # twin, so the oracle is `apply` where an option exists and the law's value nested
    test-the-empty-fold-at-the-root-is-apply =
      cell
        (all3 (c: [
          c.emptyDiscrRootUndef
          c.emptyDiscrRootApplyUndef
        ]))
        {
          native = [
            added
            added
          ];
          mount = [
            added
            added
          ];
          ref = [
            { }
            added
          ];
        };
    test-the-empty-fold-in-a-submodule-option-is-apply =
      cell
        (all3 (c: [
          c.emptyDiscrPfUndefS1
          c.emptyDiscrApplyUndef
        ]))
        {
          native = [
            added
            added
          ];
          mount = [
            added
            added
          ];
          ref = [
            { }
            added
          ];
        };
    test-the-empty-fold-nested-is-g-of-empty = cell (all3 (c: c.emptyDiscrOvr)) {
      native.x = added;
      mount.x = added;
      ref.x = { };
    };
    test-a-g-reading-keys-over-the-empty-fold = cell (all3 (c: c.emptyNested)) (same {
      x = { };
    });
    # ── identity regime: the element alone mints; one `g` binding is one construction (another `g` refuses: the error plane)
    test-the-element-alone-mints = cell (gen2 (c: c.idOfElementCtl)) (same2 true);
    test-one-g-binding-is-typeeq = cell (gen2 (c: c.typeEqBinding)) (same2 true);
    # ── poison stays lazy
    test-an-unread-throwing-definition-stays-lazy = cell (all3 (c: c.poisonThrowUnread)) (same 1);
    test-an-unread-aborting-definition-stays-lazy = cell (all3 (c: c.poisonAbortUnread)) (same 1);
    test-a-throwing-g-stays-lazy-under-names = cell (all3 (c: c.poisonGUnread)) (same [
      "x"
      "y"
    ]);
    # ── redeclaration (ADR-0039 (b′)): one construction declared N times is that construction where the element's
    # own redeclaration serves; nixpkgs' twin silently drops `g` (`ref`), the plain element is the control
    test-one-construction-redeclared-over-a-leaf =
      cell
        (all3 (
          c:
          map c.redeclLeaf [
            2
            3
            4
          ]
        ))
        {
          native = [
            2
            2
            2
          ];
          mount = [
            2
            2
            2
          ];
          ref = [
            1
            1
            1
          ];
        };
    test-one-construction-redeclared-over-listof =
      cell
        (all3 (
          c:
          map c.rdList [
            2
            3
            4
          ]
        ))
        {
          native = [
            [
              3
              2
            ]
            [
              3
              2
            ]
            [
              3
              2
            ]
          ];
          mount = [
            [
              3
              2
            ]
            [
              3
              2
            ]
            [
              3
              2
            ]
          ];
          ref = [
            [
              3
              1
              2
            ]
            [
              3
              1
              2
            ]
            [
              3
              1
              2
            ]
          ];
        };
    test-one-construction-redeclared-over-nixpkgs-attrsof =
      cell
        (all3 (
          c:
          map c.rdNpAttrs [
            2
            3
            4
          ]
        ))
        {
          native = [
            { b = 2; }
            { b = 2; }
            { b = 2; }
          ];
          mount = [
            { b = 2; }
            { b = 2; }
            { b = 2; }
          ];
          ref = [
            {
              a = 1;
              b = 2;
            }
            {
              a = 1;
              b = 2;
            }
            {
              a = 1;
              b = 2;
            }
          ];
        };
    test-one-construction-redeclared-over-gen-attrsof =
      cell
        (all3 (
          c:
          map c.rdGenAttrs [
            2
            3
            4
          ]
        ))
        {
          native = [
            { b = 2; }
            { b = 2; }
            { b = 2; }
          ];
          mount = [
            { b = 2; }
            { b = 2; }
            { b = 2; }
          ];
          ref = [
            {
              a = 1;
              b = 2;
            }
            {
              a = 1;
              b = 2;
            }
            {
              a = 1;
              b = 2;
            }
          ];
        };
    test-one-construction-redeclared-over-a-no-default-submodule =
      cell
        (all3 (
          c:
          map c.rdSubND [
            2
            3
            4
          ]
        ))
        {
          native = [
            {
              a = 1;
              added = 2;
            }
            {
              a = 1;
              added = 2;
            }
            {
              a = 1;
              added = 2;
            }
          ];
          mount = [
            {
              a = 1;
              added = 2;
            }
            {
              a = 1;
              added = 2;
            }
            {
              a = 1;
              added = 2;
            }
          ];
          ref = [
            { a = 1; }
            { a = 1; }
            { a = 1; }
          ];
        };
    # ── the `rewrites` arm: a debt on a step above a redeclared constructor is met there; `.good` is `g ∘ fold`
    test-a-debt-on-the-element-step-above-serves-a-good-definition =
      cell
        (gen2 (c: [
          (c.rw.elemAB false)
          (c.rw.elemBA false)
        ]))
        (same2 [
          { x.k = 1; }
          { x.k = 1; }
        ]);
    test-a-debt-one-step-higher-serves-a-good-definition =
      cell
        (gen2 (c: [
          (c.rw.topAB false)
          (c.rw.topBA false)
        ]))
        (same2 [
          { x.k = 1; }
          { x.k = 1; }
        ]);
    # ── the docs face reads as the element, byte-equal to the twin's
    test-the-description-is-the-elements = cell (all3 (c: c.description)) (
      same "attribute set of lazy attribute set of attribute set of attribute set of (submodule)"
    );
    # ── the gen-demo shape: `baz` = 3 keeps, `baz` = 4 swaps; `[ 1 1 ]` if `g` is dropped
    test-the-gen-demo-shape-nested = cell (all3 (c: c.demoNested)) (same [
      1
      2
    ]);
    test-the-gen-demo-shape-at-the-root = cell (all3 (c: c.demoRoot)) (same [
      1
      2
    ]);
  };
}
