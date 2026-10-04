# `deriveType` — A DERIVED TYPE KEEPS ITS DERIVATION (den-hoag-5kic).
#
# `base // Δ` over a completed type keeps the base's check and fold and loses everything closed over
# the base's knot: it merges with itself to its base, rebuilds to its base, is absorbed by its base,
# and mints as its base. Every cell below reads the derivation through one of those answers, over
# three bases — a leaf, a container and a sealed `mkOptionType` — and the separation cell over every
# relation family this library states. `naive` is what a caller writes without the primitive: each
# identity cell reads it beside the derivation, so the predicate is shown to fire on the defect in
# the same run (the seeded-class control).
#
# ★ THE BEHAVIOUR CELL IS THE CONTROL THAT THE OTHERS FIRE ON IDENTITY, NOT BREAKAGE: the naive arm
# passes it too. Its negative inputs are what make it able to fail.
{
  genMerge,
  genTypes,
  interface,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  inherit (gm) deriveType mergeTypes;
  inherit (builtins) tryEval deepSeq mapAttrs;

  # The options every derivation below shares; each passes its `id` positionally.
  tagged = {
    fields = _: {
      __tag = "tagged";
      description = "a tagged type";
    };
  };
  naive = b: b // { __tag = "tagged"; };

  # The derivation a result answers for: its `id`, `LOST` for any other type, `NULL` for a refusal.
  idOf = v: if v == null then "NULL" else v.__derivation.id or "LOST";
  tagOf = v: if v == null then "NULL" else v.__tag or "LOST";

  sealed = gm.mkOptionType {
    name = "opaque";
    check = builtins.isString;
    merge = _loc: defs: (builtins.head defs).value;
  };
  bases = {
    leaf = t.str;
    container = t.listOf t.str;
    inherit sealed;
  };
  # Every gen-merge relation family: nullary, sealed, element, and the three that compare a partner
  # with a literal name (`submodule`, `attrs`, `either`).
  families = bases // {
    attrsOf = t.attrsOf t.str;
    lazyAttrsOf = t.lazyAttrsOf t.str;
    nullOr = t.nullOr t.str;
    submodule = t.submodule { };
    attrs = t.attrs;
    either = t.either t.str t.int;
  };
  derived = mapAttrs (_: b: deriveType tagged "tagged" b) families;

  # One option declared twice; `true` iff the declaration path merged the pair.
  declares =
    a: b:
    (tryEval (
      deepSeq
        (gm.evalModuleTree { } [
          { options.o = gm.mkOption { type = a; }; }
          { options.o = gm.mkOption { type = b; }; }
        ]).options.o.type.name
        null
    )).success;
  value = b: if b.name == "listOf" then [ "a" ] else "a";
  fold =
    d: v:
    (gm.evalModuleTree { } [
      { options.o = gm.mkOption { type = d; }; }
      { o = v; }
    ]).config.o;
  checks =
    d:
    map (v: d.check v) [
      "a"
      [ "a" ]
      1
      [ 1 ]
    ];

  # The separation answers for one base: raw `mergeTypes` both orders, the foreign protocol both
  # orders, and the declaration path both orders.
  separation = b: d: {
    raw = [
      (idOf (mergeTypes {
        deciding = b;
        partner = d;
      }))
      (idOf (mergeTypes {
        deciding = d;
        partner = b;
      }))
    ];
    foreign = [
      (idOf (b.typeMerge d.functor))
      (idOf (d.typeMerge b.functor))
    ];
    declared = [
      (declares b d)
      (declares d b)
    ];
  };
  separated = {
    raw = [
      "NULL"
      "NULL"
    ];
    foreign = [
      "NULL"
      "NULL"
    ];
    declared = [
      false
      false
    ];
  };

  # The partition, against every field a type this library builds carries.
  classLists = builtins.attrValues interface.deriveClasses;
  classified = builtins.concatLists classLists;
  metadata = interface.exportClasses.nameCarried;
  built = builtins.attrNames (
    builtins.foldl' (acc: ty: acc // ty) { } (
      builtins.attrValues families
      ++ [
        t.int
        (t.oneOf [
          t.str
          t.int
        ])
        t.raw
        t.anything
        t.deferredModule
        (t.enum "e" [ "a" ])
        ((t.submodule { }).withArgs { })
      ]
    )
  );

  # A line of `lib/types.nix` that compares a `.name` with `==`/`!=`, comments excluded.
  vocabularyLines = builtins.filter (l: builtins.isString l && builtins.match " *#.*" l == null) (
    builtins.split "\n" (builtins.readFile ../../lib/types.nix)
  );
  comparesName =
    l:
    builtins.match ".*\\.name( or [^)]*)?\\)? *(==|!=).*" l != null
    || builtins.match ".*(==|!=) *\\(?[a-zA-Z_.]*\\.name([^a-zA-Z_].*)?" l != null;

  keyed = k: deriveType (tagged // { key = k; }) "tagged" t.str;
  minted = deriveType (tagged // { mint.minted = "tagged-over-str"; }) "tagged" t.str;
in
{
  flake.tests.derive-type = {
    # C1 — idempotence on gen's own path: d ⊔ d answers the derivation.
    test-merging-a-derivation-with-itself-keeps-it = {
      expr = mapAttrs (
        _: b:
        idOf (mergeTypes {
          deciding = (deriveType tagged "tagged" b);
          partner = (deriveType tagged "tagged" b);
        })
      ) bases;
      expected = mapAttrs (_: _: "tagged") bases;
    };
    # C8 — the same predicate over `//`: the base answers, or the twin is refused.
    test-control-a-naive-derivation-merged-with-itself-loses-it = {
      expr = mapAttrs (
        _: b:
        tagOf (mergeTypes {
          deciding = (naive b);
          partner = (naive b);
        })
      ) bases;
      expected = {
        leaf = "LOST";
        container = "LOST";
        sealed = "NULL";
      };
    };
    # C2 — idempotence on the foreign protocol's path.
    test-a-derivation-joins-its-own-functor-to-itself = {
      expr = mapAttrs (
        _: b:
        let
          d = deriveType tagged "tagged" b;
        in
        idOf (d.typeMerge d.functor)
      ) bases;
      expected = mapAttrs (_: _: "tagged") bases;
    };
    test-control-a-naive-derivation-joins-its-own-functor-to-its-base = {
      expr = mapAttrs (
        _: b:
        let
          d = naive b;
        in
        tagOf (d.typeMerge d.functor)
      ) bases;
      expected = mapAttrs (_: _: "LOST") bases;
    };
    # C3 — separation, the base's name kept, over every relation family.
    test-a-derivation-never-merges-with-its-base = {
      expr = mapAttrs (n: d: separation families.${n} d) derived;
      expected = mapAttrs (_: _: separated) families;
    };
    test-a-derivation-keeps-its-base-name = {
      expr = mapAttrs (n: d: d.name == families.${n}.name) derived;
      expected = mapAttrs (_: _: true) families;
    };
    test-control-a-naive-derivation-is-absorbed-by-its-base = {
      expr = mapAttrs (
        _: b:
        tagOf (mergeTypes {
          deciding = b;
          partner = (naive b);
        })
      ) bases;
      expected = {
        leaf = "LOST";
        container = "LOST";
        sealed = "NULL";
      };
    };
    # C4 — naturality: rebuilding a derivation rebuilds the derivation.
    test-rebuilding-a-derivation-keeps-it = {
      expr =
        let
          d = derived.container;
        in
        {
          recarry = idOf (d.recarry { element = t.int; });
          functorType = idOf (d.functor.type d.functor.payload);
          leafFunctorType = idOf derived.leaf.functor.type;
          withArgs = idOf (derived.submodule.withArgs { });
          rebuild = idOf (derived.submodule.substSubModules [ ]);
          element = (d.recarry { element = t.int; }).carries.element.name;
        };
      expected = {
        recarry = "tagged";
        functorType = "tagged";
        leafFunctorType = "tagged";
        withArgs = "tagged";
        rebuild = "tagged";
        element = "int";
      };
    };
    test-control-a-naive-derivation-rebuilds-its-base = {
      expr = tagOf ((naive bases.container).recarry { element = t.int; });
      expected = "LOST";
    };
    # C5 — behaviour: the base's check and fold, positive and negative inputs alike.
    test-a-derivation-checks-and-folds-as-its-base = {
      expr = mapAttrs (n: b: {
        check = checks derived.${n} == checks b;
        fold = fold derived.${n} (value b) == fold b (value b);
      }) bases;
      expected = mapAttrs (_: _: {
        check = true;
        fold = true;
      }) bases;
    };
    # C6 — identity (ADR-0034): sealed by default, never the base's.
    test-a-derivation-does-not-mint-as-its-base = {
      expr = {
        base = genTypes.typeEq derived.leaf t.str;
        self = genTypes.typeEq derived.leaf derived.leaf;
        regime = builtins.attrNames derived.leaf.__mint;
      };
      expected = {
        base = false;
        self = true;
        regime = [ "unmintable" ];
      };
    };
    # A naive `//` derivation keeps its base's mark and witness, so `typeEq` refuses it by name (the
    # completion stamp): it is not the record its constructor completed. `deriveType` is the door.
    test-control-a-naive-derivation-mints-as-its-base = {
      expr = (builtins.tryEval (genTypes.typeEq (naive t.str) t.str)).success;
      expected = false;
    };
    # C9 — `key`: two derivations of one `id` merge only where their keys agree.
    test-derivations-whose-keys-differ-never-merge = {
      expr = separation (keyed "a") (keyed "b");
      expected = separated;
    };
    test-control-derivations-whose-keys-agree-merge = {
      expr = {
        raw = idOf (mergeTypes {
          deciding = (keyed "a");
          partner = (keyed "a");
        });
        declared = declares (keyed "a") (keyed "a");
        key =
          (mergeTypes {
            deciding = (keyed "a");
            partner = (keyed "a");
          }).__derivation.key;
      };
      expected = {
        raw = "tagged";
        declared = true;
        key = "a";
      };
    };
    test-control-derivations-of-two-ids-never-merge = {
      expr = separation derived.leaf (deriveType tagged "other" t.str);
      expected = separated;
    };
    # C10 — a supplied mint is the derivation's identity.
    test-a-supplied-mint-is-the-derivations-identity = {
      expr = {
        base = genTypes.typeEq minted t.str;
        self = genTypes.typeEq minted minted;
        id = minted.__id;
      };
      expected = {
        base = false;
        self = true;
        id = "tagged-over-str";
      };
    };
    # A foreign base crosses the import boundary first.
    test-a-foreign-base-derives = {
      expr =
        let
          np = nixpkgsLib.types.str;
          d = deriveType tagged "tagged" np;
        in
        {
          self = idOf (mergeTypes {
            deciding = d;
            partner = d;
          });
          base = idOf (mergeTypes {
            deciding = d;
            partner = np;
          });
          check = checks d == checks np;
          fold = fold d "a";
        };
      expected = {
        self = "tagged";
        base = "NULL";
        check = true;
        fold = "a";
      };
    };
    test-a-derivation-of-a-derivation-keeps-both = {
      expr =
        let
          dd = deriveType tagged "outer" derived.leaf;
        in
        {
          self = idOf (mergeTypes {
            deciding = dd;
            partner = dd;
          });
          inner =
            (mergeTypes {
              deciding = dd;
              partner = dd;
            }).__derivation.base.__derivation.id;
          base = idOf (mergeTypes {
            deciding = dd;
            partner = derived.leaf;
          });
        };
      expected = {
        self = "outer";
        inner = "tagged";
        base = "NULL";
      };
    };
    test-the-metadata-and-name-are-the-callers = {
      expr =
        let
          d = deriveType (tagged // { name = "label"; }) "tagged" t.str;
        in
        {
          inherit (d) name description __tag;
          functor = d.functor.name;
        };
      expected = {
        name = "label";
        description = "a tagged type";
        __tag = "tagged";
        functor = "tagged";
      };
    };
    # Placement: one value, at the top level and in `types`.
    test-deriveType-is-published-at-both-paths = {
      expr = [
        (gm ? deriveType)
        (t ? deriveType)
        ((t.deriveType tagged "tagged" t.str).functor.name)
      ];
      expected = [
        true
        true
        "tagged"
      ];
    };
    # The partition: its classes are disjoint, and every field a type this library builds carries
    # is in one of them or is metadata a delta may set, so a field gen's vocabulary gains fails here
    # by name until it is classified.
    test-the-derivation-partition-is-disjoint-and-total = {
      expr = {
        overlaps = builtins.filter (
          n: builtins.length (builtins.filter (c: builtins.elem n c) classLists) > 1
        ) classified;
        unclassified = builtins.filter (n: !(builtins.elem n (classified ++ metadata))) built;
      };
      expected = {
        overlaps = [ ];
        unclassified = [ ];
      };
    };
    test-control-the-partition-sees-an-unclassified-field = {
      expr = builtins.filter (n: !(builtins.elem n (classified ++ metadata))) (
        builtins.attrNames (t.str // { freshField = null; })
      );
      expected = [ "freshField" ];
    };
    # K1 — a relation decides by `keyOf`, never by comparing a `.name`: a relation that did would
    # absorb a derivation keeping its base's name. Read over the source, comments excluded, so a
    # fourth literal-name relation fails here by line.
    test-no-relation-in-the-vocabulary-compares-a-name = {
      expr = builtins.filter comparesName vocabularyLines;
      expected = [ ];
    };
    test-control-the-name-comparison-predicate-fires = {
      expr = map comparesName [
        ''if !(isAttrs other) || (other.name or null) != "either" then''
        "if isAttrs other && (other.name or null) == name then"
        "if !(isAttrs other) || (keyOf other) != name then"
      ];
      expected = [
        true
        true
        false
      ];
    };
  };
}
