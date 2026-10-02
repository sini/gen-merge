# THE DOCS PHRASE (den-hoag-type-description-parity-5k1l1) — `description`/`descriptionClass` as
# nixpkgs states them, derived once at the export (`interface.phraseOfWithin`) within a node budget.
#
# Every cell compares gen's export with nixpkgs' answer for the SAME construction built over
# `nixpkgsLib.types`, so the expected text is nixpkgs', never a string written here. The budget
# cells pin the two places gen departs on purpose: past `phraseBudget` composing nodes the phrase
# elides to `…` (nixpkgs never elides), and a self-referential type renders a finite phrase where
# nixpkgs' own twin diverges. The cycle closed through a FOREIGN record's `description` is an
# uncatchable abort, so its cells live in `../tests-process-cells.nix`.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;

  # One construction, two vocabularies: the dialect is all that differs between the sides.
  dial = {
    gen = gt // {
      enum' = vs: gt.enum "e" vs;
      mods = m: gt.submodule m;
      mkOpt = gm.mkOption;
      tree = m: (gm.evalModuleTree { modules = m; }).type;
      derive = b: spec: gt.deriveType b spec;
      rederive = b: el: (gt.deriveType b { id = "d"; }).recarry { element = el; };
    };
    np = np // {
      enum' = vs: np.enum vs;
      mods = m: np.submodule m;
      mkOpt = nl.mkOption;
      tree = m: (nl.evalModules { modules = m; }).type;
      # nixpkgs' analogue of a derivation is `base // { … }`, which keeps the base's phrase and class
      derive = b: spec: b // nl.optionalAttrs (spec ? description) { inherit (spec) description; };
      rederive = _b: el: np.listOf el;
    };
  };
  m1 = D: [ { options.a = D.mkOpt { type = D.int; }; } ];
  nrc =
    D:
    D.mkOptionType {
      name = "p";
      description = "port, meaning >0";
      descriptionClass = "nonRestrictiveClause";
    };
  described =
    D:
    D.mkOptionType {
      name = "thing";
      description = "a thing";
      descriptionClass = "noun";
    };
  rows = {
    anything = D: D.anything;
    attrs = D: D.attrs;
    bool = D: D.bool;
    deferredModule = D: D.deferredModule;
    float = D: D.float;
    int = D: D.int;
    number = D: D.number;
    path = D: D.path;
    raw = D: D.raw;
    str = D: D.str;
    "attrsOf int" = D: D.attrsOf D.int;
    "lazyAttrsOf int" = D: D.lazyAttrsOf D.int;
    "listOf int" = D: D.listOf D.int;
    "nullOr int" = D: D.nullOr D.int;
    "either int str" = D: D.either D.int D.str;
    "oneOf [int str bool]" =
      D:
      D.oneOf [
        D.int
        D.str
        D.bool
      ];
    "oneOf [int]" = D: D.oneOf [ D.int ];
    "enum [a b]" =
      D:
      D.enum' [
        "a"
        "b"
      ];
    "enum [a]" = D: D.enum' [ "a" ];
    "enum []" = D: D.enum' [ ];
    "enum [1 true]" =
      D:
      D.enum' [
        1
        true
      ];
    submodule = D: D.mods (m1 D);
    "listOf (attrsOf int)" = D: D.listOf (D.attrsOf D.int);
    "attrsOf (listOf (nullOr str))" = D: D.attrsOf (D.listOf (D.nullOr D.str));
    "either (listOf int) str" = D: D.either (D.listOf D.int) D.str;
    "nullOr (either int str)" = D: D.nullOr (D.either D.int D.str);
    "attrsOf (either int str)" = D: D.attrsOf (D.either D.int D.str);
    "attrsOf submodule" = D: D.attrsOf (D.mods (m1 D));
    "listOf submodule" = D: D.listOf (D.mods (m1 D));
    "nullOr submodule" = D: D.nullOr (D.mods (m1 D));
    "lazyAttrsOf (listOf int)" = D: D.lazyAttrsOf (D.listOf D.int);
    "listOf (enum [a b])" =
      D:
      D.listOf (
        D.enum' [
          "a"
          "b"
        ]
      );
    "either (enum [a b]) int" =
      D:
      D.either (D.enum' [
        "a"
        "b"
      ]) D.int;
    "attrsOf anything" = D: D.attrsOf D.anything;
    "listOf raw" = D: D.listOf D.raw;
    "nullOr (nullOr int)" = D: D.nullOr (D.nullOr D.int);
    "either (nullOr int) str" = D: D.either (D.nullOr D.int) D.str;
    "mkOptionType bare" = D: D.mkOptionType { name = "thing"; };
    "mkOptionType described" = described;
    "listOf (mkOptionType described)" = D: D.listOf (described D);
    # a descriptor NAMED like a vocabulary construction is described by its name (`description ? name`)
    "mkOptionType named int" = D: D.mkOptionType { name = "int"; };
    "listOf (mkOptionType named int)" = D: D.listOf (D.mkOptionType { name = "int"; });
    "either nrc int" = D: D.either (nrc D) D.int;
    "either int nrc" = D: D.either D.int (nrc D);
    "oneOf [int nrc str]" =
      D:
      D.oneOf [
        D.int
        (nrc D)
        D.str
      ];
    "oneOf [nrc int str]" =
      D:
      D.oneOf [
        (nrc D)
        D.int
        D.str
      ];
    "listOf np.int" = D: D.listOf np.int;
    "np.attrsOf (listOf int)" = D: np.attrsOf (D.listOf D.int);
    "derive int" = D: D.derive D.int { id = "d"; };
    "derive (attrsOf int)" = D: D.derive (D.attrsOf D.int) { id = "d"; };
    "derive int described" =
      D:
      D.derive D.int {
        id = "d";
        description = "port number";
      };
    "derive (listOf int) recarried str" = D: D.rederive (D.listOf D.int) D.str;
    "tree plain" = D: D.tree (m1 D);
    "tree free" = D: D.tree (m1 D ++ [ { freeformType = D.attrsOf D.int; } ]);
    "submodule free" = D: D.mods (m1 D ++ [ { freeformType = D.attrsOf D.int; } ]);
  };
  read =
    t:
    let
      r = builtins.tryEval (
        builtins.deepSeq [ t.description t.descriptionClass ] {
          d = t.description;
          c = t.descriptionClass;
        }
      );
    in
    if r.success then r.value else "REFUSED";
  sides = builtins.mapAttrs (_: k: {
    gen = read (k dial.gen);
    np = read (k dial.np);
  }) rows;

  # 9v4j0's nine docs cells: a nixpkgs evaluation renders an option holding `submodule` bare and in
  # each foreign wrapper, through make-options-doc's filter (`visible && !internal`).
  docsOf =
    T:
    let
      modsOf =
        free:
        [
          {
            options.a = T.mkOpt {
              type = T.int;
              default = 0;
            };
          }
        ]
        ++ (if free then [ { freeformType = T.attrsOf T.int; } ] else [ ]);
      cons = free: {
        bare = T.mods (modsOf free);
        attrsOf = np.attrsOf (T.mods (modsOf false));
        listOf = np.listOf (T.mods (modsOf false));
        uniq = np.uniq (T.mods (modsOf false));
        unique = np.unique { message = "m"; } (T.mods (modsOf false));
        addCheck = np.addCheck (T.mods (modsOf false)) (_: true);
        coercedTo = np.coercedTo np.str (_: { a = 5; }) (T.mods (modsOf false));
        nullOr = np.nullOr (T.mods (modsOf false));
      };
      render =
        type:
        map (o: { inherit (o) name type; }) (
          builtins.filter (o: o.visible && !o.internal) (
            nl.optionAttrSetToDocList
              (nl.evalModules { modules = [ { options.s = nl.mkOption { inherit type; }; } ]; }).options
          )
        );
    in
    builtins.mapAttrs (_: render) (cons false) // { "bare/free" = render (cons true).bare; };
  docs = {
    gen = docsOf dial.gen;
    np = docsOf dial.np;
  };

  # A self-referential gen type (nixpkgs' `types.json` value shape) and nixpkgs' refusals over it.
  v = gt.nullOr (
    gt.oneOf [
      gt.str
      (gt.attrsOf v)
      (gt.listOf v)
    ]
  );
  ffself = gt.submodule [ { freeformType = ffself; } ];
  # The same shape with its cycle closed THROUGH a derivation, and closed outside one it holds.
  vd = gt.deriveType (gt.nullOr (
    gt.oneOf [
      gt.str
      (gt.attrsOf vd)
      (gt.listOf vd)
    ]
  )) { id = "d"; };
  vdIn = gt.nullOr (
    gt.oneOf [
      gt.str
      (gt.attrsOf (gt.deriveType vdIn { id = "d"; }))
      (gt.listOf vdIn)
    ]
  );
  # a phrase's head, which is where the derivation's and its base shape's agree
  head200 = t: builtins.substring 0 200 t.description;
  docTypeOf =
    type:
    (builtins.head (
      builtins.filter (o: o.name == "s") (
        nl.optionAttrSetToDocList
          (nl.evalModules { modules = [ { options.s = nl.mkOption { inherit type; }; } ]; }).options
      )
    )).type;
  mountedAt =
    type: value:
    (nl.evalModules {
      modules = [
        {
          options.s = nl.mkOption { inherit type; };
          config.s = value;
        }
      ];
    }).config.s;
  caught = x: (builtins.tryEval (builtins.deepSeq x x)).success;

  # The ceiling: k nested `listOf`s over `int` in each vocabulary.
  nest =
    L: leaf: k:
    builtins.foldl' (t: _: L t) leaf (builtins.genList (x: x) k);
  ceilingRow =
    k:
    let
      g = (nest gt.listOf gt.int k).description;
    in
    {
      equal = g == (nest np.listOf np.int k).description;
      ends = builtins.substring (builtins.stringLength g - 3) 3 g;
    };
  vs = i: builtins.genList (j: "member-value-number-${toString i}-${toString j}") 6;
  bigEnum = builtins.genList (j: "integration-${toString j}") 1500;
in
{
  flake.tests.description-phrase = {
    # G1: every construction's pair equals nixpkgs', but one. `oneOf [int nrc str]` is
    # den-hoag-b47r5's: nixpkgs' `oneOf` folds into a right-nested `either`, so its middle operand is
    # a second operand and parenthesised. This cell reds when b47r5 lands, which is the right failure.
    test-every-construction-reads-nixpkgs-phrase-and-class = {
      expr = nl.filterAttrs (_: s: s.gen != s.np) sides;
      expected."oneOf [int nrc str]" = {
        gen = {
          c = "conjunction";
          d = "signed integer or port, meaning >0, or string";
        };
        np = {
          c = "conjunction";
          d = "signed integer or (port, meaning >0) or string";
        };
      };
    };
    # Its live control: the table is the 55 constructions, and the departure set is empty of every
    # row but b47r5's, rather than every row reading the same refusal.
    test-control-the-table-reads-55-rows-none-refused = {
      expr = {
        rows = builtins.length (builtins.attrNames sides);
        refused = builtins.attrNames (nl.filterAttrs (_: s: s.gen == "REFUSED" || s.np == "REFUSED") sides);
      };
      expected = {
        rows = 55;
        refused = [ ];
      };
    };

    # G2: nixpkgs' docs render every gen-typed position as it renders nixpkgs' twin.
    test-nine-docs-cells-render-as-nixpkgs = {
      expr = builtins.attrNames (nl.filterAttrs (k: g: g != docs.np.${k}) docs.gen);
      expected = [ ];
    };
    test-control-every-docs-cell-renders-a-typed-entry = {
      expr = builtins.attrNames (
        nl.filterAttrs (_: g: g == [ ] || builtins.any (o: o.type == "") g) docs.gen
      );
      expected = [ ];
    };

    # G5: a self-referential gen type renders a finite phrase, and every nixpkgs refusal over it is a
    # catchable refusal, not a divergence. nixpkgs' own twin diverges on the same reads.
    test-a-self-referential-type-renders-a-finite-phrase = {
      expr = builtins.isString v.description;
      expected = true;
    };
    test-a-freeform-nest-of-itself-renders-a-finite-phrase = {
      expr = builtins.isString ffself.description;
      expected = true;
    };
    test-nixpkgs-refusals-over-a-self-referential-type-are-caught = {
      expr = {
        top = caught (mountedAt v 5);
        either = caught (mountedAt (np.either np.int v) true);
        list = caught (mountedAt (np.listOf v) 5);
      };
      expected = {
        top = false;
        either = false;
        list = false;
      };
    };
    test-control-a-self-referential-type-admits-its-value = {
      expr = mountedAt v { a = [ "x" ]; };
      expected = {
        a = [ "x" ];
      };
    };

    # A cycle closed through a derivation (`deriveType`) renders the base's phrase within the budget,
    # so its docs and every nixpkgs refusal over it answer, as they do for `v`.
    test-a-cycle-through-a-derivation-renders-its-bases-phrase = {
      expr = {
        through = head200 vd;
        outside = head200 vdIn;
        docs = builtins.substring 0 200 (docTypeOf vd);
      };
      expected = {
        through = head200 v;
        outside = head200 v;
        docs = head200 v;
      };
    };
    test-nixpkgs-refusals-over-a-cycle-through-a-derivation-are-caught = {
      expr = {
        top = caught (mountedAt vd 5);
        either = caught (mountedAt (np.either np.int vd) true);
        list = caught (mountedAt (np.listOf vd) 5);
        outside = caught (mountedAt vdIn 5);
      };
      expected = {
        top = false;
        either = false;
        list = false;
        outside = false;
      };
    };
    test-control-a-cycle-through-a-derivation-admits-its-value = {
      expr = mountedAt vd { a = [ "x" ]; };
      expected = {
        a = [ "x" ];
      };
    };

    # G6: the ceiling. Up to `phraseBudget` (128) composing nodes the phrase is nixpkgs'; past it the
    # rest elides to `…`. A leaf costs nothing, however wide; a freeform nest costs a node.
    test-the-phrase-is-nixpkgs-up-to-the-ceiling-and-elides-past-it = {
      expr = {
        "127" = ceilingRow 127;
        "128" = ceilingRow 128;
        "129" = ceilingRow 129;
      };
      expected = {
        "127" = {
          equal = true;
          ends = "ger";
        };
        "128" = {
          equal = true;
          ends = "ger";
        };
        "129" = {
          equal = false;
          ends = "…";
        };
      };
    };
    # A derivation stating no phrase costs one node: its base's 128-node phrase elides under it.
    test-a-derivation-is-charged-a-node = {
      expr =
        let
          row =
            k:
            let
              d = (gt.deriveType (nest gt.listOf gt.int k) { id = "d"; }).description;
            in
            {
              equal = d == (nest gt.listOf gt.int k).description;
              ends = builtins.substring (builtins.stringLength d - 3) 3 d;
            };
        in
        {
          "127" = row 127;
          "128" = row 128;
        };
      expected = {
        "127" = {
          equal = true;
          ends = "ger";
        };
        "128" = {
          equal = false;
          ends = "…";
        };
      };
    };
    # ... and a chain of them costs that one node in total, never one per layer.
    test-a-chain-of-derivations-keeps-its-bases-phrase = {
      expr =
        let
          b = nest gt.listOf gt.int 3;
          chain = n: if n == 0 then b else gt.deriveType (chain (n - 1)) { id = "d"; };
        in
        {
          "126" = (chain 126).description;
          "200" = (chain 200).description;
        };
      expected = {
        "126" = "list of list of list of signed integer";
        "200" = "list of list of list of signed integer";
      };
    };
    test-a-freeform-nest-is-charged-a-node = {
      expr =
        let
          g = (gt.submodule [ { freeformType = nest gt.listOf gt.int 128; } ]).description;
        in
        {
          equal = g == (np.submodule [ { freeformType = nest np.listOf np.int 128; } ]).description;
          ends = builtins.substring (builtins.stringLength g - 3) 3 g;
        };
      expected = {
        equal = false;
        ends = "…";
      };
    };
    test-wide-leaves-cost-no-nodes = {
      expr = {
        enums =
          (gt.oneOf [
            (gt.enum "a" (vs 1))
            (gt.enum "b" (vs 2))
            (gt.enum "c" (vs 3))
          ]).description == (np.either (np.enum (vs 1)) (np.either (np.enum (vs 2)) (np.enum (vs 3))))
          .description;
        bigEnum =
          (gt.listOf (gt.enum "e" bigEnum)).description == (np.listOf (np.enum bigEnum)).description;
      };
      expected = {
        enums = true;
        bigEnum = true;
      };
    };
  };
}
