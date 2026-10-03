# `nullOr` over a MIXED definition set — null beside a value — has nixpkgs' answer (den-hoag-azdne).
# nixpkgs' `nullOr` reports a head error for it ("defined both null and not null"); dropping the
# nulls and merging the rest through the element served a value nixpkgs refuses. Each cell is
# measured against `nixpkgsLib.evalModules` in the same run, so the expected value is nixpkgs' own,
# and the controls (every definition null, none null, a null discharged by `mkIf` or out-prioritised)
# arm the refusal against swallowing a set nixpkgs serves.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  nt = nixpkgsLib.types;
  try = e: (builtins.tryEval (builtins.deepSeq e e)).value;
  # One option of type `ty` and one definition module per entry of `defs`, under either system.
  gen =
    ty: defs:
    try
      (gm.evalModuleTree {
        modules = [ { options.x = gm.mkOption { type = ty; }; } ] ++ map (v: { x = v; }) defs;
      }).config.x;
  np =
    evalModules: mkOption: ty: defs:
    try
      (evalModules {
        modules = [ { options.x = mkOption { type = ty; }; } ] ++ map (v: { x = v; }) defs;
      }).config.x;
  ref = np nixpkgsLib.evalModules nixpkgsLib.mkOption;
  # The gen type mounted as an option type in nixpkgs' own `lib.evalModules`.
  mount = np nixpkgsLib.evalModules nixpkgsLib.mkOption;
  # An undeclared key under a freeform plane typed `attrsOf (nullOr int)`.
  ff =
    evalModules: ty: defs:
    try (evalModules { modules = [ { freeformType = ty; } ] ++ map (v: { k = v; }) defs; }).config.k;
  sets = M: {
    allNull = [
      null
      null
    ];
    oneNull = [ null ];
    allValue = [
      5
      5
    ];
    mixed = [
      null
      5
    ];
    mixedReversed = [
      5
      null
    ];
    mkMergeMixed = [
      (M.mkMerge [
        null
        5
      ])
    ];
    mkIfFalseNull = [
      (M.mkIf false null)
      5
    ];
    mkDefaultNull = [
      (M.mkDefault null)
      5
    ];
    mkForceNull = [
      (M.mkForce null)
      5
    ];
    equalPriorityMixed = [
      (M.mkDefault null)
      (M.mkDefault 5)
    ];
  };
  # Every plane's answer per set, beside nixpkgs' answer for the same spelling.
  table =
    gty: nty:
    builtins.mapAttrs (
      k: defs:
      let
        r = ref nty (sets nixpkgsLib).${k};
      in
      {
        native = gen gty defs == r;
        mount = mount gty (sets nixpkgsLib).${k} == r;
        freeform =
          ff gm.evalModuleTree (t.attrsOf gty) defs
          == ff nixpkgsLib.evalModules (nt.attrsOf nty) (sets nixpkgsLib).${k};
      }
    ) (sets gm);
  allTrue = builtins.mapAttrs (_: _: {
    native = true;
    mount = true;
    freeform = true;
  }) (sets gm);
  sub = t.submodule { options.a = gm.mkOption { type = genTypes.int; }; };
  nsub = nt.submodule { options.a = nixpkgsLib.mkOption { type = nt.int; }; };
in
{
  flake.tests.nullor-mixed = {
    test-nullOr-int-has-nixpkgs-answer-on-every-plane = {
      expr = table (t.nullOr genTypes.int) (nt.nullOr nt.int);
      expected = allTrue;
    };
    test-nested-nullOr-has-nixpkgs-answer-on-every-plane = {
      expr = table (t.nullOr (t.nullOr genTypes.int)) (nt.nullOr (nt.nullOr nt.int));
      expected = allTrue;
    };
    # The value each answer is, not only that the two agree: a mixed set refuses, the controls serve.
    test-the-mixed-set-refuses-and-the-controls-serve = {
      expr = builtins.mapAttrs (_: gen (t.nullOr genTypes.int)) (sets gm);
      expected = {
        allNull = null;
        oneNull = null;
        allValue = 5;
        mixed = false;
        mixedReversed = false;
        mkMergeMixed = false;
        mkIfFalseNull = 5;
        mkDefaultNull = 5;
        mkForceNull = null;
        equalPriorityMixed = false;
      };
    };
    # As a union's first member, nixpkgs' `nullOr` head error passes the set to the later member. A
    # union asks its member pointwise unless the member states a head judgement (den-hoag-e6m9d), so
    # the cell admits nixpkgs' answer OR a refusal, and never the element's answer over the non-null
    # definitions. `taker` accepts every definition, so nixpkgs' answer and the refusal differ where
    # it is the later member; the `mount` row is nixpkgs' `either` holding the gen `nullOr`, which
    # reads its member pointwise.
    test-a-union-member-never-serves-the-element-answer-for-a-mixed-set =
      let
        taker =
          T:
          T.mkOptionType {
            name = "taker";
            check = _: true;
            merge = _: _: "taker";
          };
        mixed = [
          null
          5
        ];
        served =
          g: n: s:
          gen g s == ref n s || gen g s == false;
        shipped = served (t.either (t.nullOr genTypes.int) (t.attrsOf genTypes.int)) (
          nt.either (nt.nullOr nt.int) (nt.attrsOf nt.int)
        );
        mountServed =
          s:
          let
            v = mount (nt.either (t.nullOr genTypes.int) (taker nt)) s;
          in
          v != 5 && (v == ref (nt.either (nt.nullOr nt.int) (taker nt)) s || v == false);
      in
      {
        expr = {
          mixed = shipped mixed;
          mixedReversed = shipped [
            5
            null
          ];
          oneNull = shipped [ null ];
          oneValue = shipped [ 5 ];
          laterTaker = served (t.either (t.nullOr genTypes.int) (taker t)) (nt.either (nt.nullOr nt.int) (
            taker nt
          )) mixed;
          oneOfTaker =
            served
              (t.oneOf [
                (t.nullOr genTypes.int)
                t.str
                (taker t)
              ])
              (nt.oneOf [
                (nt.nullOr nt.int)
                nt.str
                (taker nt)
              ])
              mixed;
          nullOrSecond = served (t.either t.str (t.nullOr genTypes.int)) (nt.either nt.str (
            nt.nullOr nt.int
          )) mixed;
          mount = mountServed mixed;
        };
        expected = {
          mixed = true;
          mixedReversed = true;
          oneNull = true;
          oneValue = true;
          laterTaker = true;
          oneOfTaker = true;
          nullOrSecond = true;
          mount = true;
        };
      };
    # A nesting element: the module walk reaches the element through the same split the fold reads.
    test-a-nesting-element-refuses-a-mixed-set = {
      expr = {
        top = gen (t.nullOr sub) [
          null
          { a = 1; }
        ];
        topRef = ref (nt.nullOr nsub) [
          null
          { a = 1; }
        ];
        lazy =
          try
            (gm.evalModuleTree {
              modules = [
                { options.x = gm.mkOption { type = t.lazyAttrsOf (t.nullOr sub); }; }
                { x.k = null; }
                { x.k.a = 1; }
              ];
            }).config.x.k.a;
        served = gen (t.nullOr sub) [ { a = 1; } ];
      };
      expected = {
        top = false;
        topRef = false;
        lazy = false;
        served = {
          a = 1;
        };
      };
    };
    # The option's own `default = null` sits at a lower priority than a definition, so it never meets
    # the definition in one set.
    test-a-null-default-beside-a-definition-serves-the-definition = {
      expr =
        try
          (gm.evalModuleTree {
            modules = [
              {
                options.x = gm.mkOption {
                  type = t.nullOr genTypes.int;
                  default = null;
                };
              }
              { x = 5; }
            ];
          }).config.x;
      expected = 5;
    };
  };
}
