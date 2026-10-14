# A door's return for a caller's FOREIGN record, re-entered through a SECOND door (den-hoag-dyagb). The published
# `mkOptionType`, `defineType` and `deriveType` return a record closed under its rebuilds (`interface.rebuildClosed`,
# `rebuildClosed.imported`), and a caller may hand that return to a door again: `defineType (mkOptionType X)`,
# `mkOptionType (defineType X)`, `deriveType` over either. Each cell is one composition `outer (inner X)`, X nixpkgs'
# `addCheck` of a stock record or the ad-hoc `// { check }` spelling, declared twice (LL) or after its plain record
# (TL) in nixpkgs' `lib.evalModules`: the definition the check rejects is refused, and the one it admits is served
# with the all-nixpkgs twin's value. The cells are every composition of two doors that served the rejected definition
# at gen-merge 72943d8 (`reports/den-hoag-dyagb-spec-v0.probes/redoor2.nix`, 50 of 4,224 rows).
# Red: the cells whose outer door completes a `mkOptionType` or `deriveType` return with `imported`'s
# `typeMergeRel` or `retainedRelation` closure left out; the cells whose inner door is `defineType` with the base
# read as the record's own join (`t.typeMerge t.functor`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    all
    attrValues
    elemAt
    isAttrs
    isInt
    isList
    listToAttrs
    replaceStrings
    split
    filter
    isString
    ;
  run =
    ts: dv:
    let
      c =
        (nl.evalModules {
          modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ map (v: { x = v; }) dv;
        }).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  gSub = gt.submodule {
    key = "drd-sub";
    options.a = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  pA = v: !(isAttrs v) || !(isInt (v.a or null)) || v.a != 2;
  pInt = x: !(isInt x) || x < 10;
  pAttrs = v: !(isAttrs v) || all pInt (attrValues v);
  shapes = {
    nullOrG = {
      t = np.nullOr gSub;
      p = pA;
      ok.a = 1;
      bad.a = 2;
    };
    listOfG = {
      t = np.listOf gSub;
      p = v: !(isList v) || all pA v;
      ok = [ { a = 1; } ];
      bad = [ { a = 2; } ];
    };
    attrsOfG = {
      t = np.attrsOf gSub;
      p = v: !(isAttrs v) || all pA (attrValues v);
      ok.k.a = 1;
      bad.k.a = 2;
    };
    listOf = {
      t = np.listOf np.int;
      p = v: !(isList v) || all pInt v;
      ok = [ 1 ];
      bad = [ 20 ];
    };
    attrsOf = {
      t = np.attrsOf np.int;
      p = pAttrs;
      ok.k = 1;
      bad.k = 20;
    };
    lazyAttrsOf = {
      t = np.lazyAttrsOf np.int;
      p = pAttrs;
      ok.k = 1;
      bad.k = 20;
    };
    int = {
      t = np.int;
      p = pInt;
      ok = 1;
      bad = 20;
    };
    either = {
      t = np.either np.int np.str;
      p = pInt;
      ok = 1;
      bad = 20;
    };
    enum = {
      t = np.enum [
        "a"
        "b"
      ];
      p = v: v != "b";
      ok = "a";
      bad = "b";
    };
  };
  spells = {
    addCheck = s: np.addCheck s.t s.p;
    check = s: s.t // { check = v: s.t.check v && s.p v; };
  };
  doors = {
    mkOptionType = gm.mkOptionType;
    defineType = gt.defineType;
    deriveType = gm.deriveType { } "drd";
  };
  # "<inner> <outer> <shape> <spelling> <arrangement>"
  cells = [
    "defineType deriveType nullOrG addCheck LL"
    "defineType deriveType nullOrG check LL"
    "defineType mkOptionType attrsOfG addCheck LL"
    "defineType mkOptionType attrsOfG addCheck TL"
    "defineType mkOptionType attrsOfG check LL"
    "defineType mkOptionType attrsOfG check TL"
    "defineType mkOptionType listOfG addCheck LL"
    "defineType mkOptionType listOfG addCheck TL"
    "defineType mkOptionType listOfG check LL"
    "defineType mkOptionType listOfG check TL"
    "defineType mkOptionType nullOrG addCheck LL"
    "defineType mkOptionType nullOrG addCheck TL"
    "defineType mkOptionType nullOrG check LL"
    "defineType mkOptionType nullOrG check TL"
    "deriveType defineType nullOrG addCheck LL"
    "deriveType defineType nullOrG check LL"
    "deriveType deriveType nullOrG addCheck LL"
    "deriveType deriveType nullOrG check LL"
    "mkOptionType defineType attrsOf addCheck LL"
    "mkOptionType defineType attrsOf addCheck TL"
    "mkOptionType defineType attrsOf check LL"
    "mkOptionType defineType attrsOf check TL"
    "mkOptionType defineType either addCheck LL"
    "mkOptionType defineType either addCheck TL"
    "mkOptionType defineType either check LL"
    "mkOptionType defineType either check TL"
    "mkOptionType defineType enum addCheck LL"
    "mkOptionType defineType enum addCheck TL"
    "mkOptionType defineType enum check LL"
    "mkOptionType defineType enum check TL"
    "mkOptionType defineType int addCheck LL"
    "mkOptionType defineType int addCheck TL"
    "mkOptionType defineType int check LL"
    "mkOptionType defineType int check TL"
    "mkOptionType defineType lazyAttrsOf addCheck LL"
    "mkOptionType defineType lazyAttrsOf addCheck TL"
    "mkOptionType defineType lazyAttrsOf check LL"
    "mkOptionType defineType lazyAttrsOf check TL"
    "mkOptionType defineType listOf addCheck LL"
    "mkOptionType defineType listOf addCheck TL"
    "mkOptionType defineType listOf check LL"
    "mkOptionType defineType listOf check TL"
    "mkOptionType defineType listOfG addCheck TL"
    "mkOptionType defineType listOfG check TL"
    "mkOptionType defineType nullOrG addCheck LL"
    "mkOptionType defineType nullOrG addCheck TL"
    "mkOptionType defineType nullOrG check LL"
    "mkOptionType defineType nullOrG check TL"
    "mkOptionType deriveType nullOrG addCheck LL"
    "mkOptionType deriveType nullOrG check LL"
  ];
  cell =
    c:
    let
      w = filter isString (split " " c);
      at = elemAt w;
      s = shapes.${at 2};
      x = doors.${at 1} (doors.${at 0} (spells.${at 3} s));
      ts =
        {
          LL = [
            x
            x
          ];
          TL = [
            s.t
            x
          ];
        }
        .${at 4};
    in
    {
      name = "test-${replaceStrings [ " " ] [ "-" ] c}";
      value = {
        expr = {
          ok = run ts [ s.ok ];
          bad = run ts [ s.bad ];
        };
        expected = {
          inherit (s) ok;
          bad = "REFUSED";
        };
      };
    };
  # ★ den-hoag-1b55t's BOUNDARY, PINNED: a caller's check laid ON a door's return and then re-doored
  # (`mkOptionType (addCheck (mkOptionType (addCheck int p)) q)`, declared twice) serves 5, which `q`
  # rejects (a silent value), while the same `q` on a gen constructor record behind one door refuses it.
  # The closure reaches the checks a door was handed, not one a caller lays on its return. The landing
  # that settles den-hoag-1b55t flips `laid-on-the-return-bad`.
  laidOn =
    let
      q = x: x != 5;
      composed = gm.mkOptionType (np.addCheck (gm.mkOptionType (np.addCheck np.int pInt)) q);
      gen = gm.mkOptionType (np.addCheck gt.int q);
    in
    {
      expr = {
        laid-on-the-return = run [ composed composed ] [ 3 ];
        laid-on-the-return-bad = run [ composed composed ] [ 5 ];
        gen-bad = run [ gen gen ] [ 5 ];
      };
      expected = {
        laid-on-the-return = 3;
        laid-on-the-return-bad = 5;
        gen-bad = "REFUSED";
      };
    };
in
{
  flake.tests.door-return-re-doored = listToAttrs (map cell cells) // {
    test-a-check-laid-on-a-door-s-return-then-re-doored-is-pinned = laidOn;
  };
}
