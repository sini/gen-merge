# gen-merge: a nixpkgs `attrTag` returned by the `mkOptionType` door (either door, `gm.mkOptionType` and
# `types.mkOptionType`) and declared as several declarations of one option keeps the RECEIVER'S tag checks in nixpkgs'
# `lib.evalModules` (den-hoag-yg7fo S1). nixpkgs reverses the declaration list, so the last declaration is the receiver,
# and the door return's `typeMerge` closes each join over the receiver's debt, which is gen's code there (ADR-0039: a gen
# function called inside nixpkgs' evaluation enforces its checks). An attrTag's base is the attrTag itself, so its debt
# is owed one level down: each tag the receiver declares owes its declared type relative to its own parameters, and
# the receiver its own shallow check. A tag the receiver does not declare is owed nothing (nixpkgs' join unions the tag
# sets) and is not forced.
#
# Each cell is one (shape, definition, word, door), read in nixpkgs' evaluation, against its LAW verdict, never against
# the word's spelling alone: a definition some declared check rejects is refused (`"REFUSED"`), a lawful one is served
# at its own value. A word is the declarations in order, one letter each: `u` the unchecked type, `c` the checked one;
# every word of length 1 to 4. The rejected definition is read on the receiver-checked words (ending in `c`) and the
# unchecked ones; a word whose `c` is only a partner's is the partner's debt, outside this cell. Enum union at a tag
# (ADR-0034, ADR-0039) and a submodule tag (a nested stock evaluation, nixpkgs' own) are read on every word: the
# union served wherever some declaration admits the value, the submodule at nixpkgs' undoored value.
# RED where the receiver's arm is vacuous (the rejected definitions served), where its tag debt or its shallow check
# is dropped, where a tag the receiver does not declare is owed (the undeclared-tag value refused) or forced, and where
# a tag's type is owed whole rather than relative to its parameters (the enum union refused).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins) deepSeq tryEval;
  read =
    v:
    let
      r = tryEval (deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
  opt = ty: nl.mkOption { type = ty; };
  sub = np.submodule {
    options.a = nl.mkOption {
      type = np.str;
      default = "x";
    };
  };
  # a foreign leaf whose functor's payload differs between its checked and unchecked forms, with a constant join
  K0 =
    let
      K =
        nl.mkOptionType {
          name = "kint";
          check = builtins.isInt;
          merge = nl.mergeEqualOption;
          functor = {
            name = "kint";
            type = null;
            wrapped = null;
            payload = { };
            binOp = _: _: null;
          };
        }
        // {
          typeMerge = _: K;
        };
    in
    K;
  Kc = K0 // {
    check = v: K0.check v && v != 1;
    functor = K0.functor // {
      payload.keep = true;
    };
  };
  leaf = {
    u = np.int;
    c = np.addCheck np.int (v: v != 1);
  };
  kleaf = {
    u = K0;
    c = Kc;
  };
  tagOf =
    b:
    np.attrTag {
      a = opt sub;
      b = opt b;
    };
  tagU = tagOf np.int;
  # the declared types, by letter
  shapes = {
    tag = k: tagOf leaf.${k};
    Ktag = k: tagOf kleaf.${k};
    tag1 = k: np.attrTag { b = opt leaf.${k}; };
    tagNest = k: tagOf (np.attrTag { x = opt leaf.${k}; });
    tagNull = k: tagOf (np.nullOr leaf.${k});
    tagEither = k: tagOf (np.either leaf.${k} np.str);
    tagOther =
      k:
      np.attrTag {
        a = opt sub;
        b = opt np.int;
        y = opt leaf.${k};
      };
    # the tag sets differ: nixpkgs' join declares `b` and `z`, the checked receiver `b` alone
    tagWide =
      k:
      if k == "u" then
        np.attrTag {
          b = opt np.int;
          z = opt np.int;
        }
      else
        np.attrTag { b = opt leaf.c; };
    # the receiver's own check, on the attrTag itself
    tagTop = k: if k == "u" then tagU else np.addCheck tagU (v: !(v ? b && v.b == 1));
    tagEnum =
      k:
      tagOf (
        if k == "u" then
          np.enum [
            1
            2
          ]
        else
          np.enum [ 2 ]
      );
    tagSub = k: tagOf (np.submodule { options.x = opt leaf.${k}; });
  };
  doors = {
    d1 = gm.mkOptionType;
    d2 = gm.types.mkOptionType;
  };
  decls =
    door: ty: w:
    map (k: { options.o = opt (door (ty k)); }) (nl.stringToCharacters w);
  eval =
    door: ty: w: def:
    read (nl.evalModules { modules = decls door ty w ++ [ { config.o = def; } ]; }).config.o;
  allWords =
    n:
    if n == 0 then
      [ "" ]
    else
      nl.concatMap (w: [
        "${w}u"
        "${w}c"
      ]) (allWords (n - 1));
  words = nl.concatMap allWords [
    1
    2
    3
    4
  ];
  has = l: w: nl.hasInfix l w;
  receiverOrPlain = builtins.filter (w: nl.hasSuffix "c" w || !(has "c" w)) words;
  # one cell per (word, door): `expr` the served value, `expected` its law verdict
  cells = ty: ws: def: verdict: {
    expr = builtins.mapAttrs (_: door: nl.genAttrs ws (w: eval door ty w def)) doors;
    expected = builtins.mapAttrs (_: door: nl.genAttrs ws (w: verdict door w)) doors;
  };
  # a definition a checked declaration rejects: refused on a word with a receiver check, served on an unchecked word
  rejected = ty: def: cells ty receiverOrPlain def (_: w: if has "c" w then "REFUSED" else def);
  admitted = ty: def: cells ty words def (_: _: def);
  bad = {
    tag.b = 1;
    Ktag.b = 1;
    tag1.b = 1;
    tagNest.b.x = 1;
    tagNull.b = 1;
    tagEither.b = 1;
    tagOther.y = 1;
    tagWide.b = 1;
    tagTop.b = 1;
  };
  good = {
    tag.b = 2;
    Ktag.b = 2;
    tag1.b = 2;
    tagNest.b.x = 2;
    tagNull.b = 2;
    tagEither.b = 2;
    tagOther.b = 1;
    tagWide.b = 2;
    tagTop.b = 2;
  };
  # a tag only the unchecked declarations declare, its value a throw: forced, the cell reads `"REFUSED"`
  names =
    door: w:
    let
      x =
        (nl.evalModules {
          modules = decls door shapes.tagWide w ++ [ { config.o.z = throw "z forced"; } ];
        }).config.o;
      r = tryEval (deepSeq (builtins.attrNames x) (builtins.attrNames x));
    in
    if r.success then r.value else "REFUSED";
  stock = def: cells shapes.tagSub words def (_: w: eval (d: d) shapes.tagSub w def);
in
{
  flake.tests.attrtag-receiver-tag-debt =
    nl.mapAttrs' (
      sh: def:
      nl.nameValuePair "test-a-receivers-declared-tag-check-is-enforced-${sh}" (rejected shapes.${sh} def)
    ) bad
    // nl.mapAttrs' (
      sh: def: nl.nameValuePair "test-an-admitted-value-is-served-${sh}" (admitted shapes.${sh} def)
    ) good
    // {
      # the tag only the unchecked declarations declare is served wherever one of them is declared, and refused
      # where none is (nixpkgs' own refusal)
      test-a-tag-the-receiver-does-not-declare-is-served = cells shapes.tagWide receiverOrPlain {
        z = 1;
      } (_: w: if has "u" w then { z = 1; } else "REFUSED");
      test-a-tag-the-receiver-does-not-declare-is-not-forced =
        let
          ws = builtins.filter (w: has "u" w && nl.hasSuffix "c" w) words;
        in
        {
          expr = builtins.mapAttrs (_: door: nl.genAttrs ws (names door)) doors;
          expected = builtins.mapAttrs (_: _: nl.genAttrs ws (_: [ "z" ])) doors;
        };
      # an enum union at a tag admits what some declaration's enum admits, in every order
      test-an-enum-union-tag-is-served = cells shapes.tagEnum words { b = 1; } (
        _: w: if has "u" w then { b = 1; } else "REFUSED"
      );
      test-an-enum-union-tag-admits-the-common-value = admitted shapes.tagEnum { b = 2; };
      # a submodule tag's fold is nixpkgs' own nested evaluation: every cell at nixpkgs' undoored value
      test-a-submodule-tag-is-nixpkgs-value-rejected = stock { b.x = 1; };
      test-a-submodule-tag-is-nixpkgs-value-admitted = stock { b.x = 2; };
    };
}
