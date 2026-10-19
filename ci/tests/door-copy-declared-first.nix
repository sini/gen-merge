# A door copy declared FIRST, its completion declared later, under nixpkgs' own `evalModules`: nixpkgs merges the two
# by calling the LATER declaration's relation on the EARLIER one's functor, and that relation is gen's, so it owes the
# copy's `verify` (ADR-0039: the meet, read by gen's code inside nixpkgs' engine). The copy's functor names the copy as
# the declaration (`__declared`) beside its completion's `type`, which stays the completion (ADR-0034), and the
# exported `typeMerge` meets the join with that declaration, on its derived arm and on the arm retaining an author's
# relation (den-hoag-s1um3).
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  inherit (builtins) deepSeq mapAttrs tryEval;
  doors = {
    inherit (gt) defineType;
    inherit (gm) mkOptionType;
  };
  readNp =
    tys: v:
    let
      x =
        (nl.evalModules {
          modules = map (t: { options.x = nl.mkOption { type = t; }; }) tys ++ [ { x = v; } ];
        }).config.x;
      o = tryEval (deepSeq x x);
    in
    if o.success then o.value else "REFUSED";
  read =
    tys: v:
    let
      x =
        (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) tys ++ [ { x = v; } ]))
        .config.x;
      o = tryEval (deepSeq x x);
    in
    if o.success then o.value else "REFUSED";
  notSeven = v: if v == 7 then "seven is out" else null;
  # LT = the copy first; TL (the reversed order) and the copy alone are the controls
  rows = base: c: {
    ltBad = readNp [
      c
      base
    ] 7;
    ltOk = readNp [
      c
      base
    ] 3;
    tlBad = readNp [
      base
      c
    ] 7;
    onceBad = readNp [ c ] 7;
  };
  met = {
    ltBad = "REFUSED";
    ltOk = 3;
    tlBad = "REFUSED";
    onceBad = "REFUSED";
  };
  # a record stating its OWN relation (`functor.binOp`) beside its own `verify`, as gen-schema's `refined` does: its
  # export keeps the author's `typeMerge` (`retainedRelation`), whose join here is the record itself
  rel =
    let
      r0 = gm.mkOptionType (
        builtins.removeAttrs gt.int [
          "functor"
          "typeMerge"
          "__mint"
          "__okAt"
          "__payload"
          "__sealed"
          "__typeSelf"
        ]
        // gt.mkIdentity "door-copy-declared-first" [ gt.int ] (tags: {
          base = builtins.head tags;
        }) [ ] "intRel"
        // {
          verify = _: null;
          typeMerge = f: if (f.name or null) == "intRel" then r0 else null;
          functor = {
            name = "intRel";
            type = r0;
            payload = null;
            binOp = _: _: null;
          };
        }
      );
    in
    r0;
  Td = gt.typedef { } "td" builtins.isInt;
in
{
  flake.tests.door-copy-declared-first = {
    # RED (the copy's `verify` dropped, `7` served LT) without the slot or without the derived arm's meet
    test-a-leaf-copy-declared-first-is-met-by-the-later-relation = {
      expr = mapAttrs (_: d: rows gt.int (d (gt.int // { verify = notSeven; }))) doors;
      expected = mapAttrs (_: _: met) doors;
    };
    # RED (`7` served LT) without the retained arm's meet: the later relation is the author's, and gen runs it
    test-a-copy-declared-first-is-met-by-a-retained-relation = {
      expr = mapAttrs (_: d: rows rel (d (rel // { verify = notSeven; }))) doors;
      expected = mapAttrs (_: _: met) doors;
    };
    # The slot moves no identity: `functor.type` is the completion, gen-types' readers refuse the copy by name, and gen's
    # engine meets it beside its completion in both orders (1 rejected, 2 served)
    test-the-declaration-slot-leaves-the-completion-the-type = {
      expr = mapAttrs (
        _: d:
        let
          c = d (Td // { verify = v: if v == 1 then "no" else null; });
          refused = e: !(tryEval (deepSeq e e)).success;
        in
        {
          typeIsCompletion = c.functor.type == (Td.__typeSelf null) || c.functor.type == Td;
          slotIsCopy = (c.functor.__declared or null) == c;
          redoorSlot = (d c).functor ? __declared;
          idOfRefused = refused (genTypes.idOf c);
          typeEqRefused = refused (gt.typeEq Td c);
          gen = [
            (read [ Td c ] 1)
            (read [ Td c ] 2)
            (read [ c Td ] 1)
            (read [ c Td ] 2)
          ];
        }
      ) doors;
      expected = mapAttrs (_: _: {
        typeIsCompletion = true;
        slotIsCopy = true;
        redoorSlot = true;
        idOfRefused = true;
        typeEqRefused = true;
        gen = [
          "REFUSED"
          2
          "REFUSED"
          2
        ];
      }) doors;
    };
  };
}
