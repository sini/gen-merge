# THE COMPLETION STAMP AT THE PROTOCOL BOUNDARY (gate C3, ruled arm (c)). The boundary rebuilds every
# record it imports and exports and re-ties the stamp to what it completes, so every exported type is
# decided as before; a `//` copy entering it is served, unminted, and `typeEq` refuses it by name.
{
  genMerge,
  interface,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  inherit (builtins) deepSeq tryEval;
  refused = e: !(tryEval (deepSeq e e)).success;
  ev =
    tys: val:
    let
      p =
        (gm.evalModuleTree { } (
          map (ty: { options.p = gm.mkOption { type = ty; }; }) tys ++ [ { p = val; } ]
        )).config.p;
      r = tryEval (deepSeq p p);
    in
    if r.success then r.value else "REFUSED";
  via =
    ty: v:
    (gm.evalModuleTree { } [
      { options.k = gm.mkOption { type = ty; }; }
      { config.k = v; }
    ]).config.k;
  posT = t.refined t.int {
    check = v: v > 0;
    message = "positive";
  };
  slash = t.int // {
    verify = _: null;
  };
  # the record the import boundary completes from `ty`
  imported = ty: (interface.importType ty).imported;
in
{
  flake.tests.completion-stamp-boundary = {
    # Every exported type is decided as before: the boundary re-tied its stamp.
    test-exported-types-decide-as-before = {
      expr = {
        strSelf = t.typeEq t.str t.str;
        intStr = t.typeEq t.int t.str;
        enumTwins = t.typeEq (t.enum "e" [ "a" ]) (t.enum "e" [ "a" ]);
        posTThroughAnything = t.typeEq posT (via t.anything posT);
      };
      expected = {
        strSelf = true;
        intStr = false;
        enumTwins = true;
        posTThroughAnything = true;
      };
    };
    # A `//` copy is refused by name at `typeEq`, directly and after the boundary imported it.
    test-a-slash-copy-is-refused-at-typeEq = {
      expr = {
        direct = refused (t.typeEq t.int slash);
        afterAnything = refused (t.typeEq t.int (via t.anything slash));
        # through the import boundary: served, unminted, its stale witness kept, refused by name
        afterImport = refused (t.typeEq t.int (imported slash));
        importedMinted = (imported slash).__mint ? minted;
        # the control: an honest type through the same door is re-tied and decides
        honestImport = t.typeEq t.int (imported t.int);
      };
      expected = {
        direct = true;
        afterAnything = true;
        afterImport = true;
        importedMinted = false;
        honestImport = true;
      };
    };
    # Redeclaring `int` beside the copy, in both orders, still refuses `"x"` and admits 3; the copy
    # declared alone is served (it is imported, unminted, never refused at import).
    test-redeclaration-beside-the-copy-is-unchanged = {
      expr = {
        intThenCopyX = ev [ t.int slash ] "x";
        copyThenIntX = ev [ slash t.int ] "x";
        intThenCopy3 = ev [ t.int slash ] 3;
        copyAloneServes = ev [ slash ] "x";
      };
      expected = {
        intThenCopyX = "REFUSED";
        copyThenIntX = "REFUSED";
        intThenCopy3 = 3;
        copyAloneServes = "x";
      };
    };
    # THE PRICE, stated and pinned: a description-only `//` (the nixpkgs idiom) is a copy too, so
    # `typeEq` refuses it; as an option type it is still served.
    test-a-description-only-copy-pays-the-price = {
      expr = {
        typeEq = refused (t.typeEq t.str (t.str // { description = "a label"; }));
        served = ev [ (t.str // { description = "a label"; }) ] "x";
      };
      expected = {
        typeEq = true;
        served = "x";
      };
    };
  };
}
