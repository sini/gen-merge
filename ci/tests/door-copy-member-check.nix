# A door copy of a nixpkgs container whose MEMBER carries the check (`listOf (addCheck int p)` and its kin), declared
# twice under nixpkgs' own `evalModules` (den-hoag-f3uez). nixpkgs' join rebuilds the container from its functor's
# payload, and `addCheck` keeps its base's functor, so the join's member is the bare `int` and the member check is gone.
# The door's closure lays the copy's debt back on the join (`rebuildClosed.own`), and that debt is the copy's
# membership at every depth: its `check`, which reads a container at its own depth only, and its own merge of the value
# as one definition (ADR-0039: the meet, read by gen's code inside nixpkgs' engine). Every value the member check
# rejects is refused, in both orders (the copy twice; the plain container first, the copy later), and every value it
# admits is served as nixpkgs' twin serves it. Controls: one declaration, and gen's engine, refuse as before. A copy
# whose member is an ad-hoc `type // { check }` (v2-incoherent, refused by nixpkgs' coherence guard on its own merge)
# keeps the shallow debt, so the values it admits stay served. A container over a checked module set, declared once,
# is closed by the same debt where its closure has no base (`o`).
# Red at gen-merge 453e597: `redeclared` (every `bad` served) and `one-declaration-module-set` (every `bad` served).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    deepSeq
    listToAttrs
    mapAttrs
    tryEval
    ;
  L = np.addCheck np.int (v: v != 1);
  opt = type: nl.mkOption { inherit type; };
  tagOf = s: np.attrTag { t = opt s; };
  shapes = {
    list = {
      mk = np.listOf;
      w = v: [ v ];
    };
    attrs = {
      mk = np.attrsOf;
      w = v: { k = v; };
    };
    tag = {
      mk = tagOf;
      w = v: { t = v; };
    };
    listTag = {
      mk = s: np.listOf (tagOf s);
      w = v: [ { t = v; } ];
    };
    tagTag = {
      mk = s: np.attrTag { u = opt (tagOf s); };
      w = v: { u.t = v; };
    };
  };
  readNp =
    tys: v:
    let
      x =
        (nl.evalModules {
          modules = map (t: { options.x = opt t; }) tys ++ [ { x = v; } ];
        }).config.x;
      o = tryEval (deepSeq x x);
    in
    if o.success then o.value else "REFUSED";
  readGen =
    tys: v:
    let
      x =
        (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) tys ++ [ { x = v; } ]))
        .config.x;
      o = tryEval (deepSeq x x);
    in
    if o.success then o.value else "REFUSED";
  orders = s: x: {
    copies = [
      x
      x
    ];
    plainFirst = [
      (s.mk np.int)
      x
    ];
  };
  cells =
    read:
    mapAttrs (
      _: s:
      mapAttrs (_: tys: {
        bad = read tys (s.w 1);
        ok = read tys (s.w 2);
      }) (orders s (gm.mkOptionType (s.mk L)))
    ) shapes;
  # the twin: nixpkgs' own value for an admitted definition, the same declarations without the door
  want = mapAttrs (
    _: s:
    mapAttrs (_: tys: {
      bad = "REFUSED";
      ok = readNp tys (s.w 2);
    }) (orders s (s.mk L))
  ) shapes;
  sub = np.submodule {
    options.a = nl.mkOption {
      type = np.int;
      default = 0;
    };
  };
  adHoc = np.listOf (sub // { check = v: sub.check v && (v.a or 0) != 2; });
  # a container over a checked module set, declared once: nixpkgs' fixup asks the copy's `substSubModules`, gen's code,
  # whose closure has no base to relativise to (`own`'s `o`)
  sets = {
    listOf = v: [ v ];
    attrsOf = v: { k = v; };
    lazyAttrsOf = v: { k = v; };
  };
  checkedSub = np.addCheck sub (v: (v.a or 0) != 2);
in
{
  flake.tests.door-copy-member-check = {
    test-redeclared = {
      expr = cells readNp;
      expected = want;
    };
    test-one-declaration = {
      expr = mapAttrs (_: s: {
        bad = readNp [ (gm.mkOptionType (s.mk L)) ] (s.w 1);
        ok = readNp [ (gm.mkOptionType (s.mk L)) ] (s.w 2);
      }) shapes;
      expected = mapAttrs (_: s: {
        bad = "REFUSED";
        ok = readNp [ (s.mk L) ] (s.w 2);
      }) shapes;
    };
    test-one-declaration-module-set = {
      expr = mapAttrs (n: w: {
        bad = readNp [ (gm.mkOptionType (np.${n} checkedSub)) ] (w {
          a = 2;
        });
        ok = readNp [ (gm.mkOptionType (np.${n} checkedSub)) ] (w {
          a = 1;
        });
      }) sets;
      expected = mapAttrs (n: w: {
        bad = "REFUSED";
        ok = readNp [ (np.${n} checkedSub) ] (w {
          a = 1;
        });
      }) sets;
    };
    test-gen-engine = {
      expr = mapAttrs (_: mapAttrs (_: c: c.bad)) (cells readGen);
      expected = mapAttrs (_: mapAttrs (_: _: "REFUSED")) want;
    };
    test-ad-hoc-member-served = {
      expr = listToAttrs (
        map
          (n: {
            name = toString n;
            value = readNp (builtins.genList (_: gm.mkOptionType adHoc) n) [ { a = 1; } ];
          })
          [
            1
            2
          ]
      );
      expected = listToAttrs (
        map
          (n: {
            name = toString n;
            value = readNp (builtins.genList (_: adHoc) n) [ { a = 1; } ];
          })
          [
            1
            2
          ]
      );
    };
  };
}
