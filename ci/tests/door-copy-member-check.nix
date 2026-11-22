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
# A value read lazily (an unread undefined option, an unread throwing element, a field read from the option's own
# config) reads as nixpkgs reads it (`lazy-read`): the member check is read per element by the join's merge, never forced.
# Red at gen-merge cb8ccbd: `redeclared`, `one-declaration-module-set` and `lazy-read` (every rejected value served).
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
  # read LAZILY, one leaf (`config.x.k.a`), as a configuration reads it: a container over a submodule through the door,
  # declared once or twice; the member is plain or checked (a != 2). `undef`: a member option with no default, never
  # defined, never read; `lazy`: a `lazyAttrsOf` sibling element that throws, never read; `selfref`: a member field
  # defined from the option's own config. Every value the checks admit reads as nixpkgs' twin reads it, forcing nothing
  # nixpkgs leaves unread; the value the member's check rejects is refused
  lazyo =
    let
      full = np.submodule {
        options.a = nl.mkOption { type = np.int; };
        options.b = nl.mkOption {
          type = np.int;
          default = 0;
        };
      };
      req = np.submodule {
        options.a = nl.mkOption { type = np.int; };
        options.req = nl.mkOption { type = np.int; };
      };
      cases = {
        undef = {
          s = req;
          c = np.attrsOf;
          v = a: _: { k = { inherit a; }; };
        };
        lazy = {
          s = full;
          c = np.lazyAttrsOf;
          v = a: _: {
            k = { inherit a; };
            j = throw "unread element";
          };
        };
        selfref = {
          s = full;
          c = np.attrsOf;
          v = a: config: {
            k = {
              inherit a;
              b = config.x.k.a + 1;
            };
          };
        };
      };
      members = s: {
        plain = s;
        checked = np.addCheck s (v: (v.a or 0) != 2);
      };
      read =
        door: n: cs: m: a:
        let
          ty = if door then gm.mkOptionType (cs.c m) else cs.c m;
          x =
            (nl.evalModules {
              modules = builtins.genList (_: { options.x = opt ty; }) n ++ [
                ({ config, ... }: { x = cs.v a config; })
              ];
            }).config.x.k.a;
          o = tryEval x;
        in
        if o.success then o.value else "REFUSED";
      grid =
        door:
        mapAttrs (
          _: cs:
          mapAttrs (
            mn: m:
            listToAttrs (
              map
                (n: {
                  name = "n${toString n}";
                  value = {
                    admitted = read door n cs m 1;
                    rejected = read door n cs m 2;
                  };
                })
                [
                  1
                  2
                ]
            )
          ) (members cs.s)
        ) cases;
    in
    {
      expr = grid true;
      # the twin's value, and the checked member's rejected value refused
      expected = mapAttrs (
        _: mapAttrs (mn: mapAttrs (_: c: if mn == "checked" then c // { rejected = "REFUSED"; } else c))
      ) (grid false);
    };
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
    test-lazy-read = lazyo;
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
