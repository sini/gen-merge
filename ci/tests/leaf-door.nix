# A nixpkgs leaf through either `mkOptionType` door, declared beside gen's own leaf, is joined as its raw form is.
# Each cell is read by gen's engine and, over nixpkgs' own twin of the same declarations, by nixpkgs'
# `lib.evalModules`, each as JSON or `"REFUSED"`. RED (the class cells `"REFUSED"`) where gen's leaf relation read
# the door's return as a gen leaf of another name and never consulted its embedding. A door partner's own check,
# rejected where nixpkgs drops it, is pinned on the error plane (`ci/tests-error.nix`, `leaf-door`).
# Two, three and four declarations are read in every order (below): the declared type is met at every step of the
# fold, a held step included, so a checked partner's check is kept whatever follows it.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib.types;
  doors = {
    d1 = gm.mkOptionType;
    d2 = gm.types.mkOptionType;
  };
  json =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x (builtins.toJSON x));
    in
    if r.success then r.value else "REFUSED";
  gen =
    ts: v:
    json
      (gm.evalModuleTree { } (map (ty: { options.x = gm.mkOption { type = ty; }; }) ts ++ [ { x = v; } ]))
      .config.x;
  nixpkgs =
    ts: v:
    json
      (nixpkgsLib.evalModules {
        modules = map (ty: { options.x = nixpkgsLib.mkOption { type = ty; }; }) ts ++ [ { x = v; } ];
      }).config.x;
  # each row: gen's leaf `g`, nixpkgs' twin of it `n`, the partner `p` and the values it is read at
  classRows = {
    str = {
      g = t.str;
      n = np.str;
      p = np.str;
      vs = [ "s" ];
    };
    enum = {
      g = t.enum "e" [ "a" ];
      n = np.enum [ "a" ];
      p = np.enum [ "a" ];
      vs = [ "a" ];
    };
    # the enum-union law: the partner's own member is served, a member of neither is refused
    enumAB = {
      g = t.enum "e" [ "a" ];
      n = np.enum [ "a" ];
      p = np.enum [ "b" ];
      vs = [
        "a"
        "b"
        "c"
      ];
    };
    number = {
      g = t.number;
      n = np.number;
      p = np.number;
      vs = [
        2
        1.5
      ];
    };
    # a door partner's own check, at a value it accepts (the rejected value is on the error plane)
    checkedStr = {
      g = t.str;
      n = np.str;
      p = np.addCheck np.str (s: s != "bad");
      vs = [ "ok" ];
    };
    checkedEnum = {
      g = t.enum "e" [
        "a"
        "b"
      ];
      n = np.enum [
        "a"
        "b"
      ];
      p = np.addCheck (np.enum [
        "a"
        "b"
      ]) (v: v != "b");
      vs = [ "a" ];
    };
    checkedNumber = {
      g = t.number;
      n = np.number;
      p = np.addCheck np.number (x: x > 0);
      vs = [ 2 ];
    };
  };
  # the leaves whose door return the leaf relation already joined, and a different leaf through the door
  controlRows = {
    int = {
      g = t.int;
      n = np.int;
      p = np.int;
      vs = [ 2 ];
    };
    bool = {
      g = t.bool;
      n = np.bool;
      p = np.bool;
      vs = [ true ];
    };
    float = {
      g = t.float;
      n = np.float;
      p = np.float;
      vs = [ 1.5 ];
    };
    path = {
      g = t.path;
      n = np.path;
      p = np.path;
      vs = [ "/etc" ];
    };
    anything = {
      g = t.anything;
      n = np.anything;
      p = np.anything;
      vs = [ 2 ];
    };
    raw = {
      g = t.raw;
      n = np.raw;
      p = np.raw;
      vs = [ 2 ];
    };
    unspecified = {
      g = t.unspecified;
      n = np.unspecified;
      p = np.unspecified;
      vs = [ 2 ];
    };
    strBesideInt = {
      g = t.str;
      n = np.str;
      p = np.int;
      vs = [ "s" ];
    };
    enumBesideStr = {
      g = t.enum "e" [ "a" ];
      n = np.enum [ "a" ];
      p = np.str;
      vs = [ "a" ];
    };
    numberBesideStr = {
      g = t.number;
      n = np.number;
      p = np.str;
      vs = [ 2 ];
    };
  };
  # every door, both orders, and one level down under `listOf` and `attrsOf`; `read` is the engine, `side` maps
  # a row to its operands (gen's leaf with the door, or nixpkgs' twin with the bare partner)
  cells =
    read: side: rows:
    builtins.mapAttrs (
      _: r:
      builtins.mapAttrs (
        door: d:
        let
          o = side d r;
        in
        map (v: {
          TL = read [ o.a o.b ] v;
          LT = read [ o.b o.a ] v;
          listOf = read [ (o.list o.a) (o.list o.b) ] [ v ];
          attrsOf = read [ (o.attrs o.a) (o.attrs o.b) ] { k = v; };
        }) r.vs
      ) doors
    ) rows;
  genSide = d: r: {
    a = r.g;
    b = d r.p;
    list = t.listOf;
    attrs = t.attrsOf;
  };
  npSide = _: r: {
    a = r.n;
    b = r.p;
    list = np.listOf;
    attrs = np.attrsOf;
  };
  # ── N DECLARATIONS ── every ordered list of 2, 3 or 4 distinct members: `C` and `D` two nixpkgs
  # leaves under DISTINCT checks, `N` the plain nixpkgs leaf, `G` gen's leaf. Each is read at a value every check
  # accepts and at one each check rejects. The lawful answer is the ALONE oracle: a value is served iff every
  # declaration declared alone serves it, at nixpkgs' value over its own twin; otherwise refused (THE MEET; nixpkgs
  # serves those only by dropping the check).
  members = {
    str = {
      leaf = np.str;
      g = t.str;
      c1 = s: s != "bad";
      c2 = s: s != "worse";
      vals = [
        "s"
        "bad"
        "worse"
      ];
    };
    enum = {
      leaf = np.enum [
        "a"
        "b"
        "c"
      ];
      g = t.enum "e" [
        "a"
        "b"
        "c"
      ];
      c1 = v: v != "b";
      c2 = v: v != "c";
      vals = [
        "a"
        "b"
        "c"
      ];
    };
    int = {
      leaf = np.int;
      g = t.int;
      c1 = x: x > 0;
      c2 = x: x != 2;
      vals = [
        3
        (-1)
        2
      ];
    };
    number = {
      leaf = np.number;
      g = t.number;
      c1 = x: x > 0;
      c2 = x: x != 2;
      vals = [
        3
        (-1)
        2
      ];
    };
  };
  member =
    k: m:
    {
      C = np.addCheck members.${k}.leaf members.${k}.c1;
      D = np.addCheck members.${k}.leaf members.${k}.c2;
      N = members.${k}.leaf;
      G = members.${k}.g;
    }
    .${m};
  perms =
    xs:
    if xs == [ ] then
      [ [ ] ]
    else
      builtins.concatMap (x: map (p: [ x ] ++ p) (perms (builtins.filter (y: y != x) xs))) xs;
  subsets =
    xs:
    if xs == [ ] then
      [ [ ] ]
    else
      let
        r = subsets (builtins.tail xs);
      in
      r ++ map (s: [ (builtins.head xs) ] ++ s) r;
  orders = builtins.concatMap perms (
    builtins.filter (s: builtins.length s >= 2) (subsets [
      "C"
      "D"
      "N"
      "G"
    ])
  );
  # one cell per (kind, order, value) under `read`, over each member through `door`
  declared =
    read: door:
    builtins.mapAttrs (
      k: r:
      builtins.listToAttrs (
        map (o: {
          name = builtins.concatStringsSep "" o;
          value = map (read (map (m: if m == "G" then r.g else door (member k m)) o)) r.vals;
        }) orders
      )
    ) members;
  lawful = builtins.mapAttrs (
    k: r:
    builtins.listToAttrs (
      map (o: {
        name = builtins.concatStringsSep "" o;
        value = map (
          v:
          if builtins.all (m: gen [ (member k m) ] v != "REFUSED") o then
            nixpkgs (map (m: if m == "G" then r.leaf else member k m) o) v
          else
            "REFUSED"
        ) r.vals;
      }) orders
    )
  ) members;
in
{
  flake.tests.leaf-door = {
    test-a-nixpkgs-leaf-through-a-door-beside-gen-leaf-reads-nixpkgs-value = {
      expr = cells gen genSide classRows;
      expected = cells nixpkgs npSide classRows;
    };
    test-the-leaves-already-joined-and-a-different-leaf-read-nixpkgs-value = {
      expr = cells gen genSide controlRows;
      expected = cells nixpkgs npSide controlRows;
    };
    # RED: a held step dropped a checked door partner's check at the third declaration (`[C, N, G]` served "bad"),
    # and `int` `[C, G, N]` did on main before the leaf guards
    test-n-declarations-through-the-door-serve-only-what-every-declaration-accepts = {
      expr = {
        d1 = declared gen doors.d1;
        d2 = declared gen doors.d2;
      };
      expected = {
        d1 = lawful;
        d2 = lawful;
      };
    };
    test-n-declarations-through-the-door-read-as-their-raw-forms = {
      expr = {
        d1 = declared gen doors.d1;
        d2 = declared gen doors.d2;
      };
      expected = {
        d1 = declared gen (x: x);
        d2 = declared gen (x: x);
      };
    };
  };
}
