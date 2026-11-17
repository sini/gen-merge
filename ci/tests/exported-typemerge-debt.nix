# What gen's exported `typeMerge` owes under nixpkgs' own `evalModules` (ADR-0039, the doors clause and THE MEET). Every
# cell mounts gen declarations in nixpkgs' engine, which folds a redeclared option by asking each accumulated type's
# `typeMerge` with the next declaration's functor, and reads the value against the declarations' checks, computed per
# cell (a value is owed a refusal when some declaration's check rejects it):
#   - a check-only door copy names itself as the declaration (`functor.__declared`) whenever it is carried, so the
#     relation that decides owes its check;
#   - a met record's typeMerge owes the partner's declaration beside itself, and is itself owed whole;
#   - a held step owes the partner's declaration, and holds the unchecked fold of one a door copy states, unless the
#     join widens its parameters; a partner recovered from its functor is owed but not held.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    all
    any
    concatMap
    deepSeq
    elem
    filter
    isInt
    isString
    tryEval
    ;
  d1 = gm.mkOptionType;
  d2 = gm.types.mkOptionType;
  doors = { inherit d1 d2; };
  chars = nl.stringToCharacters;
  readAt =
    opt: tys: v:
    let
      x =
        (nl.evalModules {
          modules = map (t: { options.${opt} = nl.mkOption { type = t; }; }) tys ++ [ { ${opt} = v; } ];
        }).config.${opt};
      o = tryEval (deepSeq x x);
    in
    if o.success then o.value else "REFUSED";
  read = readAt "x";
  admits =
    t: v:
    let
      r = tryEval (t.check v);
    in
    r.success && r.value;
  # every declaration's check admits v ⇒ served, else refused
  owed = tys: v: if all (t: admits t v) tys then v else "REFUSED";
  spell =
    o: g: p:
    map (c: if c == "G" then g else p) (chars o);
  even = v: isInt v && nl.mod v 2 == 0;
  orders = [
    "GP"
    "PG"
    "GPP"
    "PGP"
    "PPG"
    "GGP"
    "GPG"
    "PGG"
    "GGGP"
    "GGPG"
    "GGPP"
    "GPGG"
    "GPGP"
    "GPPG"
    "GPPP"
    "PGGG"
    "PGGP"
    "PGPG"
    "PGPP"
    "PPGG"
    "PPGP"
    "PPPG"
  ];
  # gen `str` beside a check-only copy of it (a door over `gt.str // { check }`), every order, both doors
  strCopy = gt.str // {
    name = "str";
    check = v: isString v && nl.hasPrefix "s" v;
  };
  copyGrid = nl.genAttrs [ "d1" "d2" ] (
    dn:
    nl.genAttrs orders (
      o:
      map
        (
          v:
          let
            tys = spell o gt.str (doors.${dn} strCopy);
          in
          {
            got = read tys v;
            want = owed [
              gt.str
              strCopy
            ] v;
          }
        )
        [
          "s"
          "x"
        ]
    )
  );
  # an author relation narrowing to positive on any `int` functor (its own check is `isInt`): its join is the author's
  # answer, so -1 is admitted by every declaration and served (as nixpkgs' twin serves it)
  narrowRecord =
    name:
    np.mkOptionType {
      inherit name;
      check = isInt;
      functor = np.defaultFunctor "int";
      typeMerge = f: if f.name == "int" then np.ints.positive else null;
    };
  narrowOrders = [
    "GPP"
    "PGP"
    "GGP"
    "GGGP"
    "GGPP"
    "GPGP"
    "GPPP"
    "PGGP"
    "PGPP"
    "PPGP"
  ];
  narrowGrid = nl.genAttrs [ "nTM" "int" ] (
    rn:
    nl.genAttrs [ "d1" "d2" ] (
      dn: nl.genAttrs narrowOrders (o: read (spell o gt.int (doors.${dn} (narrowRecord rn))) (-1))
    )
  );
  # enum extension (a union, a widening join) beside a check-only copy admitting `a` alone, every word of length 2..4:
  # v is admitted iff some declaration's parameters hold it and every declaration whose parameters hold it admits it
  onlyA = v: v == "a";
  enumPool = {
    A = {
      t = gt.enum "ab" [
        "a"
        "b"
      ];
      ps = [
        "a"
        "b"
      ];
      ck = _: true;
    };
    C = {
      t = gt.enum "c" [ "c" ];
      ps = [ "c" ];
      ck = _: true;
    };
    K = {
      t = d1 (
        gt.enum "ab" [
          "a"
          "b"
        ]
        // {
          check = onlyA;
        }
      );
      ps = [
        "a"
        "b"
      ];
      ck = onlyA;
    };
    L = {
      t = d2 (
        gt.enum "ab" [
          "a"
          "b"
        ]
        // {
          check = onlyA;
        }
      );
      ps = [
        "a"
        "b"
      ];
      ck = onlyA;
    };
  };
  ext = ws: concatMap (w: map (c: w + c) (builtins.attrNames enumPool)) ws;
  enumWords =
    let
      w2 = ext (builtins.attrNames enumPool);
      w3 = ext w2;
    in
    w2 ++ w3 ++ ext w3;
  enumWrong = concatMap (
    w:
    concatMap
      (
        v:
        let
          ds = map (c: enumPool.${c}) (chars w);
          holds = filter (d: elem v d.ps) ds;
          adm = holds != [ ] && all (d: d.ck v) holds;
          got = read (map (d: d.t) ds) v;
        in
        if (got != "REFUSED") == adm then [ ] else [ "${w}/${v}" ]
      )
      [
        "a"
        "b"
        "c"
        "d"
      ]
  ) enumWords;
  # mixed int folds: the even-only check-only copy declared first, beside a door partner and gen `int` declared last
  mixPool = {
    B = d1 (np.ints.between 0 9);
    N = d1 (narrowRecord "nTM");
    R = np.ints.positive;
    U = d2 np.ints.u8;
  };
  evenCopy = d1 (gt.int // { check = even; });
  mixGrid = nl.mapAttrs (
    _: p:
    map (v: read [ evenCopy p gt.int ] v) [
      (-1)
      2
      3
    ]
  ) mixPool;
  # a held step: `either (listOf X) str` with X gen `int` or a nixpkgs refinement of `int` (four spellings, one check and
  # one self-answering relation), raw and through the door
  rejTM =
    self: f:
    if f.name == "int" && (f.payload == null || f.payload == { refined = true; }) then self else null;
  rejInt = {
    self =
      n:
      let
        self = nl.mkOptionType {
          name = "int";
          check = x: isInt x && x != n;
          merge = nl.options.mergeEqualOption;
          functor = np.defaultFunctor "int" // {
            type = _: self;
            payload = {
              refined = true;
            };
            binOp = a: _b: a;
          };
          typeMerge = rejTM self;
        };
      in
      self;
    base =
      n:
      let
        self = nl.mkOptionType {
          name = "int";
          check = x: isInt x && x != n;
          merge = nl.options.mergeEqualOption;
          functor = np.defaultFunctor "int" // {
            payload = {
              refined = true;
            };
            binOp = a: _b: a;
          };
          typeMerge = rejTM self;
        };
      in
      self;
    bare =
      n:
      let
        self = nl.mkOptionType {
          name = "int";
          check = x: isInt x && x != n;
          merge = nl.options.mergeEqualOption;
          functor = np.defaultFunctor "int";
          typeMerge = rejTM self;
        };
      in
      self;
    addCheck =
      n:
      let
        self = np.addCheck np.int (x: x != n) // {
          typeMerge = rejTM self;
        };
      in
      self;
  };
  uol = c: t: c.either (c.listOf t) c.str;
  heldGrid = nl.mapAttrs (
    _: sp:
    let
      A = uol np (sp 7);
      B = uol np (sp 9);
      G = uol gt gt.int;
      cols = {
        raw = {
          inherit A B G;
        };
        door = {
          inherit G;
          A = d1 A;
          B = d1 B;
        };
      };
    in
    nl.mapAttrs (
      _: ds:
      nl.genAttrs [ "ABG" "ABGG" "AGBG" "BAG" ] (
        w:
        map (v: readAt "p" (map (c: ds.${c}) (chars w)) [ v ]) [
          (if w == "BAG" then 9 else 7)
          8
        ]
      )
    ) cols
  ) rejInt;
  # an author-declared met record (y's `type = options.x.type`, x's declarations a verify copy through a door and the
  # narrowing author record through either door), redeclared in y beside gen `int`
  verifyEven = d1 (gt.int // { verify = v: if even v then null else "odd"; });
  metOf =
    door:
    (nl.evalModules {
      modules = map (t: { options.x = nl.mkOption { type = t; }; }) [
        verifyEven
        (door (narrowRecord "nTM"))
      ];
    }).options.x.type;
  plantGrid = nl.mapAttrs (
    _: X:
    map (yw: readAt "y" (map (c: if c == "G" then gt.int else X) (chars yw)) (-2)) [
      "GX"
      "XX"
    ]
  ) (nl.mapAttrs (_: metOf) doors);
in
{
  flake.tests.exported-typemerge-debt = {
    # RED (22 orders serve "x", every one ending in the gen leaf) unless the check-only copy names its declaration
    # whenever it is carried; the admitted value is served at every order
    test-a-check-only-door-copy-is-owed-at-every-order = {
      expr = nl.mapAttrs (_: nl.mapAttrs (_: map (c: c.got))) copyGrid;
      expected = nl.mapAttrs (_: nl.mapAttrs (_: map (c: c.want))) copyGrid;
    };
    # RED (140 words serve a value the copy rejects, its parameters holding it) unless the copy names its declaration
    test-a-check-only-door-copy-is-owed-over-a-widening-join = {
      expr = enumWrong;
      expected = [ ];
    };
    # RED (-1 and 3 served at all four partners) unless the met record owes the partner's declaration beside itself
    test-a-met-record-owes-the-partner-it-is-handed = {
      expr = mixGrid;
      expected = nl.mapAttrs (_: _: [
        "REFUSED"
        2
        "REFUSED"
      ]) mixPool;
    };
    # A held step does not hold a partner recovered from its functor: holding that rebuilt fold beside an ad-hoc held
    # record refuses free values main and nixpkgs' twin serve (ADR-0039 parity-defect rule (2)). So the element 7 or 9
    # a refinement rejects is served at every spelling, raw and through the door, as main serves it: an open defect
    # (SILENT-D, den-hoag-alnjf), asserted as the value it produces so a build refusing it reds it. The element every
    # declaration admits is served.
    test-a-held-step-serves-what-a-recovered-partner-rejects = {
      expr = heldGrid;
      expected = nl.mapAttrs (
        _: _:
        nl.genAttrs [ "raw" "door" ] (
          _:
          nl.genAttrs [ "ABG" "ABGG" "AGBG" "BAG" ] (w: [
            [ (if w == "BAG" then 9 else 7) ]
            [ 8 ]
          ])
        )
      ) rejInt;
    };
    # RED (-2, which the verify copy alone refuses, served) where a met record an author declares is not owed whole
    test-an-author-declared-met-record-is-owed-whole = {
      expr = plantGrid;
      expected = nl.mapAttrs (_: _: [
        "REFUSED"
        "REFUSED"
      ]) doors;
    };
    # The author relation's narrowing answer decides: -1, admitted by every declaration, is served at every order
    # (RED where the met record is owed whole at every step, or a door owes its export where nothing is declared)
    test-an-author-narrowing-relation-is-not-over-refused = {
      expr = narrowGrid;
      expected = nl.genAttrs [ "nTM" "int" ] (
        _: nl.genAttrs [ "d1" "d2" ] (_: nl.genAttrs narrowOrders (_: -1))
      );
    };
  };
}
