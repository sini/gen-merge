# THE MEET'S IDENTITY (den-hoag-hnd82 Q1, owner-ruled 2026-10-14: mint the meet). A met record over a GEN join is a
# gen-merge construction, `gen-merge.meet`, over its join and the operands it owes, minted per component through the one
# mint (ADR-0034): two constructions of one meet are one type, a different meet is not, a meet over a sealed member is
# refused at `typeEq` rather than decided, and the meet is still enforced. A met record is completed (its own stamp),
# so a union reads its `verify` as its domain. Over a FOREIGN join it is COMPARED on every route, as the carry route's
# record is (den-hoag-k4f4g arm (c), owner-ruled 2026-10-16): no mark, a decision and no identity.
# The record a module set carries (`carriedAtDepth`) is the same construction where it owes ANOTHER declaration's
# check (den-hoag-k4f4g, arm (a)); carried over its own check alone it is re-handed (ADR-0014), and a foreign record
# keeps its foreign regime, so nixpkgs' `valueMeta` is still served for it (den-hoag-xroc7).
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib.types;
  inherit (builtins) deepSeq tryEval;
  try =
    e:
    let
      r = tryEval (deepSeq e e);
    in
    if r.success then r.value else "REFUSED";
  decl =
    tys:
    (gm.evalModuleTree { } (map (ty: { options.o = gm.mkOption { type = ty; }; }) tys)).options.o.type;
  val =
    tys: v:
    try
      (gm.evalModuleTree { } (
        map (ty: { options.o = gm.mkOption { type = ty; }; }) tys ++ [ { o = v; } ]
      )).config.o;
  even = v: builtins.bitAnd v 1 == 0;
  # one foreign operand VALUE, shared by every construction below
  evenInt = np.addCheck t.int even;
  posInt = np.addCheck t.int (v: v > 0);
  oddInt = np.addCheck t.int (v: !(even v));
  # a met record from each of the other two producers: `meetOf`'s foreign-`verify` record (a foreign join whose copy
  # states a `verify`), and `metWith`'s held record (a gen operand whose fold is not the carrier's)
  attrsInt = np.attrsOf np.int;
  small = v: if builtins.all (x: x < 10) (builtins.attrValues v) then null else "rejected";
  # the same over a GEN join: a gen container's copy states the `verify`
  verifiedOverGen = [
    (t.attrsOf t.int // { verify = small; })
    (t.attrsOf t.int)
  ];
  verifiedOver = [
    (
      attrsInt
      // {
        verify = v: if builtins.all (x: x < 10) (builtins.attrValues v) then null else "rejected";
      }
    )
    attrsInt
  ];
  # a fold whose relation answers `j`: nixpkgs' `int` (a foreign join) or gen's (a gen join)
  evenFoldOver =
    j:
    gm.mkOptionType (
      let
        self = nixpkgsLib.mkOptionType {
          name = "evenFold";
          check = {
            __functor = _: builtins.isInt;
            isV2MergeCoherent = true;
          };
          merge =
            loc: defs:
            let
              v = nixpkgsLib.mergeEqualOption loc defs;
            in
            if even v then v else throw "odd";
          functor = np.defaultFunctor "evenFold" // {
            type = _: self;
            payload = { };
            binOp = _a: _b: { };
          };
          typeMerge = f: if f.name == "int" || f.name == "evenFold" then j else null;
        };
      in
      self
    );
  heldOver = [
    (evenFoldOver np.int)
    t.int
  ];
  heldOverGen = [
    (evenFoldOver t.int)
    t.int
  ];
  # what a meet over a FOREIGN join is: met, no mark, a decision (self true, a twin false) and no identity
  compared =
    tys:
    let
      m = decl tys;
    in
    {
      met = m ? __meetJoin;
      minted = m ? __mint;
      self = try (t.typeEq m m);
      twin = try (t.typeEq m (decl tys));
      identity = if try (genTypes.idOf m) == "REFUSED" then "REFUSED" else "served";
    };
  minted = m: {
    ctor = try (m.__payload.minted.ctor or null);
    self = try (t.typeEq m m);
  };
  # a gen module set, wrapped by a foreign `addCheck`, and a foreign one (keyed, so nixpkgs merges it declared twice)
  gSub = t.submodule {
    options.a = gm.mkOption {
      type = t.int;
      default = 1;
    };
  };
  npSub = np.submodule {
    key = "k4f4g-np-sub";
    options.a = nixpkgsLib.mkOption {
      type = np.int;
      default = 1;
    };
  };
  carried = m: {
    ctor = try (m.__payload.minted.ctor or null);
    carried = try (m.__payload.minted.args.carried or false);
    joinsMark = try (m.__mint == gSub.__mint);
  };
  foreign =
    tys:
    let
      e = gm.evalModuleTree { } (
        map (ty: { options.o = gm.mkOption { type = ty; }; }) tys ++ [ { o.a = 2; } ]
      );
    in
    {
      minted = e.options.o.type ? __mint;
      valueMeta = try e.options.o.valueMeta.configuration.config;
    };
in
{
  flake.tests.met-identity = {
    test-a-met-record-is-one-type-with-itself = {
      expr =
        let
          m = decl [
            evenInt
            t.int
          ];
        in
        {
          met = m ? __meetJoin;
          self = try (t.typeEq m m);
        };
      expected = {
        met = true;
        self = true;
      };
    };
    test-two-constructions-of-one-meet-are-one-type = {
      expr = try (
        t.typeEq
          (decl [
            evenInt
            t.int
          ])
          (decl [
            evenInt
            t.int
          ])
      );
      expected = true;
    };
    # a meet whose operand is itself a met record: the member enters by the met record's own mark
    test-a-meet-over-a-met-record-is-one-type = {
      expr = try (
        t.typeEq
          (decl [
            evenInt
            t.int
            posInt
          ])
          (decl [
            evenInt
            t.int
            posInt
          ])
      );
      expected = true;
    };
    # a different owed check is never the same type: its subject differs, and no inert evidence decides it
    test-a-different-meet-is-not-one-type = {
      expr = try (
        t.typeEq
          (decl [
            evenInt
            t.int
          ])
          (decl [
            oddInt
            t.int
          ])
      );
      expected = "REFUSED";
    };
    # two SEPARATE constructions of a foreign operand are two closures: sealed, refused by name, never decided
    test-a-meet-over-separately-built-foreign-operands-refuses = {
      expr = try (
        t.typeEq
          (decl [
            (np.addCheck t.int even)
            t.int
          ])
          (decl [
            (np.addCheck t.int even)
            t.int
          ])
      );
      expected = "REFUSED";
    };
    # the mark is the meet's own construction over its join, not the join's mark carried by `//`
    test-a-met-record-mints-its-own-construction = {
      expr =
        let
          m = decl [
            evenInt
            t.int
          ];
        in
        {
          ctor = m.__payload.minted.ctor or null;
          joinsMark = m.__mint == m.__meetJoin.__mint;
        };
      expected = {
        ctor = "gen-merge.meet";
        joinsMark = false;
      };
    };
    # each producer mints over a gen join: `meetOf`'s foreign-`verify` record, and `metWith`'s held record
    test-a-foreign-verify-met-record-mints-its-own-construction = {
      expr =
        let
          m = decl verifiedOverGen;
        in
        minted m // { verify = m ? verify; };
      expected = {
        ctor = "gen-merge.meet";
        self = true;
        verify = true;
      };
    };
    test-a-held-met-record-mints-its-own-construction = {
      expr =
        let
          m = decl heldOverGen;
        in
        minted m // { holds = m.holds or false; };
      expected = {
        ctor = "gen-merge.meet";
        self = true;
        holds = true;
      };
    };
    # what a met record does beyond its members enters its construction as inert arguments: a foreign `verify`, a
    # held fold, and which owed operands are relativised
    test-a-met-record-states-what-it-does-in-its-arguments = {
      expr =
        map
          (
            m:
            let
              a = m.__payload.minted.args or { };
            in
            {
              verify = a.verify or null;
              holds = a.holds or null;
              relativised = a.relativised or null;
            }
          )
          [
            (decl verifiedOverGen)
            (decl heldOverGen)
          ];
      expected = [
        {
          verify = true;
          holds = null;
          relativised = [ false ];
        }
        {
          verify = null;
          holds = true;
          relativised = [
            false
            false
          ];
        }
      ];
    };
    # over a FOREIGN join no producer mints: `meetOf`'s record, its foreign-`verify` record, `metWith`'s held record, and
    # a join widening its operands (relativised) are each a decision, one with itself and not with a second construction,
    # with no identity
    test-a-met-record-over-a-foreign-join-is-compared-at-every-producer =
      let
        c = {
          met = true;
          minted = false;
          self = true;
          twin = false;
          identity = "REFUSED";
        };
      in
      {
        expr = map compared [
          [
            (np.addCheck np.int even)
            np.int
          ]
          verifiedOver
          heldOver
          [
            (np.enum [ "a" ])
            (np.enum [ "b" ])
          ]
        ];
        expected = [
          c
          c
          c
          c
        ];
      };
    # a foreign module-set join reaches `meetOf` inside a union and the carry route bare: one regime either way, and
    # nixpkgs' metadata served for both at a value both declarations admit
    test-a-foreign-module-set-join-is-compared-wrapped-in-a-union-or-not =
      let
        p = v: !(builtins.isAttrs v) || v.a != 3;
        wrapped = [
          (np.addCheck (np.either np.str npSub) p)
          (np.either np.str npSub)
        ];
        bare = [
          (np.addCheck npSub p)
          npSub
        ];
        row = tys: {
          inherit (compared tys) minted twin;
          valueMeta = try (foreign tys).valueMeta;
        };
      in
      {
        expr = map row [
          wrapped
          bare
        ];
        expected = [
          {
            minted = false;
            twin = false;
            valueMeta = {
              a = 2;
            };
          }
          {
            minted = false;
            twin = false;
            valueMeta = {
              a = 2;
            };
          }
        ];
      };
    # the meet is still enforced: a value is served only where every declaration admits it
    test-a-minted-meet-is-still-the-meet = {
      expr =
        map
          (val [
            evenInt
            t.int
          ])
          [
            2
            3
            "x"
          ];
      expected = [
        2
        "REFUSED"
        "REFUSED"
      ];
    };
    # a union member that is a met record is judged by its completed domain, its owed `verify` included, so the
    # union serves exactly where the member declared alone serves (the census ovl family)
    test-a-union-reads-a-met-member-by-its-domain =
      let
        pA =
          v: !(builtins.isAttrs v) || builtins.all (x: !(builtins.isInt x) || x < 10) (builtins.attrValues v);
        B = np.attrsOf np.int;
        x = t.either (B // { verify = v: if pA v then null else "rejected"; }) (np.attrsOf np.int);
        plain = t.either B (np.attrsOf np.int);
        narrowX = t.either (B // { verify = v: if pA v then null else "rejected"; }) (
          np.attrsOf (np.ints.between 0 5)
        );
        narrowPlain = t.either B (np.attrsOf (np.ints.between 0 5));
      in
      {
        expr = {
          alone = val [ x ] { a = 20; };
          redeclared = val [ plain x ] { a = 20; };
          neither = val [ narrowPlain narrowX ] { a = 20; };
        };
        expected = {
          alone = {
            a = 20;
          };
          redeclared = {
            a = 20;
          };
          neither = "REFUSED";
        };
      };
    # the module-set join restricted by another declaration's check: minted, one type with itself and with a second
    # declaration of the same pair, the wrapper's check still enforced
    test-a-module-set-carried-over-another-declarations-check-is-minted =
      let
        w = np.addCheck gSub (v: v.a != 3);
        # the values read over a module set whose option states no `default`: the two declarations'
        # module sets merge into one, and two copies of one option both stating `default` are refused
        # (nixpkgs' `bothHave`), so the check is read where nothing else refuses
        gSubBare = t.submodule { options.a = gm.mkOption { type = t.int; }; };
        wBare = np.addCheck gSubBare (v: v.a != 3);
      in
      {
        expr =
          carried (decl [
            w
            gSub
          ])
          // {
            twins = try (
              t.typeEq
                (decl [
                  w
                  gSub
                ])
                (decl [
                  w
                  gSub
                ])
            );
            values = map (v: val [ gSubBare wBare ] { a = v; }) [
              2
              3
            ];
          };
        expected = {
          ctor = "gen-merge.meet";
          carried = true;
          joinsMark = false;
          twins = true;
          values = [
            { a = 2; }
            "REFUSED"
          ];
        };
      };
    # carried over its own check alone it admits what it did: re-handed, the declaration's own mark kept
    test-a-module-set-carried-over-its-own-check-alone-is-re-handed =
      let
        w = np.addCheck gSub (v: v.a != 3);
      in
      {
        expr = {
          lone = carried (decl [ w ]);
          twice = carried (decl [
            w
            w
          ]);
        };
        expected = {
          lone = {
            ctor = "gen-merge.submodule";
            carried = false;
            joinsMark = true;
          };
          twice = {
            ctor = "gen-merge.submodule";
            carried = false;
            joinsMark = true;
          };
        };
      };
    # a foreign module set declared once, or one value declared twice, keeps its foreign regime: not minted, and
    # nixpkgs' metadata is served for it
    test-a-foreign-module-set-carried-over-its-own-check-keeps-its-foreign-regime = {
      expr = {
        lone = foreign [ npSub ];
        twice = foreign [
          npSub
          npSub
        ];
      };
      expected = {
        lone = {
          minted = false;
          valueMeta = {
            a = 2;
          };
        };
        twice = {
          minted = false;
          valueMeta = {
            a = 2;
          };
        };
      };
    };
    # a foreign join restricted by ANOTHER foreign declaration's check is carried, and still COMPARED: a mint over a
    # join rebuilt per evaluation is no identity (its twins refused), and nixpkgs' metadata is served for it
    test-a-foreign-join-carried-over-another-declarations-check-stays-compared = {
      expr = foreign [
        (np.addCheck npSub (v: v.a != 3))
        npSub
      ];
      expected = {
        minted = false;
        valueMeta = {
          a = 2;
        };
      };
    };
  };
}
