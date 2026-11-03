# gen-merge: a gen leaf beside a FOREIGN partner it does not key by name answers that partner as the decider only, and says
# so before any join (the relation's `later`, `lib/interface.nix` `keyed.leaf` and `keyed.either`), so the step asks the later declaration's
# relation alone and meets its join with both operands (`lib/modules.nix` `bandedLeaves`, the deferred unthreaded arm).
# A door closure serves such a foreign join unclosed in its relation slot (`lib/interface.nix` `rebuildClosed.own`): the
# meet owes the closure's check once, and the met carrier does not re-owe it at every later step. Each row is a check
# nixpkgs' later-operand rule drops where the unchecked declaration decides, so gen's engine refuses the value the check
# rejects (THE MEET) and serves nixpkgs' value for every other. RED (`bad` served) where the deferred step answers the
# join unmet, or the slot's unclosed join reaches the carrier without the meet. Every mixed order at N = 2..4, raw and
# through both doors; the two-partner rows hold every order over {G, C, D} at N = 3 and 4.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  nl = nixpkgsLib;
  gt = gm.types;
  np = nl.types;
  json =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x (builtins.toJSON x));
    in
    if r.success then r.value else "REFUSED";
  gen =
    ts: v:
    json
      (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = v; } ]))
      .config.x;
  npe =
    ts: v:
    json
      (nl.evalModules {
        modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ [ { x = v; } ];
      }).config.x;
  doors = {
    raw = p: p;
    d1 = gm.mkOptionType;
    d2 = gt.mkOptionType;
  };
  letters = w: builtins.filter (c: builtins.isString c && c != "") (builtins.split "" w);
  words =
    al: n: if n == 0 then [ "" ] else builtins.concatMap (s: map (c: c + s) al) (words al (n - 1));
  holding = cs: w: builtins.all (c: builtins.elem c (letters w)) cs;
  # the mixed G / P orders at N = 2..4, and every order over {G, C, D} at N = 3 and 4
  duo = builtins.filter (holding [
    "G"
    "P"
  ]) (words [ "G" "P" ] 2 ++ words [ "G" "P" ] 3 ++ words [ "G" "P" ] 4);
  tri = builtins.filter (holding [
    "G"
    "C"
    "D"
  ]) (words [ "G" "C" "D" ] 3 ++ words [ "G" "C" "D" ] 4);
  # a row: the gen declaration `G` and its twin `Gn`, the foreign partners by letter (each through the door), the orders,
  # the values, and whether a declared check rejects `bad` (`owed`)
  check = p: t: np.addCheck t p;
  positive = v: v > 0;
  notBad = s: s != "bad";
  str = {
    ok = "a";
    bad = "bad";
  };
  int = {
    ok = 2;
    bad = -1;
  };
  rows = {
    # a gen leaf beside a door return of a checked foreign leaf (`chkI`: the name-keyed control, never deferred)
    chk = str // {
      G = gt.str;
      Gn = np.str;
      P = check notBad np.str;
      orders = duo;
      owed = true;
    };
    chkI = int // {
      G = gt.int;
      Gn = np.int;
      P = check positive np.int;
      orders = duo;
      owed = true;
    };
    plain = str // {
      G = gt.str;
      Gn = np.str;
      P = np.str;
      orders = duo;
      owed = false;
    };
    # a payload-stating deferred partner: gen `number` (functor `either`) beside a checked foreign `either`
    numE = int // {
      G = gt.number;
      Gn = np.either np.int np.float;
      P = check positive (np.either np.int np.float);
      orders = duo;
      owed = true;
    };
    # two distinct foreign partners, one checked
    mix = str // {
      G = gt.str;
      Gn = np.str;
      C = check notBad np.str;
      D = np.str;
      orders = tri;
      owed = true;
    };
    mixI = int // {
      G = gt.int;
      Gn = np.int;
      C = check positive np.int;
      D = np.int;
      orders = tri;
      owed = true;
    };
  }
  # a door closure over a gen leaf a caller checked, declared beside a plain foreign leaf: the closure's check is owed
  // builtins.listToAttrs (
    builtins.concatMap
      (d: [
        {
          name = "closedStr-${d}";
          value = str // {
            G = doors.${d} (check notBad gt.str);
            Gn = check notBad np.str;
            P = np.str;
            orders = duo;
            owed = true;
          };
        }
        {
          name = "closedInt-${d}";
          value = int // {
            G = doors.${d} (check positive gt.int);
            Gn = check positive np.int;
            P = np.int;
            orders = duo;
            owed = true;
          };
        }
      ])
      [
        "d1"
        "d2"
      ]
  );
  cells =
    want:
    builtins.mapAttrs (
      _: r:
      builtins.mapAttrs (
        _: d:
        builtins.listToAttrs (
          builtins.concatMap (
            w:
            map
              (vn: {
                name = "${w}/${vn}";
                value = want r vn (map (c: if c == "G" then r.G else d r.${c}) (letters w)) (map (
                  c: if c == "G" then r.Gn else r.${c}
                ) (letters w)) r.${vn};
              })
              [
                "ok"
                "bad"
              ]
          ) r.orders
        )
      ) doors
    ) rows;
in
{
  flake.tests.deferred-door-meet = {
    test-a-gen-leaf-beside-a-foreign-partner-is-met-with-every-declared-check-at-every-count-and-order = {
      expr = cells (
        _: _: ts: _: v:
        gen ts v
      );
      expected = cells (
        r: vn: _: tn: v:
        if vn == "bad" && r.owed then "REFUSED" else npe tn v
      );
    };
  };
}
