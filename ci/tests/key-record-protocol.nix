# THE RECORD'S REFERENCE KEY AND ITS FOLD. A record module may state its reference key on the record
# (`__keyEq.key`) and carry no `key` in its result, or a result `key` that is a foreign evaluator's
# own: this engine reads the record's, only where two occurrences meet, and tests its presence (never
# its value) at load. A record opting into the seal-decided fold (`__keyEq.onDistinct =
# "refuse-on-conflict"`, the one value) is decided against every construction its key has kept: equal
# under `decide` is that construction reached again (one module), otherwise `conflicts` refuses it by
# name, otherwise both compose. A record naming its node and stating no result key is still walked, so
# one construction reached N times is one module (the plain-list fast path reads `__moduleKey`). `l` is
# a list option, so one module reads one element and two read two.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  lib = nixpkgsLib;
  decl.options.l = gm.mkOption {
    type = gm.types.listOf gm.types.str;
    default = [ ];
  };
  try =
    v:
    let
      r = builtins.tryEval (builtins.deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
  # sorted: which module is collected first is not this file's subject
  l =
    mods:
    let
      v = try (gm.evalModuleTree { } ([ decl ] ++ mods)).config.l;
    in
    if builtins.isList v then builtins.sort builtins.lessThan v else v;
  # a record: node `node`, record key `rkey` (never compared, so a throwing key stays unread), result
  # key `result` (absent where null); `c` names its construction, `x` whether it conflicts with a
  # distinct one
  record =
    {
      tag,
      node ? "n1",
      rkey ? "rk#m1",
      result ? null,
      c ? tag,
      x ? false,
      onDistinct ? null,
    }:
    {
      __moduleKey = node;
      __keyEq = {
        meeting = "rk";
        subject = { inherit c x; };
        decide = a: b: a.c == b.c;
        key = rkey;
      }
      // (
        if onDistinct == null then
          { }
        else
          {
            inherit onDistinct;
            conflicts = a: b: a.x || b.x;
          }
      );
      __functor =
        _: _:
        {
          config.l = [ tag ];
        }
        // (if result == null then { } else { key = result; });
    };
  fold = args: record (args // { onDistinct = "refuse-on-conflict"; });

  # OQ-V5's shape: a record naming its node, its reference key on the record only, the option declared
  # in its own content, reached N times; the declaration through gen-merge's `mkOption`, nixpkgs'
  # `lib.mkOption` and raw (`{ _type = "option"; ... }`). `decls:value` reads one declaration kept.
  fooDecl =
    door:
    let
      o = {
        type = gm.types.str;
        default = "x";
      };
    in
    {
      options.foo =
        if door == "gm" then
          gm.mkOption o
        else if door == "lp" then
          lib.mkOption o
        else
          o // { _type = "option"; };
    };
  ownRecord = door: {
    __moduleKey = "M";
    __keyEq = {
      meeting = "M";
      key = "M#ref";
      subject = {
        mark = "M";
        sealed = { };
      };
      decide = a: b: a.sealed == b.sealed && a.mark == b.mark;
    };
    __functionArgs = {
      config = false;
    };
    __functor = _: { config, ... }: fooDecl door;
  };
  foo =
    ms:
    let
      ev = gm.evalModuleTree { } ms;
    in
    try "${toString (builtins.length ev.options.foo.declarations)}:${ev.config.foo}";
  definer = {
    foo = "y";
  };
  ownCells =
    door:
    builtins.concatMap
      (
        n:
        [ (foo (builtins.genList (_: ownRecord door) n)) ]
        ++ builtins.genList (p: foo (builtins.genList (i: if i == p then definer else ownRecord door) n)) n
      )
      [
        2
        3
        4
      ];
  ownExpected = builtins.concatMap (n: [ "1:x" ] ++ builtins.genList (_: "1:y") n) [
    2
    3
    4
  ];
  # nixpkgs' engine on the same records (its own types): it keys a module by its RESULT's `key` only, so a
  # record stating its key on the record alone is N anonymous modules, and two of them both state `default`.
  # gen serves where nixpkgs refuses: the (b′) serve beyond nixpkgs whose value and check oracles are
  # `test-b-prime-…` below (ADR-0039, merge law ADR-0012); nixpkgs' column is pinned so it stays visible.
  npRecord = ownRecord "lp" // {
    __functor =
      _:
      { config, ... }:
      {
        options.foo = lib.mkOption {
          type = lib.types.str;
          default = "x";
        };
      };
  };
  npFoo =
    ms:
    let
      ev = lib.evalModules { modules = ms; };
    in
    try "${toString (builtins.length ev.options.foo.declarations)}:${ev.config.foo}";
  npOwnCells =
    builtins.concatMap
      (
        n:
        [ (npFoo (builtins.genList (_: npRecord) n)) ]
        ++ builtins.genList (p: npFoo (builtins.genList (i: if i == p then definer else npRecord) n)) n
      )
      [
        2
        3
        4
      ];

  # THE SERVE BEYOND NIXPKGS, (b′) (ADR-0039; den-hoag-xh14j, orchestrator reading 2026-10-29): one record
  # construction reached N times is one module, where nixpkgs, reading identity from the result `key` alone,
  # refuses N anonymous declarations. The merge law is ADR-0012's "a diamond is two edges to one node, so
  # deduplication holds BY CONSTRUCTION", the node named by the record's key. Two oracles per cell, N = 2..4,
  # each door, the declaration in the record's own content (`own`) and imported (`imp`):
  #   VALUE: the served value and declarations equal the ONE construction's, declared once (`once`);
  #   CHECK: a planted definition the construction's own type rejects (an int for a `str`) is refused.
  # Scope: one construction only; two distinct constructions served once are not this law.
  spelledRecord =
    door: spelling:
    let
      r = ownRecord door;
    in
    if spelling == "own" then
      r
    else
      r // { __functor = _: { config, ... }: { imports = [ (fooDecl door) ]; }; };
  served = ms: foo ms;
  onceValue = door: spelling: served [ (spelledRecord door spelling) ];
  valueRows =
    door: spelling:
    builtins.concatMap
      (
        n:
        [ (served (builtins.genList (_: spelledRecord door spelling) n)) ]
        ++ builtins.genList (
          p: served (builtins.genList (i: if i == p then definer else spelledRecord door spelling) n)
        ) n
      )
      [
        2
        3
        4
      ];
  checkRows =
    door: spelling:
    map (n: served (builtins.genList (_: spelledRecord door spelling) n ++ [ { foo = 5; } ])) [
      2
      3
      4
    ];
  serveBeyond = door: spelling: {
    once = onceValue door spelling;
    value = valueRows door spelling;
    check = checkRows door spelling;
  };
  serveBeyondExpected = {
    once = "1:x";
    value = ownExpected;
    check = [
      "REFUSED"
      "REFUSED"
      "REFUSED"
    ];
  };

  # removal names a node with no result key positionally, as nixpkgs does, where the graph is read
  rmMods = [
    decl
    (record {
      tag = "a";
      rkey = "rk#m1";
    })
    { disabledModules = [ "/nothing-here" ]; }
    { _module.args.zz = "z"; }
  ];
  files =
    ev: map (d: builtins.baseNameOf (toString d.file)) ev.options._module.args.definitionsWithLocations;
in

{
  flake.tests.key-record-protocol = {
    # A record stating its reference key on the record and none in its result loads.
    test-a-record-stating-its-key-on-the-record-only-loads = {
      expr = l [ (record { tag = "a"; }) ];
      expected = [ "a" ];
    };
    # The record's key is read, never the result's: distinct record keys under one result key are two
    # refinements, which both compose; reading the result's would decide them as one key.
    test-the-record-key-is-read-not-the-result-key = {
      expr = {
        ab = l [
          (record {
            tag = "a";
            rkey = "rk#m1";
            result = "rk#same";
          })
          (record {
            tag = "b";
            node = "n2";
            rkey = "rk#m2";
            result = "rk#same";
          })
        ];
        ba = l [
          (record {
            tag = "b";
            node = "n2";
            rkey = "rk#m2";
            result = "rk#same";
          })
          (record {
            tag = "a";
            rkey = "rk#m1";
            result = "rk#same";
          })
        ];
      };
      expected = {
        ab = [
          "a"
          "b"
        ];
        ba = [
          "a"
          "b"
        ];
      };
    };
    # The record key is tested by presence at load: a lone record whose key would throw if read loads.
    test-a-lone-records-key-is-never-read = {
      expr = l [
        (record {
          tag = "a";
          rkey = throw "the record key was read at load";
        })
      ];
      expected = [ "a" ];
    };
    # The fold, at one key: the construction reached again is one module; a distinct construction is
    # kept unless `conflicts` says it collides, which is refused; in either order.
    test-the-fold-decides-then-refuses-on-conflict = {
      expr = {
        again = l [
          (fold { tag = "a"; })
          (fold { tag = "a"; })
        ];
        distinct = l [
          (fold { tag = "a"; })
          (fold { tag = "b"; })
        ];
        conflict = l [
          (fold { tag = "a"; })
          (fold {
            tag = "b";
            x = true;
          })
        ];
        conflictRev = l [
          (fold {
            tag = "b";
            x = true;
          })
          (fold { tag = "a"; })
        ];
        deep = l [
          (fold { tag = "a"; })
          { imports = [ (fold { tag = "a"; }) ]; }
          { imports = [ { imports = [ (fold { tag = "b"; }) ]; } ]; }
        ];
      };
      expected = {
        again = [ "a" ];
        distinct = [
          "a"
          "b"
        ];
        conflict = "REFUSED";
        conflictRev = "REFUSED";
        deep = [
          "a"
          "b"
        ];
      };
    };
    # One construction of OQ-V5's shape reached N = 2..4 times, alone and beside a definer at every
    # position, through each door: one declaration kept.
    test-a-record-naming-its-node-reached-n-times-is-one-module = {
      expr = {
        gm = ownCells "gm";
        lp = ownCells "lp";
        raw = ownCells "raw";
        nixpkgs = npOwnCells;
      };
      expected = {
        gm = ownExpected;
        lp = ownExpected;
        raw = ownExpected;
        nixpkgs = [
          "REFUSED"
          "1:y"
          "1:y"
        ]
        ++ builtins.genList (_: "REFUSED") 9;
      };
    };
    # (b′): VALUE and CHECK oracles for one record construction reached N times, every door and spelling.
    test-b-prime-one-record-construction-reached-n-times-value-and-check = {
      expr = lib.genAttrs [ "gm" "lp" "raw" ] (
        door: lib.genAttrs [ "own" "imp" ] (spelling: serveBeyond door spelling)
      );
      expected = lib.genAttrs [ "gm" "lp" "raw" ] (
        _: lib.genAttrs [ "own" "imp" ] (_: serveBeyondExpected)
      );
    };
    # Removal reads the graph's node names: a node with no result key is named positionally, so the
    # read is the engines' common value.
    test-removal-names-a-keyless-record-node-positionally = {
      expr = {
        gen = files (gm.evalModuleTree { } rmMods);
        nixpkgs = files (lib.evalModules { modules = rmMods; });
      };
      expected = {
        gen = [
          "modules.nix"
          "<unknown-file>"
        ];
        nixpkgs = [
          "modules.nix"
          "<unknown-file>"
        ];
      };
    };
  };
}
