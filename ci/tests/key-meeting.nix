# THE KEY MEETING (den-hoag-9zyp7 OQ2): a record module names its NODE on its record (`__moduleKey`)
# and its REFERENCE key in its result (`key`, what nixpkgs dedups by and a `disabledModules` item
# names), the reference key being `<__keyEq.meeting>#<__keyEq.refine subject>`. The merge path meets
# occurrences by meeting, so every pair sharing a reference key meets whatever their nodes, and the
# refinement is demanded only at a meeting. Equal refinements are one key, decided as `key-eq.nix`
# decides one key; different refinements are two keys, both kept. `l` is a list option, so one module
# reads one element and two read two.

{
  genMerge,
  genMergeCore,
  genScope,
  ...
}:

let
  gm = genMerge;
  decl.options.l = gm.mkOption {
    type = gm.types.listOf gm.types.str;
    default = [ ];
  };
  # a record module: node `node`, reference key `rk#<mark>`; `c` names its construction, so `decide`
  # holds one construction reached twice as one module and refuses two (gen-schema's `sealedCollisionEq`)
  record =
    {
      tag,
      node,
      mark,
      c ? tag,
      meeting ? "rk",
      refine ? s: s.mark,
      imports ? [ ],
    }:
    {
      __moduleKey = node;
      __keyEq = {
        subject = { inherit mark c; };
        decide = a: b: a == b;
        inherit refine;
      }
      // (if meeting == null then { } else { inherit meeting; });
      __functor = _: _: {
        key = "rk#" + mark;
        inherit imports;
        config.l = [ tag ];
      };
    };
  a = record {
    tag = "a";
    node = "n1";
    mark = "m1";
  };
  l =
    mods:
    let
      r = builtins.tryEval (
        builtins.deepSeq (gm.evalModuleTree { } ([ decl ] ++ mods)).config.l
          (gm.evalModuleTree { } ([ decl ] ++ mods)).config.l
      );
    in
    if r.success then r.value else "REFUSED";
  deep = k: m: if k == 0 then m else { imports = [ (deep (k - 1) m) ]; };
in

{
  flake.tests.key-meeting = {
    # Two nodes sharing a reference key MEET: two constructions are refused in both orders, as one key
    # was (den-hoag-kind-generator-collision-d4gnx); the control is one construction reached twice.
    test-two-nodes-sharing-a-reference-key-meet = {
      expr =
        let
          b = record {
            tag = "b";
            node = "n2";
            mark = "m1";
          };
        in
        {
          ab = l [
            a
            b
          ];
          ba = l [
            b
            a
          ];
          deep = l [
            a
            (deep 2 b)
          ];
          once = l [
            a
            (deep 2 a)
          ];
        };
      expected = {
        ab = "REFUSED";
        ba = "REFUSED";
        deep = "REFUSED";
        once = [ "a" ];
      };
    };
    # Two refinements of one meeting are two keys: both compose, under one node or two.
    test-two-refinements-of-one-meeting-both-compose = {
      expr = {
        oneNode = l [
          a
          (record {
            tag = "b";
            node = "n1";
            mark = "m2";
          })
        ];
        twoNodes = l [
          a
          (record {
            tag = "b";
            node = "n2";
            mark = "m2";
          })
        ];
      };
      expected = {
        oneNode = [
          "b"
          "a"
        ];
        twoNodes = [
          "b"
          "a"
        ];
      };
    };
    # A plain module stating a record's reference key meets it, and only one publishes a comparison,
    # so it is refused in both orders; a plain key of the same meeting and another refinement composes.
    test-a-plain-key-stating-a-records-reference-key-meets-it = {
      expr =
        let
          forge = {
            key = "rk#m1";
            l = [ "f" ];
          };
        in
        {
          recordFirst = l [
            a
            forge
          ];
          plainFirst = l [
            forge
            a
          ];
          otherRefinement = l [
            a
            {
              key = "rk#m9";
              l = [ "f" ];
            }
          ];
        };
      expected = {
        recordFirst = "REFUSED";
        plainFirst = "REFUSED";
        otherRefinement = [
          "f"
          "a"
        ];
      };
    };
    # A plain key carrying the separator keeps nixpkgs' key rule: one key is its first occurrence, two
    # keys of one meeting are two modules.
    test-a-plain-key-with-the-separator-keeps-the-key-rule = {
      expr = l [
        {
          key = "x#1";
          l = [ "1" ];
        }
        {
          key = "x#1";
          l = [ "1b" ];
        }
        (deep 1 {
          key = "x#2";
          l = [ "2" ];
        })
      ];
      expected = [
        "2"
        "1"
      ];
    };
    # THE REFINEMENT IS DEMANDED ONLY AT A MEETING: a record whose refinement throws composes alone and
    # beside another meeting's record, and is refused (the throw, caught) where its meeting is shared.
    test-the-refinement-is-forced-only-at-a-meeting = {
      expr =
        let
          t = record {
            tag = "t";
            node = "n3";
            mark = "m3";
            refine = _: throw "the refinement was forced";
          };
        in
        {
          alone = l [ t ];
          otherMeeting = l [
            t
            (record {
              tag = "o";
              node = "n4";
              mark = "m4";
              meeting = "other";
            })
          ];
          sharedMeeting = l [
            t
            a
          ];
        };
      expected = {
        alone = [ "t" ];
        otherMeeting = [
          "o"
          "t"
        ];
        sharedMeeting = "REFUSED";
      };
    };
    # THE EARLIEST HOLDER of a meeting decides every deeper occurrence (den-hoag-9zyp7 gate v0 C1): two
    # refinements of one node, each reached at two depths, compose once each.
    test-the-earliest-holder-decides-a-deep-occurrence = {
      expr =
        let
          b = record {
            tag = "b";
            node = "n1";
            mark = "m2";
          };
        in
        l [
          a
          (deep 2 b)
          (deep 3 a)
          (deep 1 b)
        ];
      expected = [
        "b"
        "a"
      ];
    };
    # A record without a `meeting` meets by its node: two nodes never meet.
    test-a-record-without-a-meeting-meets-by-its-node = {
      expr = l [
        (record {
          tag = "a";
          node = "n1";
          mark = "m1";
          meeting = null;
        })
        (record {
          tag = "b";
          node = "n2";
          mark = "m1";
          meeting = null;
        })
      ];
      expected = [
        "b"
        "a"
      ];
    };
    # A `disabledModules` item names a record by its REFERENCE key, as nixpkgs' `moduleKey` does, never
    # by its node; the module family of the removing tree (`removal.closeKept`) drops it too.
    test-a-record-is-removed-by-its-reference-key = {
      expr =
        let
          b = record {
            tag = "b";
            node = "n2";
            mark = "m2";
          };
          family =
            mods:
            let
              ev = (genMergeCore.evalModuleTreeExposed { modules = [ decl ] ++ mods; })._evaluation;
            in
            builtins.length (
              builtins.filter (i: (genScope.decodeNta i).name or null == "modules") ev.allNodeIds
            );
        in
        {
          byReference = l [
            a
            b
            { disabledModules = [ { key = "rk#m1"; } ]; }
          ];
          byNode = l [
            a
            b
            { disabledModules = [ { key = "n1"; } ]; }
          ];
          familyByReference = family [
            a
            b
            { disabledModules = [ { key = "rk#m1"; } ]; }
          ];
          familyByNode = family [
            a
            b
            { disabledModules = [ { key = "n1"; } ]; }
          ];
        };
      expected = {
        byReference = [ "b" ];
        byNode = [
          "b"
          "a"
        ];
        familyByReference = 3;
        familyByNode = 4;
      };
    };
    # A record whose key is not `<meeting>#<refinement>` is refused by name where it meets, since a plain
    # key equal to it would never meet it; alone it is not read.
    test-a-meeting-its-key-does-not-name-is-refused-where-it-meets = {
      expr =
        let
          off = {
            __moduleKey = "n9";
            __keyEq = {
              subject = { };
              decide = _: _: true;
              meeting = "rk";
            };
            __functor = _: _: {
              key = "zz#m9";
              config.l = [ "z" ];
            };
          };
        in
        {
          alone = l [ off ];
          met = l [
            a
            off
          ];
        };
      expected = {
        alone = [ "z" ];
        met = "REFUSED";
      };
    };
    # A record publishing a null node key names no node: two of them both compose.
    test-a-null-node-key-names-no-node =
      let
        n = tag: {
          __moduleKey = null;
          __keyEq = null;
          __functor = _: _: {
            imports = [ ];
            config.l = [ tag ];
          };
        };
      in
      {
        expr = l [
          (n "a")
          (n "b")
        ];
        expected = [
          "b"
          "a"
        ];
      };
    # The warm path's origin split reads the graph refined where one node is kept twice, and serves
    # what the cold path does. Each record imports a module, so the split is read.
    test-the-warm-split-reads-the-refined-graph = {
      expr =
        let
          r =
            tag: mark:
            record {
              inherit tag mark;
              node = "n1";
              imports = [ { l = [ ("i" + tag) ]; } ];
            };
          b = r "b" "m2";
          base = [
            decl
            (r "a" "m1")
          ];
          warm = gm.evalModuleTree {
            warmFrom = gm.evalModuleTree { } base;
            editedModules = [ b ];
          } (base ++ [ b ]);
          v = builtins.tryEval (builtins.deepSeq warm.config.l warm.config.l);
        in
        if v.success then v.value else "REFUSED";
      expected = [
        "ib"
        "ia"
        "b"
        "a"
      ];
    };
  };
}
