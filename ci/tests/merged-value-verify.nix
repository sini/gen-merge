# A `verify` no completion states is read on the MERGED value at the meet and at a door's unminted return
# (den-hoag-5f99v). A `// { verify }` copy refines the value its definitions merge to, and a definition alone is not
# that value: gen's own fold reads it once on the merged value. Two readers still read it per definition or never: the
# meet of a redeclared option (`interface.meetOf`'s `dom` judged a gen copy's `verify` per definition), and a door's
# re-completion of a record no mint vouches for (its export's `check` was that `verify` per definition, and its fold
# never read it on the merged value). Each now states the copy's own check per definition and its `verify` in the v2
# protocol's `headError`, so a union choosing its member moves on to the next one. A gen leaf container's copy declared
# ONCE in nixpkgs' engine is not here: which reading its non-v2 fold publishes there is open (den-hoag-5f99v OQ1).
# Red at gen-merge main 048502b: every `*-split` and `*-bad` key of admdl / ynqbo (an uncatchable
# `attribute 'a' missing`, or a refusal of a merged value the verify admits); every `*-four`, `*-bad` and `*-split` key
# of l80pw / zhy56 / x7qe5, `laid-split-*` included (served); and the `gen-np-either-bad`, `gen-v2-*-bad` union keys
# (refused where the other member admits the value). Each half is held by its own keys: `gen-v2-*-bad` red where the
# meet states a v2 operand's `verify` by a throw in the value rather than in `headError`, and `laid-split-*` red where
# the caller-checked door exits skip `rebuildClosed.root`.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    isAttrs
    isInt
    isString
    all
    attrValues
    length
    split
    ;
  run =
    eng: ts: vs:
    let
      c =
        if eng == "gen" then
          (gm.evalModuleTree { } (
            map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ map (v: { x = v; }) vs
          )).config
        else
          (nl.evalModules {
            modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ map (v: { x = v; }) vs;
          }).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  # a verify reading members the merged value holds and one definition alone lacks
  both = v: if v.a == 1 && v.b == 1 then null else "needs a = 1 and b = 1";
  twoLines = v: if isString v && length (split "\n" v) > 1 then null else "needs two lines";
  notFour = v: if v == 4 || isAttrs v && (v.a or null) == 4 then "4 rejected" else null;
  notAB = v: if isAttrs v && v ? a && v ? b then "a beside b rejected" else null;
  below10 =
    v: if !(isAttrs v) || all (x: !(isInt x) || x < 10) (attrValues v) then null else "10 or more";
  notTwo = v: if !(isAttrs v) || !(v ? a) || !(isInt v.a) || v.a != 2 then null else "a = 2 rejected";
  gSub = gt.submodule {
    key = "merged-value-verify-g";
    options.a = gm.mkOption {
      type = gt.int;
      default = 0;
    };
    options.b = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  npSub = np.submodule {
    key = "merged-value-verify-np";
    options.a = nl.mkOption {
      type = np.int;
      default = 0;
    };
  };
  splitOk = [
    { a = 1; }
    { b = 1; }
  ];
  splitBad = [
    { a = 1; }
    { b = 2; }
  ];
  gAI = gt.attrsOf gt.int;
  npAI = np.attrsOf np.int;
  # a verify copy of a gen leaf container, through each door (den-hoag-admdl)
  leafDt = gt.defineType (gAI // { verify = both; });
  leafMk = gm.mkOptionType (gAI // { verify = both; });
  # a door applied to a nixpkgs record's verify copy (den-hoag-ynqbo)
  foreignMk = gm.mkOptionType (npAI // { verify = both; });
  linesMk = gm.mkOptionType (np.lines // { verify = twoLines; });
  # a verify copy of a door's import of a nixpkgs record, no caller check, re-completed by a door (den-hoag-l80pw)
  kInt = gm.mkOptionType np.int;
  importInt = gt.defineType (kInt // { verify = notFour; });
  importSub = gm.mkOptionType (gm.mkOptionType npSub // { verify = notFour; });
  importAI = gt.defineType (gm.mkOptionType npAI // { verify = notAB; });
  # the same copy with a caller's check laid on it (nixpkgs' `addCheck`), re-completed by each door
  laidAI = np.addCheck (gm.mkOptionType npAI // { verify = notAB; }) (_: true);
  # a gen either over a submodule, its verify copy beside its base below a container, a module function defining it
  # (den-hoag-zhy56; den-hoag-x7qe5 below nixpkgs' `attrsOf`)
  gE = gt.either gSub gt.str;
  eCopy = gt.defineType (gE // { verify = notTwo; });
  # an OVERLAPPING union declared twice: the copy rejects a = 20, the other member admits it (den-hoag-bbpll)
  ovlCopy = np.either (gt.defineType (gAI // { verify = below10; })) npAI;
  ovlBase = np.either gAI npAI;
  # a v2 operand's verify copy (nixpkgs' `attrsOf`), a member of an overlapping union declared after its plain twin
  rawAI = npAI // {
    verify = below10;
  };
  rawAttrs = np.attrs // {
    verify = below10;
  };
in
{
  flake.tests.merged-value-verify = {
    test-a-verify-copy-of-a-gen-leaf-container-is-read-on-the-merged-value = {
      expr = {
        np-ll-split = run "np" [ leafMk leafMk ] splitOk;
        gen-tl-split = run "gen" [ gAI leafDt ] splitOk;
        gen-tl-bad = run "gen" [ gAI leafDt ] splitBad;
      };
      expected = {
        np-ll-split = {
          a = 1;
          b = 1;
        };
        gen-tl-split = {
          a = 1;
          b = 1;
        };
        gen-tl-bad = "REFUSED";
      };
    };
    test-a-door-over-a-nixpkgs-verify-copy-reads-it-on-the-merged-value = {
      expr = {
        np-a-split = run "np" [ foreignMk ] splitOk;
        np-a-bad = run "np" [ foreignMk ] splitBad;
        gen-tl-split = run "gen" [ npAI foreignMk ] splitOk;
        gen-tl-bad = run "gen" [ npAI foreignMk ] splitBad;
        np-lines =
          run "np"
            [ linesMk ]
            [
              "x"
              "y"
            ];
        np-lines-one = run "np" [ linesMk ] [ "x" ];
        np-lines-twin =
          run "np"
            [ np.lines ]
            [
              "x"
              "y"
            ];
      };
      expected = {
        np-a-split = {
          a = 1;
          b = 1;
        };
        np-a-bad = "REFUSED";
        gen-tl-split = {
          a = 1;
          b = 1;
        };
        gen-tl-bad = "REFUSED";
        np-lines = "y\nx";
        np-lines-one = "REFUSED";
        np-lines-twin = "y\nx";
      };
    };
    test-a-verify-copy-of-a-door-import-keeps-its-verify-in-nixpkgs-engine = {
      expr = {
        tl-four = run "np" [ kInt importInt ] [ 4 ];
        tl-one = run "np" [ kInt importInt ] [ 1 ];
        ll-four = run "np" [ importInt importInt ] [ 4 ];
        sub-four = run "np" [ importSub ] [ { a = 4; } ];
        sub-one = run "np" [ importSub ] [ { a = 1; } ];
        split =
          run "np"
            [ importAI ]
            [
              { a = 1; }
              { b = 5; }
            ];
        split-one = run "np" [ importAI ] [ { a = 1; } ];
        laid-split-define =
          run "np"
            [ (gt.defineType laidAI) ]
            [
              { a = 1; }
              { b = 5; }
            ];
        laid-split-mk =
          run "np"
            [ (gm.mkOptionType laidAI) ]
            [
              { a = 1; }
              { b = 5; }
            ];
        laid-one-mk = run "np" [ (gm.mkOptionType laidAI) ] [ { a = 1; } ];
      };
      expected = {
        tl-four = "REFUSED";
        tl-one = 1;
        ll-four = "REFUSED";
        sub-four = "REFUSED";
        sub-one = {
          a = 1;
        };
        split = "REFUSED";
        split-one = {
          a = 1;
        };
        laid-split-define = "REFUSED";
        laid-split-mk = "REFUSED";
        laid-one-mk = {
          a = 1;
        };
      };
    };
    test-a-redeclared-either-copy-reads-a-module-function-definition-on-the-merged-value = {
      expr = {
        gen-attrs-bad = run "gen" [ (gt.attrsOf gE) (gt.attrsOf eCopy) ] [ { k = { ... }: { a = 2; }; } ];
        gen-attrs-ok = run "gen" [ (gt.attrsOf gE) (gt.attrsOf eCopy) ] [ { k = { ... }: { a = 1; }; } ];
        gen-np-attrs-bad =
          run "gen"
            [ (np.attrsOf gE) (np.attrsOf eCopy) ]
            [ { k = { ... }: { a = 2; }; } ];
        gen-np-attrs-ok = run "gen" [ (np.attrsOf gE) (np.attrsOf eCopy) ] [ { k = { ... }: { a = 1; }; } ];
      };
      expected = {
        gen-attrs-bad = "REFUSED";
        gen-attrs-ok.k = {
          a = 1;
          b = 0;
        };
        gen-np-attrs-bad = "REFUSED";
        gen-np-attrs-ok.k = {
          a = 1;
          b = 0;
        };
      };
    };
    test-a-union-declared-twice-takes-its-other-member-past-a-rejecting-verify = {
      expr = {
        np-ovl-bad = run "np" [ ovlBase ovlCopy ] [ { a = 20; } ];
        gen-ovl-bad = run "gen" [ ovlBase ovlCopy ] [ { a = 20; } ];
        np-ovl-ok = run "np" [ ovlBase ovlCopy ] [ { a = 1; } ];
        gen-np-either-bad =
          run "gen"
            [ (np.either np.attrs npAI) (np.either rawAttrs npAI) ]
            [ { a = 20; } ];
        gen-gen-either-bad =
          run "gen"
            [ (gt.either np.attrs npAI) (gt.either rawAttrs npAI) ]
            [ { a = 20; } ];
        gen-str-bad = run "gen" [ (np.either np.attrs np.str) (np.either rawAttrs np.str) ] [ { a = 20; } ];
        gen-v2-either-bad = run "gen" [ (np.either npAI npAI) (np.either rawAI npAI) ] [ { a = 20; } ];
        gen-v2-oneof-bad =
          run "gen"
            [
              (np.oneOf [
                npAI
                npAI
              ])
              (np.oneOf [
                rawAI
                npAI
              ])
            ]
            [ { a = 20; } ];
      };
      expected = {
        np-ovl-bad.a = 20;
        gen-ovl-bad.a = 20;
        np-ovl-ok.a = 1;
        gen-np-either-bad.a = 20;
        gen-gen-either-bad.a = 20;
        gen-str-bad = "REFUSED";
        gen-v2-either-bad.a = 20;
        gen-v2-oneof-bad.a = 20;
      };
    };
  };
}
