# TWO SEPARATE `defineType` COMPLETIONS OF ONE `mkType` LEAF RECORD ARE REFUSED; COPIES OF ONE COMPLETION KEEP
# THEIR ANSWER (`lib/types.nix` `sealedLeaf`, den-hoag-oqqa5).
#
# `mkType`'s leaf relation answers a same-key gen partner with the un-exported record, so two completions joined
# to a bare descriptor and aborted (`attribute 'merge' missing`; nixpkgs' engine: `deprecationMessage`). The
# completion now seals that relation to its export (`sealedTo`), and two operands whose seals differ under
# `closuresFirst` are refused by name, as nixpkgs refuses them. Every other pair answers as before the seal:
# one completion declared N times, its `//` copies, its re-completions and derivations, a raw or unsealed
# partner, and a record the published door's import arm completes (a stated foreign `check`), which is never
# sealed. The refusals' and the held aborts' messages are the error plane's (`tests-error-two-completions.nix`).
{
  genMerge,
  nixpkgsLib,
  interface,
  ...
}:
let
  f = import ./_fixtures/two-completions.nix { inherit genMerge nixpkgsLib; };
  inherit (f)
    gt
    gen
    npe
    verdict
    m
    T
    T'
    Tc
    C
    Rd
    Dx
    Dx'
    Ti
    mCM
    mV2
    r
    ;
  cf = x: genMerge.closuresFirst [ x ] x;
  phrase = "`nm' and `nm', two separate `defineType' completions of one name that this relation cannot compare";
  lz = sentinel: {
    unmarked = gt.defineType {
      name = "lz";
      verify = _: null;
      typeMergeRel = throw sentinel;
    };
    marked = gt.defineType (m // { typeMergeRel = throw sentinel; });
  };
  lzs = lz "two-completions: a single declaration forced the relation";
in
{
  flake.tests.two-completions = {
    # cell 1 (class; the message is the error plane's): the ruled forms refuse catchably, in both orders
    test-two-separate-completions-refuse-catchably = {
      expr = map (ts: verdict (gen ts 4)) [
        f.twob
        f.twobR
        f.two2
        f.twob3
      ];
      expected = [
        "REFUSED"
        "REFUSED"
        "REFUSED"
        "REFUSED"
      ];
    };
    # cell 2: the export's derived `typeMerge` is null in both orders, the relation states the sealed refusal, and
    # the functor's type is the export itself, so the null is the seal's and not a broken partner recovery
    test-the-exported-typemerge-of-two-completions-is-the-seal-s-null = {
      expr = {
        twoThenOne = T'.typeMerge T.functor == null;
        oneThenTwo = T.typeMerge T'.functor == null;
        relation = (T'.typeMergeRel T).refused or null;
        relationReversed = (T.typeMergeRel T').refused or null;
        functorTypeIsTheExport = cf T.functor.type == cf T;
      };
      expected = {
        twoThenOne = true;
        oneThenTwo = true;
        relation = phrase;
        relationReversed = phrase;
        functorTypeIsTheExport = true;
      };
    };
    # cell 3: one value declared N times keeps its value and its check (gen's engine)
    test-one-completion-declared-n-times-keeps-its-value-and-check = {
      expr = {
        bare2 = verdict (gen [ T T ] 4);
        bare2s = verdict (gen [ T T ] "s");
        bare3 = verdict (gen [ T T T ] 4);
        copy2 = verdict (gen [ Tc Tc ] 4);
        copy2s = verdict (gen [ Tc Tc ] "s");
        raw2 = verdict (gen [ m m ] 4);
        raw2s = verdict (gen [ m m ] "s");
        one = verdict (gen [ T ] 4);
        ones = verdict (gen [ T ] "s");
        oneNpe = verdict (npe [ T ] 4);
        onesNpe = verdict (npe [ T ] "s");
      };
      expected = {
        bare2 = 4;
        bare2s = "REFUSED";
        bare3 = 4;
        copy2 = 4;
        copy2s = "REFUSED";
        raw2 = 4;
        raw2s = "REFUSED";
        one = 4;
        ones = "REFUSED";
        oneNpe = 4;
        onesNpe = "REFUSED";
      };
    };
    # cell 3 (K4, P3): the one-completion direct `typeMerge` is non-null, as before the seal; its `check` and
    # `deprecationMessage` are the error plane's (they abort, as before)
    test-one-completion-direct-typemerge-null-ness-is-held = {
      expr = {
        TT = T.typeMerge T.functor == null;
        TC = T.typeMerge C.functor == null;
        CT = C.typeMerge T.functor == null;
        TcTc = Tc.typeMerge Tc.functor == null;
      };
      expected = {
        TT = false;
        TC = false;
        CT = false;
        TcTc = false;
      };
    };
    # cell 4: copies, re-completions and derivations of one completion keep their class
    test-copies-of-one-completion-keep-their-class = {
      expr = {
        CC = verdict (gen [ C C ] 4);
        CCs = verdict (gen [ C C ] "s");
        TC = verdict (gen [ T C ] 4);
        CT = verdict (gen [ C T ] 4);
        TCT = verdict (gen [ T C T ] 4);
        CTC = verdict (gen [ C T C ] "s");
        DxDx = verdict (gen [ Dx Dx ] 4);
        DxDx2 = verdict (gen [ Dx Dx' ] 4);
        DxDxNpe = verdict (npe [ Dx Dx ] 4);
        TDx = verdict (gen [ T Dx ] 4);
        TDxNpe = verdict (npe [ T Dx ] 4);
        RdIsCarried = interface.carriedCopy C != null;
      };
      expected = {
        CC = 4;
        CCs = "REFUSED";
        TC = 4;
        CT = 4;
        TCT = 4;
        CTC = "REFUSED";
        DxDx = 4;
        DxDx2 = 4;
        DxDxNpe = 4;
        TDx = "REFUSED";
        TDxNpe = "REFUSED";
        RdIsCarried = false;
      };
    };
    # cell 5: a stock-named leaf beside gen's `int` keeps its served value (arm (b): no seal on the partner)
    test-a-mixed-pair-keeps-its-class = {
      expr = {
        gen = verdict (gen [ Ti gt.int ] 4);
        gens = verdict (gen [ Ti gt.int ] "s");
        npe = verdict (npe [ Ti gt.int ] 4);
      };
      expected = {
        gen = 4;
        gens = "REFUSED";
        npe = 4;
      };
    };
    # cell 6 and cell 8 (class): the verify hazard and the stock-named pair refuse catchably
    test-the-verify-hazard-and-the-stock-named-pair-refuse = {
      expr = {
        hz = verdict (gen f.hz 4);
        TiTi = verdict (gen f.TiTi 4);
        TiTiNpe = verdict (npe f.TiTi 4);
      };
      expected = {
        hz = "REFUSED";
        TiTi = "REFUSED";
        TiTiNpe = "REFUSED";
      };
    };
    # cell 7 (K3): a planted relation throw is never forced by a single declaration or a construction
    test-a-single-declaration-never-forces-the-relation = {
      expr = {
        unmarked = verdict (gen [ lzs.unmarked ] 4);
        marked = verdict (gen [ lzs.marked ] 4);
        unmarkedNpe = verdict (npe [ lzs.unmarked ] 4);
        markedNpe = verdict (npe [ lzs.marked ] 4);
        construction = [
          lzs.unmarked._type
          lzs.unmarked.name
          lzs.marked._type
          lzs.marked.name
        ];
        # the control: the planted throw fires when the relation IS forced
        plantedFires = verdict (builtins.seq lzs.marked.typeMergeRel "forced");
      };
      expected = {
        unmarked = 4;
        marked = 4;
        unmarkedNpe = 4;
        markedNpe = 4;
        construction = [
          "option-type"
          "lz"
          "option-type"
          "nm"
        ];
        plantedFires = "REFUSED";
      };
    };
    # cell 9: the reach's edges that keep their class (one-completion containers, the slow path)
    test-the-reach-s-held-edges-keep-their-class = {
      expr = {
        aoTT = verdict (gen [ (gt.attrsOf T) (gt.attrsOf T) ] { a = 4; });
        loTT = verdict (gen [ (gt.listOf T) (gt.listOf T) ] [ 4 ]);
        slow = verdict (gen [ (gt.defineType r) (gt.defineType r) ] 4);
        slows = verdict (gen [ (gt.defineType r) (gt.defineType r) ] "s");
        slowNpe = verdict (npe [ (gt.defineType r) (gt.defineType r) ] 4);
        nestedTwo = verdict (gen f.aoTT2 { a = 4; });
        nvTwob = verdict (gen f.nvTwob 4);
        mDTwob = verdict (gen f.mDTwob 4);
      };
      expected = {
        aoTT = {
          a = 4;
        };
        loTT = [ 4 ];
        slow = 4;
        slows = "REFUSED";
        slowNpe = 4;
        nestedTwo = "REFUSED";
        nvTwob = "REFUSED";
        mDTwob = "REFUSED";
      };
    };
    # K2 (protected): a record stating the foreign `check` is completed by the import arm and never sealed, so two
    # separate completions keep their served value with their check kept (`s` is refused by the check)
    test-an-imported-check-record-is-never-sealed = {
      expr = {
        mCMTwob = verdict (gen f.mCMTwob 4);
        mCMTwobs = verdict (gen f.mCMTwob "s");
        mCMBare = verdict (
          gen (
            let
              X = gt.defineType mCM;
            in
            [
              X
              X
            ]
          ) 4
        );
        mV2Twob = verdict (gen f.mV2Twob [ 4 ]);
        seals = map (x: x.__leafSeal or "ABSENT") [
          (gt.defineType mCM)
          (gt.defineType mV2)
        ];
      };
      expected = {
        mCMTwob = 4;
        mCMTwobs = "REFUSED";
        mCMBare = 4;
        mV2Twob = [ 4 ];
        seals = [
          "ABSENT"
          "ABSENT"
        ];
      };
    };
    # where the seal sits: `mkType` marks, the fast path seals, a copy and a re-completion keep the seal, and a
    # derivation, a stock leaf and an unmarked record carry none
    test-the-seal-sits-only-on-mkType-completions = {
      expr = map (x: x.__leafSeal or "ABSENT") [
        m
        T
        C
        Rd
        Dx
        gt.int
        (gt.defineType r)
      ];
      expected = [
        "open"
        "sealed"
        "sealed"
        "sealed"
        "ABSENT"
        "ABSENT"
        "ABSENT"
      ];
    };
    # K1: the seal state is classified by the derivation partition, as `tied`
    test-the-leaf-seal-is-classified-by-the-derivation-partition = {
      expr = builtins.filter (
        n:
        !(builtins.elem n (builtins.concatLists (builtins.attrValues interface.deriveClasses)))
        && !(builtins.elem n interface.exportClasses.nameCarried)
      ) (builtins.attrNames (gt.defineType (gt.mkType { name = "nm"; })));
      expected = [ ];
    };
    test-the-leaf-seal-is-tied = {
      expr = builtins.elem "__leafSeal" interface.deriveClasses.tied;
      expected = true;
    };
  };
}
