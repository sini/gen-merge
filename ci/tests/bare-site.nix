# The orphan gate at the BARE site decides its own level only: a finding is refused by the nested
# tree that owns it, under its effective strictness, when that tree is read; and a warm evaluation
# is admitted only over a prior of the same effective strictness, so warm == cold. `RED:` notes
# record how each cell failed before this construction.
{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption mkIf;
  t = gm.types;
  forces = e: (builtins.tryEval (builtins.deepSeq e null)).success;
  # T2: a leaf tree. T1: a tree whose `sub` is a T2. `check` is per tree.
  t2Of =
    check:
    (evalModuleTree {
      inherit check;
      modules = [
        {
          options.k = mkOption {
            type = t.str;
            default = "d";
          };
        }
      ];
    }).type;
  t1Of =
    check:
    (evalModuleTree {
      inherit check;
      modules = [
        {
          options.known = mkOption {
            type = t.str;
            default = "k";
          };
          options.flag = mkOption {
            type = t.bool;
            default = false;
          };
          options.sub = mkOption { type = t2Of check; };
        }
      ];
    }).type;
  run =
    check: ty: m:
    evalModuleTree {
      inherit check;
      modules = [
        { options.x = mkOption { type = ty; }; }
        m
      ];
    };
  # the nested tree's definition reads the outer tree's own config
  selfRef =
    { config, ... }:
    {
      config.x = {
        known = "v";
        flag = true;
        sub = mkIf config.x.flag { k = "s"; };
      };
    };
  subThrow = {
    config.x = {
      known = "v";
      sub = throw "lazy-sub";
    };
  };
  subBad = {
    _file = "/real/F.nix";
    config.x = {
      known = "v";
      sub = {
        k = "s";
        bogus = 1;
      };
    };
  };
  # read a value, or "refused" where it throws catchably
  val =
    e:
    let
      r = builtins.tryEval (builtins.deepSeq e e);
    in
    if r.success then r.value else "refused";
  plainLeaf = {
    options.p = mkOption { type = t.str; };
    config.p = "P";
  };
  rootBad = {
    _file = "/real/R.nix";
    config.rootBogus = 1;
  };
  edited = [
    {
      options.other = mkOption { type = t.str; };
      config.other = "o";
    }
  ];
  nestedBase = [
    { options.x = mkOption { type = t1Of false; }; }
    plainLeaf
    subBad
  ];
  rootBase = [
    plainLeaf
    rootBad
  ];
  # warm re-eval of `base ++ edited` at `next`, from a prior of `base` at `prev`; `coldAt` is the reference
  warmAt =
    prev: next: base:
    evalModuleTree {
      check = next;
      modules = base ++ edited;
      warmFrom = evalModuleTree {
        check = prev;
        modules = base;
      };
      editedModules = edited;
    };
  coldAt =
    c: base:
    evalModuleTree {
      check = c;
      modules = base ++ edited;
    };
  ownBad = {
    _file = "/real/F.nix";
    config.x = {
      known = "v";
      bogus = 1;
    };
  };
in
{
  flake.tests.bare-site = {
    # RED: uncatchable infinite recursion (the gate is seq'd onto the config the mkIf reads).
    test-a-bare-tree-reads-a-self-referential-nested-mkif = {
      expr = {
        outerStrict = (run true (t1Of false) selfRef).config.x.sub.k;
        bothStrict = (run true (t1Of true) selfRef).config.x.sub.k;
        innerStrict = (run false (t1Of true) selfRef).config.x.sub.k;
        report = (run true (t1Of true) selfRef).undeclared;
      };
      expected = {
        outerStrict = "s";
        bothStrict = "s";
        innerStrict = "s";
        report = [ ];
      };
    };
    # RED: catchable — the gate forces the nested definition and `lazy-sub` fires on a sibling read.
    test-a-bare-tree-read-does-not-force-a-nested-definition = {
      expr = {
        outerStrict = forces (run true (t1Of false) subThrow).config.x.known;
        bothStrict = forces (run true (t1Of true) subThrow).config.x.known;
        subBadSiblingRead = forces (run true (t1Of false) subBad).config.x.known;
      };
      expected = {
        outerStrict = true;
        bothStrict = true;
        subBadSiblingRead = true;
      };
    };
    # RED: uncatchable — a leaf whose TYPE reads this eval's own config, typed bare, recursed
    # through the same walk of the nested-findings channel.
    test-a-config-derived-bare-leaf-type-reads-at-check =
      let
        r = evalModuleTree {
          check = true;
          modules = [
            {
              options.kindName = mkOption {
                type = t.str;
                default = "igloo";
              };
              options.registry = mkOption {
                type = if r.config.kindName == "igloo" then t.str else t.int;
                default = "r";
              };
              options.plain = mkOption { type = t.str; };
              config.plain = "ok";
            }
          ];
        };
      in
      {
        expr = {
          plain = r.config.plain;
          registry = r.config.registry;
          report = r.undeclared;
        };
        expected = {
          plain = "ok";
          registry = "r";
          report = [ ];
        };
      };
    # CONTROL, green on both arms: the refusal set is unchanged under a deep read, the report is
    # total, and an own-level finding still refuses at its owner's WHNF.
    test-a-bare-tree-still-refuses-and-reports-every-finding = {
      expr = {
        laxUnderStrictRefusedDeep = !(forces (run true (t1Of false) subBad).config);
        strictInnerRefusedDeep = !(forces (run false (t1Of true) subBad).config);
        ownRefusedAtOwner = !(forces (run true (t1Of false) ownBad).config.x.known);
        laxEverywhereIsAValue = (run false (t1Of false) subBad).config.x.sub;
        report = map (u: u.path) (run true (t1Of false) subBad).undeclared;
      };
      expected = {
        laxUnderStrictRefusedDeep = true;
        strictInnerRefusedDeep = true;
        ownRefusedAtOwner = true;
        laxEverywhereIsAValue = {
          k = "s";
        };
        report = [
          [
            "x"
            "sub"
            "bogus"
          ]
        ];
      };
    };
    # F1: warm == cold across a change of `check`, lax prior -> strict warm. The finding lives in a
    # reused nested leaf; the warm eval must refuse it as the cold strict eval does, and says why
    # it did not reuse.
    test-a-strict-warm-eval-over-a-lax-prior-refuses-as-cold-does = {
      expr = {
        warmDeep = val (warmAt false true nestedBase).config;
        coldDeep = val (coldAt true nestedBase).config;
        mode = (warmAt false true nestedBase).warmDecision.mode;
        reason = (warmAt false true nestedBase).warmDecision.reason;
        report = map (u: u.path) (warmAt false true nestedBase).undeclared;
      };
      expected = {
        warmDeep = "refused";
        coldDeep = "refused";
        mode = "cold";
        reason = "check differs from warmFrom's (warm refused)";
        report = [
          [
            "x"
            "sub"
            "bogus"
          ]
        ];
      };
    };
    # The mirror direction, strict prior -> lax warm: the cold lax eval is a value, and so is the warm
    # one. `root` has its finding at the root's own level, on a plain leaf's sibling.
    test-a-lax-warm-eval-over-a-strict-prior-is-the-cold-value = {
      expr = {
        nestedWarm = val (warmAt true false nestedBase).config.x;
        nestedCold = val (coldAt false nestedBase).config.x;
        rootWarm = val (warmAt true false rootBase).config.p;
        rootCold = val (coldAt false rootBase).config.p;
      };
      expected = {
        nestedWarm = {
          flag = false;
          known = "v";
          sub.k = "s";
        };
        nestedCold = {
          flag = false;
          known = "v";
          sub.k = "s";
        };
        rootWarm = "P";
        rootCold = "P";
      };
    };
    # CONTROL for the regime key: where `check` is unchanged the reuse survives, in both regimes.
    test-a-warm-eval-at-an-unchanged-check-still-reuses-the-nested-leaf = {
      expr = {
        strictReusesX = builtins.elem "x" (warmAt true true nestedBase).warmDecision.reused;
        laxReusesX = builtins.elem "x" (warmAt false false nestedBase).warmDecision.reused;
        strictMode = (warmAt true true nestedBase).warmDecision.mode;
        strictDeep = val (warmAt true true nestedBase).config;
        laxEqualsCold =
          builtins.toJSON (warmAt false false nestedBase).config
          == builtins.toJSON (coldAt false nestedBase).config;
      };
      expected = {
        strictReusesX = true;
        laxReusesX = true;
        strictMode = "warm";
        strictDeep = "refused";
        laxEqualsCold = true;
      };
    };
    # F2: a strict parent whose `apply` discards a lax nested tree's value never reads the owner, so
    # nothing refuses; nixpkgs gives the same value. The finding is still reported.
    test-a-strict-parent-whose-apply-discards-a-lax-nested-tree-reads-the-apply-value =
      let
        r = evalModuleTree {
          check = true;
          modules = [
            {
              options.x = mkOption {
                type = t1Of false;
                apply = _: "const";
              };
            }
            subBad
          ];
        };
      in
      {
        expr = {
          deep = val r.config;
          report = map (u: u.path) r.undeclared;
        };
        expected = {
          deep.x = "const";
          report = [
            [
              "x"
              "sub"
              "bogus"
            ]
          ];
        };
      };
  };
}
