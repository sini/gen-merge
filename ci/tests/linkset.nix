# THE EXPORT MERGE — Cardelli's linkset discipline at `lib/default.nix`'s `types` assembly.
#
# The site merges two libraries' export environments. It used to do that with bare `//`: a
# non-empty intersection, silently resolved by Nix's right bias. Cardelli 1997 gates a linkset
# merge on `exp(L) ∩ exp(L') = ∅` (Definition 5-7's precondition), and where the overlap is real
# the implementable form is disjointness WITH A DECLARED ALLOWLIST.
#
# ★ WHY THESE CELLS AND NOT A COMPATIBILITY TEST. Cardelli Definition 5-5's `÷` — the two
# environments agree on every shared name — cannot be evaluated at THIS relatum: the colliding
# entries are CONSTRUCTORS, and gen's type equality is not total over functions (it forces `v.name`
# on a lambda and the abort escapes `tryEval`). A precondition unevaluable at the merged objects is
# not a precondition.
{
  genLinkset,
  genMergeCompat,
  genMergeWith,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  ok = e: (builtins.tryEval e).success;
  refuses = e: !(builtins.tryEval e).success;

  # The allowlist the library reads, by the same path — not a second copy of it.
  allowlist = import ../../lib/types-allowlist.nix;

  # A vocabulary gen-merge never saw, lacking every allowlist name.
  np = nixpkgsLib.types;
  V = { inherit (np) str int bool; };
  overV = genMergeWith V;
  readV =
    v:
    (overV.evalModuleTree {
      modules = [
        { options.p = overV.mkOption { type = overV.types.str; }; }
        { p = v; }
      ];
    }).config.p;
  # The same vocabulary padded with every allowlist name (`foreign-leaf-check.nix`'s `compat` shape).
  padded = V // {
    inherit (np) attrs listOf attrsOf;
    option = np.nullOr;
  };

  # ROSTER HYGIENE (claim (ii)): every allowlist entry still names a collision WITH THE SHIPPED
  # ROSTER. It lives here because this is where the roster is pinned; `lib/` sees only an argument.
  rosterMissing = roster: builtins.filter (n: !(roster ? ${n})) (builtins.attrNames allowlist);

  L = {
    library = "gen-types";
    exports = {
      a = 1;
      shared = "LEFT";
      onlyLeft = 9;
    };
  };
  R = {
    library = "gen-merge";
    exports = {
      b = 2;
      shared = "RIGHT";
    };
  };
  merged = genLinkset.mergeExports {
    left = L;
    right = R;
    allow.shared.ground = "the right side wins here because X";
  };
in
{
  # (i) THE ADMITTED SHADOW RESOLVES RIGHT AND KEEPS ITS LOSER REACHABLE. The retention record is
  # REQUIRED AND PERMANENT (owner-ruled): Leijen's remedy applied where the shadow is ADMITTED. A
  # shadow whose loser is unreachable is a silent drop wearing a declaration.
  flake.tests.linkset.test-admitted-shadow-retains-its-loser = {
    expr = {
      rightWins = merged.exports.shared;
      shadowedValue = merged.admitted.shared.overridden.value;
      shadowedLibrary = merged.admitted.shared.overridden.library;
      shadowingLibrary = merged.admitted.shared.shadowedBy;
      groundIsCarried = merged.admitted.shared.ground != "";
    };
    expected = {
      rightWins = "RIGHT";
      shadowedValue = "LEFT";
      shadowedLibrary = "gen-types";
      shadowingLibrary = "gen-merge";
      groundIsCarried = true;
    };
  };

  # (iv) A NON-COLLIDING NAME FROM THE LOSING SIDE STILL LANDS — the merge decides overlaps, it does
  # not narrow the union.
  flake.tests.linkset.test-non-colliding-name-still-lands = {
    expr = merged.exports.onlyLeft;
    expected = 9;
  };

  # (iii) AN UNDECLARED COLLISION REFUSES AT ITS NAME, and (ii) A GROUNDLESS ENTRY DOES NOT
  # CONSTRUCT — the second is a defect in the right side's own declaration, so it stays whole-merge.
  flake.tests.linkset.test-undeclared-and-groundless-refuse = {
    expr = {
      undeclared =
        refuses
          (genLinkset.mergeExports {
            left = L;
            right = R;
            allow = { };
          }).exports.shared;
      groundless =
        refuses
          (genLinkset.mergeExports {
            left = L;
            right = R;
            allow.shared.ground = "";
          }).exports;
    };
    expected = {
      undeclared = true;
      groundless = true;
    };
  };

  # THE DISTINCTNESS FLOOR — no entry's ground may be byte-identical to another's. ★ Its limit is
  # stated rather than papered over: this catches the VERBATIM copy only. A paraphrased ground
  # defeats it, and no predicate writable here catches that — the substantive question, does this
  # ground actually hold OF THIS NAME, is an honest person-oracle sitting ON TOP of this floor.
  flake.tests.linkset.test-byte-identical-grounds-refuse = {
    expr =
      refuses
        (genLinkset.mergeExports {
          left = {
            library = "l";
            exports = {
              p = 1;
              q = 1;
            };
          };
          right = {
            library = "r";
            exports = {
              p = 2;
              q = 2;
            };
          };
          allow = {
            p.ground = "same words";
            q.ground = "same words";
          };
        }).exports;
    expected = true;
  };

  # ★★ THE DISCRIMINATING CONTROL, and it is the cell that separates the two mechanisms. A collision
  # whose two values AGREE must STILL be declared. A COMPATIBILITY test would admit it silently —
  # that is what `÷` means — whereas disjointness requires the decision either way. So this cell
  # FAILS if anyone later swaps in a `÷` check, which is the outcome it exists to prevent. The
  # refusal is per name, so the cell demands the name.
  flake.tests.linkset.test-control-agreeing-collision-still-requires-declaration = {
    expr =
      refuses
        (genLinkset.mergeExports {
          left = {
            library = "l";
            exports.same = 7;
          };
          right = {
            library = "r";
            exports.same = 7;
          };
          allow = { };
        }).exports.same;
    expected = true;
  };

  # AN ADMITTED SHADOW AND AN UNDECLARED COLLISION IN ONE LINK. The undecided name refuses by name
  # and takes nothing else with it: the admitted shadow resolves and keeps its retention record,
  # and a non-colliding name lands.
  flake.tests.linkset.test-undeclared-collision-refuses-only-its-name = {
    expr =
      let
        m = genLinkset.mergeExports {
          left = {
            library = "l";
            exports = {
              shared = "LEFT";
              clash = 1;
              onlyLeft = 9;
            };
          };
          right = {
            library = "r";
            exports = {
              shared = "RIGHT";
              clash = 2;
            };
          };
          allow.shared.ground = "the right side wins here because X";
        };
      in
      {
        shared = m.exports.shared;
        onlyLeft = m.exports.onlyLeft;
        admitted = builtins.attrNames m.admitted;
        overridden = m.admitted.shared.overridden.value;
        clashRefused = refuses m.exports.clash;
      };
    expected = {
      shared = "RIGHT";
      onlyLeft = 9;
      admitted = [ "shared" ];
      overridden = "LEFT";
      clashRefused = true;
    };
  };

  # A VOCABULARY SHARING AN UNDECLARED NAME WITH THE STRATEGIES STILL PUBLISHES THE REST (ADR-0025
  # item 1): a demand is judged only on the names it touches. `nullOr` is the one undecided name
  # here; it stays in the namespace, answering with its refusal (tests-error.nix), and the caller's
  # `str` and gen-merge's `listOf` publish beside it. The `1` definition is the paired control: a
  # namespace that published a non-checking `str` would read it.
  flake.tests.linkset.test-undeclared-collision-refuses-per-name = {
    expr =
      let
        W = genMergeWith { inherit (np) str nullOr; };
        read =
          type: v:
          (W.evalModuleTree {
            modules = [
              { options.p = W.mkOption { inherit type; }; }
              { p = v; }
            ];
          }).config.p;
      in
      {
        names = builtins.attrNames W.types;
        str = read W.types.str "sateen";
        listOf = read (W.types.listOf W.types.str) [ "sateen" ];
        strRefusesInt = refuses (read W.types.str 1);
        nullOrRefused = refuses W.types.nullOr;
      };
    expected = {
      names = [
        "anything"
        "attrs"
        "attrsOf"
        "deferredModule"
        "defineType"
        "either"
        "lazyAttrsOf"
        "listOf"
        "mkOption"
        "mkOptionType"
        "mkType"
        "nullOr"
        "oneOf"
        "option"
        "raw"
        "str"
        "submodule"
      ];
      str = "sateen";
      listOf = [ "sateen" ];
      strRefusesInt = true;
      nullOrRefused = true;
    };
  };

  # ...AND OVER NIXPKGS' WHOLE `lib.types`, THE REFUSING SET IS EXACTLY THE OLD WHOLE-NAMESPACE ONE:
  # the nine undeclared names, each refusing on its own, and every other name a value. No refusal
  # was lost to the per-name binding, and none was added.
  flake.tests.linkset.test-compat-namespace-refuses-exactly-its-undeclared-names = {
    expr = {
      count = builtins.length (builtins.attrNames genMergeCompat.types);
      refusing = builtins.filter (n: refuses genMergeCompat.types.${n}) (
        builtins.attrNames genMergeCompat.types
      );
    };
    expected = {
      count = 71;
      refusing = [
        "anything"
        "deferredModule"
        "either"
        "lazyAttrsOf"
        "mkOptionType"
        "nullOr"
        "oneOf"
        "raw"
        "submodule"
      ];
    };
  };

  # CONTROL ON THE INSTRUMENT: a merge with no overlap constructs in the same run. Without this,
  # every refusal cell above would pass against a `mergeExports` that refused everything.
  flake.tests.linkset.test-control-disjoint-merge-constructs = {
    expr =
      (genLinkset.mergeExports {
        left = {
          library = "l";
          exports.x = 1;
        };
        right = {
          library = "r";
          exports.y = 2;
        };
        allow = { };
      }).exports;
    expected = {
      x = 1;
      y = 2;
    };
  };

  # A STALE EXEMPTION — an allowlist entry naming nothing the RIGHT side exports — refuses: it reads
  # as a decided overlap and can decide nothing. The message is asserted in tests-error.nix.
  flake.tests.linkset.test-stale-allowlist-entry-refuses = {
    expr =
      refuses
        (genLinkset.mergeExports {
          left = {
            library = "l";
            exports.x = 1;
          };
          right = {
            library = "r";
            exports.y = 2;
          };
          allow.nosuch.ground = "names a collision that does not exist";
        }).exports;
    expected = true;
  };

  # AN INAPPLICABLE ENTRY IS NOT STALE. The entry names a name the right side exports and the left
  # lacks: there is no overlap at it for this link, so it decides nothing and shadows nothing, and
  # the merge constructs.
  flake.tests.linkset.test-inapplicable-entry-constructs = {
    expr =
      (genLinkset.mergeExports {
        left = {
          library = "l";
          exports = { };
        };
        right = {
          library = "gen-merge";
          exports.x = 1;
        };
        allow.x.ground = "the right side wins here because X";
      }).exports;
    expected = {
      x = 1;
    };
  };

  # A VOCABULARY LACKING EVERY ALLOWLIST NAME PUBLISHES its own names beside the strategies. Scoped:
  # this holds for a vocabulary whose overlap with the strategies is allowlisted; nixpkgs' whole
  # `lib.types` shares nine undeclared names, and each refuses by name (tests-error.nix).
  flake.tests.linkset.test-foreign-vocabulary-without-allowlist-names-publishes = {
    expr = builtins.attrNames overV.types;
    expected = [
      "anything"
      "attrs"
      "attrsOf"
      "bool"
      "deferredModule"
      "defineType"
      "either"
      "int"
      "lazyAttrsOf"
      "listOf"
      "mkOption"
      "mkOptionType"
      "mkType"
      "nullOr"
      "oneOf"
      "option"
      "raw"
      "str"
      "submodule"
    ];
  };

  # ...AND ITS OWN NAME STILL CHECKS, as a pair: the `1` side alone would also read "refused" if
  # `str` itself refused, so only the pair discriminates.
  flake.tests.linkset.test-foreign-vocabulary-own-name-mounts-and-checks = {
    expr = {
      good = readV "x";
      badRefused = refuses (readV 1);
    };
    expected = {
      good = "x";
      badRefused = true;
    };
  };

  # EACH ALLOWLIST NAME, REMOVED ALONE from a vocabulary carrying all of them, leaves a namespace
  # that publishes. The live half of the pair is the padded vocabulary itself.
  flake.tests.linkset.test-each-allowlist-name-is-droppable-from-the-vocabulary = {
    expr = {
      padded = ok (builtins.attrNames (genMergeWith padded).types);
      dropped = builtins.mapAttrs (
        n: _: ok (builtins.attrNames (genMergeWith (removeAttrs padded [ n ])).types)
      ) allowlist;
    };
    expected = {
      padded = true;
      dropped = builtins.mapAttrs (_: _: true) allowlist;
    };
  };

  # ROSTER HYGIENE — the shipped gen-types still collides at every allowlist entry; the planted drift
  # (one name removed) is the same-run control that the predicate can fire.
  flake.tests.linkset.test-every-allowlist-entry-names-a-shipped-roster-collision = {
    expr = {
      shipped = rosterMissing genTypes;
      plantedDrift = rosterMissing (removeAttrs genTypes [ "listOf" ]);
    };
    expected = {
      shipped = [ ];
      plantedDrift = [ "listOf" ];
    };
  };
}
