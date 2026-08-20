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
{ genLinkset, ... }:
let
  ok = e: (builtins.tryEval e).success;
  refuses = e: !(builtins.tryEval e).success;

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

  # (iii) AN UNDECLARED COLLISION REFUSES, and (ii) A GROUNDLESS ENTRY DOES NOT CONSTRUCT.
  flake.tests.linkset.test-undeclared-and-groundless-refuse = {
    expr = {
      undeclared =
        refuses
          (genLinkset.mergeExports {
            left = L;
            right = R;
            allow = { };
          }).exports;
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
  # FAILS if anyone later swaps in a `÷` check, which is the outcome it exists to prevent.
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
        }).exports;
    expected = true;
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

  # A STALE EXEMPTION — an allowlist entry naming no actual collision — refuses too: it reads as a
  # decided overlap and decides nothing.
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
}
