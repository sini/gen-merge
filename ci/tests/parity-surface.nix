# The nixpkgs-PARITY SURFACE this landing adds: the shape-directed default-merge law
# (`mergeDefaultOption`) and the ORDER pass (`sortProperties` + `mkOrder`/`mkBefore`/`mkAfter`).
#
# ★ THE PARITY CLAIM IS WATCHED LIVE, NOT STAMPED. A rev-stamp drift oracle used to sit at the foot of
# this file; it was retired by owner ruling 2026-09-22. The note where it stood says what carries the
# property forward and what was deliberately given up — read it before restoring anything like it.
#
# ★★★ EVERY RED AND GREEN IN THIS FILE WAS EVALUATED BEFORE THE CELL WAS WRITTEN, NEVER DERIVED FROM
# READING SOURCE. RED was run against gen-merge as it stood before the pass landed; GREEN was run at
# the pinned nixpkgs, which is available up front precisely because the target is PARITY — correct is
# knowable before the fix exists. Each RED is recorded at its cell so a later reader can tell a cell
# that pins a fix from a cell that pins a coincidence.
#
# ★★ THE PARITY CELLS COMPARE AGAINST THE LIVE nixpkgs, NOT A TRANSCRIPTION OF IT. Every law cell
# below asserts BOTH sides in one `expr` — this library's answer and `nixpkgsLib`'s on the same
# `(loc, defs)` — against literal expected values. Asserting only the two against each other would
# pass an implementation that copied a nixpkgs bug; asserting only the literal would let the two
# drift apart silently. The fixtures are chosen so the two sides would DIVERGE under a wrong
# implementation: every multi-definition fixture uses DIFFERING, ORDERED payloads, so an
# agree-or-refuse law, a first-wins law and a reversed-order law each red.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  np = nixpkgsLib;

  # `defs` in both engines are `[{ file; value; }]`.
  defsOf =
    vals:
    map (v: {
      file = "<f>";
      value = v;
    }) vals;
  bothLaws =
    vals:
    let
      d = defsOf vals;
    in
    {
      gen = gm.mergeDefaultOption [ "k" ] d;
      nixpkgs = np.mergeDefaultOption [ "k" ] d;
    };
  refuses =
    v:
    (builtins.tryEval (
      let
        r = v;
      in
      builtins.deepSeq r r
    )).success;

  # ── the ORDER fixtures, run through BOTH engines from ONE source ──────────────────────────────
  # Parameterized over the constructor set so neither engine gets its own fixture — the oracle
  # suite's idiom (ci/tests/oracle.nix).
  listFx = a: b: c: P: [
    {
      options.xs = P.mkOption {
        type = P.types.listOf P.types.str;
        default = [ ];
      };
    }
    { config.xs = a P; }
    { config.xs = b P; }
    { config.xs = c P; }
  ];
  # ★ THE AUTHORED ORDER IS ADVERSARIAL ON PURPOSE. Collection order at this plane is REVERSE
  # flattened-module order in BOTH engines (control-order-pass-is-not-a-no-op measures it), so the
  # marker-free reading of these same three modules is `[ "c" "b" "a" ]` — the exact reverse of the
  # sorted answer. A pass that strips wrappers and does not sort cannot fake this cell.
  sorted = listFx (P: P.mkBefore [ "a" ]) (P: [ "b" ]) (P: P.mkAfter [ "c" ]);
  unmarked = listFx (P: [ "a" ]) (P: [ "b" ]) (P: [ "c" ]);
  forced = listFx (P: P.mkBefore [ "a" ]) (P: P.mkForce [ "FORCED" ]) (P: P.mkAfter [ "c" ]);

  rawFx = def: P: [
    { options.k = P.mkOption { type = P.types.raw; }; }
    { config.k = def P; }
  ];

  # A CHECK-ONLY `mkOptionType`, declared through each engine's OWN constructor: no fold is stated, so
  # the fold is the constructor's default. Two files define the option, in the order given.
  threadFx = a: b: P: [
    {
      options.heddle = P.mkOption {
        type = P.mkOptionType {
          name = "thread";
          check = v: v != null;
        };
      };
    }
    {
      _file = "/demo/warp.nix";
      config.heddle = a;
    }
    {
      _file = "/demo/weft.nix";
      config.heddle = b;
    }
  ];

  gmP = {
    inherit (gm)
      mkOption
      mkOptionType
      mkForce
      mkBefore
      mkAfter
      types
      ;
  };
  npP = {
    inherit (np)
      mkOption
      mkOptionType
      mkForce
      mkBefore
      mkAfter
      types
      ;
  };
  gmCfg = fx: (gm.evalModuleTree { modules = fx gmP; }).config;
  npCfg = fx: builtins.removeAttrs (np.evalModules { modules = fx npP; }).config [ "_module" ];
  bothCfg = fx: attr: {
    gen = (gmCfg fx).${attr};
    nixpkgs = (npCfg fx).${attr};
  };
in
{
  flake.tests.parity-surface = {
    # ── O11: the default-merge law, one cell per arm, both engines, ordered payloads ────────────
    # RED for every cell below: `mergeDefaultOption` did not exist in this library (measured absent
    # at the pin, whole repo). GREEN: the nixpkgs value measured on the same input — first at
    # `44a91898`, and RE-DERIVED on every run since, because the `nixpkgs` arm of `bothLaws` calls
    # upstream's function live. The rev names where the literal was first read, NOT a basis the
    # suite asserts; no rev is stamped anywhere (see the retirement note at the foot of this file).
    test-law-singleton = {
      expr = bothLaws [ 42 ];
      expected = {
        gen = 42;
        nixpkgs = 42;
      };
    };

    # DISCRIMINATING: differing lists CONCATENATE, in definition order. An agree-or-refuse law reds;
    # so does a law that reverses, and so does one that takes `head`.
    test-law-all-lists-concatenate = {
      expr = bothLaws [
        [ 1 ]
        [
          2
          3
        ]
      ];
      expected = {
        gen = [
          1
          2
          3
        ];
        nixpkgs = [
          1
          2
          3
        ];
      };
    };

    # DISCRIMINATING, and it is the arm the interim marker is ABOUT: the fold is `//`, so it is
    # SHALLOW and LAST-WINS per key. `a` is defined in both definitions with different values, so a
    # first-wins fold reds and a deep merge reds.
    test-law-all-attrsets-shallow-last-wins = {
      expr = bothLaws [
        { a = 1; }
        {
          a = 2;
          b = 3;
        }
      ];
      expected = {
        gen = {
          a = 2;
          b = 3;
        };
        nixpkgs = {
          a = 2;
          b = 3;
        };
      };
    };

    # DISCRIMINATING: DIFFERING bools are OR'd — they do NOT refuse. An agree-or-refuse law reds.
    test-law-differing-bools-are-ored = {
      expr = bothLaws [
        false
        true
      ];
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };

    # The negative twin of the cell above, same run: OR is not "always true". Without it, a law that
    # returned `true` unconditionally on bools would pass.
    test-control-agreeing-false-bools-stay-false = {
      expr = bothLaws [
        false
        false
      ];
      expected = {
        gen = false;
        nixpkgs = false;
      };
    };

    # DISCRIMINATING: DIFFERING strings CONCATENATE — they do not refuse — and `"ab"` rather than
    # `"ba"` pins the direction of the fold.
    test-law-differing-strings-concatenate = {
      expr = bothLaws [
        "a"
        "b"
      ];
      expected = {
        gen = "ab";
        nixpkgs = "ab";
      };
    };

    test-law-agreeing-ints-pass-through = {
      expr = bothLaws [
        7
        7
      ];
      expected = {
        gen = 7;
        nixpkgs = 7;
      };
    };

    # ── the two inputs that REACH the refusal, and they are the only two ────────────────────────
    # Differing INTS refuse where differing bools and strings did not — that asymmetry is the law,
    # and these cells are what stop it being read as "scalars refuse". Catchability is the assertion
    # here; the refusal's NAME is asserted in ci/tests-error.nix, which is the only output that can.
    test-law-differing-ints-refuse-catchably = {
      expr = {
        gen = refuses (
          gm.mergeDefaultOption [ "k" ] (defsOf [
            1
            2
          ])
        );
        nixpkgs = refuses (
          np.mergeDefaultOption [ "k" ] (defsOf [
            1
            2
          ])
        );
      };
      expected = {
        gen = false;
        nixpkgs = false;
      };
    };

    test-law-heterogeneous-defs-refuse-catchably = {
      expr = {
        gen = refuses (
          gm.mergeDefaultOption [ "k" ] (defsOf [
            1
            "a"
          ])
        );
        nixpkgs = refuses (
          np.mergeDefaultOption [ "k" ] (defsOf [
            1
            "a"
          ])
        );
      };
      expected = {
        gen = false;
        nixpkgs = false;
      };
    };

    # LIVE CONTROL for the two cells above, same instrument and same run: `refuses` must be able to
    # report a SUCCESS, or a law that refused everything would pass both of them. Without this the
    # two `false`s are consistent with a broken predicate.
    test-control-refusal-probe-reports-success-too = {
      expr = {
        gen = refuses (
          gm.mergeDefaultOption [ "k" ] (defsOf [
            7
            7
          ])
        );
        nixpkgs = refuses (
          np.mergeDefaultOption [ "k" ] (defsOf [
            7
            7
          ])
        );
      };
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };

    # ── the FUNCTION arm — POINTWISE, and the one measured divergence ───────────────────────────
    # ★ THIS CELL ASSERTS gen's SIDE ALONE, AND THAT IS THE FINDING RATHER THAN A GAP IN THE CELL.
    # nixpkgs' own multi-function arm recurses with RAW VALUES into a parameter that immediately
    # applies `getValues`, so on these two ordinary functions it dies UNCATCHABLY at the pinned rev
    # (`expected a set but found a list`) — measured, with a catchable refusal on the same
    # instrument in the same run as the control. There is no nixpkgs value to compare against, so
    # putting one here would be inventing it. lib/modules.nix declares the divergence at the law.
    # `[ 1 2 ]` is what POINTWISE-then-merge gives; COMPOSITION would give `[ [ 2 ] ]`, so this
    # value is also what separates the ruled reading from the one nixpkgs' docstring describes.
    test-law-functions-apply-pointwise-not-composed = {
      expr =
        (gm.mergeDefaultOption [ "k" ] (defsOf [
          (x: [ x ])
          (x: [ (x + 1) ])
        ]))
          1;
      expected = [
        1
        2
      ];
    };

    # The SINGLETON function is on the fast path and is NOT the divergent arm, so here both engines
    # answer and the cell is a real parity cell — which is what fences the divergence to arity > 1.
    test-control-single-function-is-parity = {
      expr = {
        gen = (gm.mergeDefaultOption [ "k" ] (defsOf [ (x: [ x ]) ])) 3;
        nixpkgs = (np.mergeDefaultOption [ "k" ] (defsOf [ (x: [ x ]) ])) 3;
      };
      expected = {
        gen = [ 3 ];
        nixpkgs = [ 3 ];
      };
    };

    # ── the CONSTRUCTOR'S default: a check-only `mkOptionType` folds by nixpkgs' law ─────────────
    # nixpkgs' `mkOptionType` takes `merge ? mergeDefaultOption`; a descriptor stating `name` and no
    # fold gets that default here too (lib/interface.nix `importDescriptor`). Parity criterion, owner
    # 2026-09-25: take nixpkgs' value where it is not silent. RED for each cell below was evaluated
    # at gen-merge 6a508e3, whose constructor folded agree-or-refuse; it is recorded per cell. The
    # carve-outs (differing values at a shared attrset key, functions) refuse, and their cells are on
    # the error plane (ci/tests-error.nix `mkoptiontype-default-merge`), which can read the message.
    #
    # RED: ☢ refused, lists are not equal.
    test-mkoptiontype-default-lists-concatenate = {
      expr = bothCfg (threadFx [ "warp" ] [ "weft" ]) "heddle";
      expected = {
        gen = [
          "weft"
          "warp"
        ];
        nixpkgs = [
          "weft"
          "warp"
        ];
      };
    };
    # RED: ❌ gen `"a"` — agree-or-refuse passed equal strings through, a changed value with no word.
    test-mkoptiontype-default-equal-strings-concatenate = {
      expr = bothCfg (threadFx "a" "a") "heddle";
      expected = {
        gen = "aa";
        nixpkgs = "aa";
      };
    };
    # RED: ☢ refused.
    test-mkoptiontype-default-differing-strings-concatenate = {
      expr = bothCfg (threadFx "warp" "weft") "heddle";
      expected = {
        gen = "weftwarp";
        nixpkgs = "weftwarp";
      };
    };
    # The payloads are chosen so the LAST definition read is `false`: OR gives `true`, last-wins would
    # not. RED: ☢ refused.
    test-mkoptiontype-default-differing-bools-are-ored = {
      expr = bothCfg (threadFx false true) "heddle";
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
    # RED: ☢ refused. Disjoint keys: `//` drops nothing, so nixpkgs' value is not silent.
    test-mkoptiontype-default-disjoint-attrsets-union = {
      expr = bothCfg (threadFx { a = 1; } { b = 2; }) "heddle";
      expected = {
        gen = {
          a = 1;
          b = 2;
        };
        nixpkgs = {
          a = 1;
          b = 2;
        };
      };
    };
    # A SHARED key carrying EQUAL values also drops nothing, so the carve-out does not reach it: it
    # is a differing value at a shared key that `//` loses. RED: ☢ refused (the whole values differ).
    test-mkoptiontype-default-attrsets-sharing-an-equal-key-union = {
      expr = bothCfg (threadFx
        {
          a = 1;
          b = 1;
        }
        {
          a = 1;
          c = 2;
        }
      ) "heddle";
      expected = {
        gen = {
          a = 1;
          b = 1;
          c = 2;
        };
        nixpkgs = {
          a = 1;
          b = 1;
          c = 2;
        };
      };
    };
    # Equal ints pass through in both laws, so this cell is green at 6a508e3 by design; it fences
    # the change from over-reaching. RED driven with a planted default that refuses every int.
    test-mkoptiontype-default-equal-ints-pass = {
      expr = bothCfg (threadFx 3 3) "heddle";
      expected = {
        gen = 3;
        nixpkgs = 3;
      };
    };

    # ── O13: the SINGLE-DEF order-marker LEAK — the cheapest demonstration of the pass ──────────
    # It needs no multi-def and it tests the UNWRAP ALONE.
    # RED, MEASURED before the pass landed: `{ _type = "order"; content = "x"; priority = 500; }` —
    # the raw wrapper, verbatim, as the config value. GREEN, MEASURED at the pinned nixpkgs on the
    # same fixture: `"x"`.
    test-single-order-marker-is-unwrapped = {
      expr = bothCfg (rawFx (P: P.mkBefore "x")) "k";
      expected = {
        gen = "x";
        nixpkgs = "x";
      };
    };

    # CONTROL, same run, BOTH SIDES MEASURED: the same position with no wrapper read `"x"` before
    # the pass and `"x"` after, at both engines. This is what separates "the pass unwraps the
    # marker" from "the fixture stopped reaching the arm".
    test-control-unwrapped-def-at-the-same-position = {
      expr = bothCfg (rawFx (P: "x")) "k";
      expected = {
        gen = "x";
        nixpkgs = "x";
      };
    };

    # ── the ORDER pass actually REORDERS — O13 is satisfied by a pass that strips and ignores ───
    # RED, MEASURED before the pass landed: an UNCATCHABLE abort, `expected a list but found a set:
    # { _type = "order"; … }` — the wrappers reached `listOf`'s element check. GREEN, MEASURED at
    # the pinned nixpkgs on the same fixture: `[ "a" "b" "c" ]`, priorities 500 / 1000 / 1500
    # ascending. Because the RED is an uncatchable abort it cannot be asserted in-suite; the GREEN
    # is the whole of this cell, and what a failing run looks like is written below.
    #
    # ★ THIS IS THE CELL THAT CATCHES THE TWO PORT ERRORS NOTHING ELSE SEES:
    #   · a VERBATIM port of nixpkgs' `strip`/`compare` reads `def.priority or defaultOrderPriority`
    #     and finds gen-merge's STAMPED override 100 already sitting there on the plain def, sorting
    #     it first ⇒ `[ "b" "a" "c" ]`;
    #   · sorting BEFORE `filterOverrides` turns the order numbers into override numbers, the filter
    #     keeps only the minimum, ONE definition survives ⇒ no three-element answer at all.
    # Both are invisible to O13 and to either control below.
    test-order-pass-sorts-by-order-priority = {
      expr = bothCfg sorted "xs";
      expected = {
        gen = [
          "a"
          "b"
          "c"
        ];
        nixpkgs = [
          "a"
          "b"
          "c"
        ];
      };
    };

    # CONTROL (a) — the same three modules in the same authored order with NO markers. It
    # DISCRIMINATES: `[ "c" "b" "a" ]` is the reverse of the subject's answer, so a pass that never
    # sorted would make the two cells agree. It also measures the fact the subject rests on —
    # collection order at this plane is REVERSE flattened-module order, identically at both engines —
    # and it was `[ "c" "b" "a" ]` before the pass landed too, so it is byte-identical across it.
    test-control-order-pass-is-not-a-no-op = {
      expr = bothCfg unmarked "xs";
      expected = {
        gen = [
          "c"
          "b"
          "a"
        ];
        nixpkgs = [
          "c"
          "b"
          "a"
        ];
      };
    };

    # CONTROL (b) — an OVERRIDE alongside the order markers. `mkForce` is priority 50 against
    # `mkBefore`'s order priority 500, and the two live on DIFFERENT number lines: the override pass
    # must consume its axis before the order pass writes the other one. Measured `[ "FORCED" ]` at
    # nixpkgs and `[ "FORCED" ]` at gen-merge before the pass landed — byte-identical across it,
    # which is what an invariance control should be.
    # ★ IT IS AN INVARIANCE CONTROL, NOT A PASS-ORDER DETECTOR, and saying so is the point: lowest
    # priority-number wins, `mkForce` is 50 and `mkBefore` is 500, so `mkForce` wins under EITHER
    # pass order and this cell agrees under both. The pass-order detector is the subject cell above.
    test-control-override-axis-survives-the-order-pass = {
      expr = bothCfg forced "xs";
      expected = {
        gen = [ "FORCED" ];
        nixpkgs = [ "FORCED" ];
      };
    };

    # ── RETIRED 2026-09-22: O15, the rev-stamp drift oracle, and its control ────────────────────
    # ★★★ WHAT CARRIES THE PARITY PROPERTY FORWARD: the `nixpkgs` arm of `bothLaws` in this file's
    # `let`, which calls `np.mergeDefaultOption` — nixpkgs' OWN function, evaluated LIVE at whatever
    # rev `ci/flake.lock` resolves. Every O11 law cell above goes through `bothLaws` and asserts BOTH
    # sides against literal expected values, so an upstream change to the merge law reds those cells
    # on the PROPERTY. The order cells do the same through `bothCfg`/`npCfg`. Parity is not left
    # unwatched by this removal; it is watched DIRECTLY instead of through a proxy.
    #
    # ★★ WHAT IS DELIBERATELY GIVEN UP: LOCK-MOVEMENT NOTIFICATION. O15 stated a nixpkgs rev in
    # source text and asserted `ci/flake.lock` agreed with it, both directions, so a routine bump
    # redded it with both laws byte-unchanged — intended, as a prompt to re-verify and re-stamp. The
    # 2026-09-22 roster relock is what that cost: the red refused publication at this node and
    # skipped 11 downstream members plus both trailing nodes. Owner ruling that day, verbatim — *"the
    # parity contract should move with upstream, remove the hardcode"*. There is now NO signal when
    # the pin moves; the property is re-checked on every run against whatever it moved to.
    #
    # ★ SO DO NOT RESTORE THE STAMP BELIEVING PARITY WENT UNWATCHED — it did not — and do not
    # "preserve" it by deriving the stated rev from the lock: that makes the comparison vacuously
    # true, and a drift oracle that cannot fail is the defect it exists to prevent.
  };
}
