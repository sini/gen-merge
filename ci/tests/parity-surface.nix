# The nixpkgs-PARITY SURFACE this landing adds: the shape-directed default-merge law
# (`mergeDefaultOption`), the ORDER pass (`sortProperties` + `mkOrder`/`mkBefore`/`mkAfter`), and the
# drift oracle that keeps the parity claim from ageing silently.
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
  lib,
  genMerge,
  nixpkgsLib,
  prelude,
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

  gmP = {
    inherit (gm)
      mkOption
      mkForce
      mkBefore
      mkAfter
      types
      ;
  };
  npP = {
    inherit (np)
      mkOption
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

  # ── the DRIFT oracle's two sides ──────────────────────────────────────────────────────────────
  # The rev the parity claim is STAMPED at, read back out of the committed source between its
  # markers — structural, not line-numbered, so an edit above or below cannot silently move it.
  exportSource = builtins.readFile ../../lib/default.nix;
  window = lib.elemAt (lib.splitString "nixpkgs-parity-rev:end" (lib.elemAt (lib.splitString "nixpkgs-parity-rev:begin" exportSource) 1)) 0;
  # The window is comment lines: strip the `#` markers and all whitespace, leaving the bare rev.
  statedRev = lib.concatStrings (
    lib.filter (s: s != "#") (lib.splitString "#" (lib.replaceStrings [ "\n" " " ] [ "" "" ] window))
  );

  # ★ THE NODE SELECTION IS THE WHOLE CORRECTNESS OF THIS CELL, AND THE LOCK CARRIES A DECOY.
  # `ci/flake.lock` holds more than one nixpkgs-bearing node, and the one literally NAMED `nixpkgs`
  # is NOT this flake's: it is a transitive node, and reading it would give a plausible rev rather
  # than an error. The right node is whatever the ROOT's own `nixpkgs` input resolves to — which the
  # lock happens to name `nixpkgs_2` — so it is reached by INDIRECTION through `root.inputs`, never
  # by spelling a node name.
  lock = builtins.fromJSON (builtins.readFile ../flake.lock);
  lockedRev = lock.nodes.${lock.nodes.root.inputs.nixpkgs}.locked.rev;
in
{
  flake.tests.parity-surface = {
    # ── O11: the default-merge law, one cell per arm, both engines, ordered payloads ────────────
    # RED for every cell below: `mergeDefaultOption` did not exist in this library (measured absent
    # at the pin, whole repo). GREEN: the nixpkgs value measured on the same input at `b5aa0fbd`.
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

    # ── O15: THE PARITY-DRIFT ORACLE ────────────────────────────────────────────────────────────
    # The exported law and the order pass are an INDEPENDENT REIMPLEMENTATION — `lib/` is
    # nixpkgs-free (ci/tests/purity.nix) — so parity is a claim verified once against a pinned rev
    # with nothing watching upstream. This binds the stated rev to the resolved one, BOTH
    # DIRECTIONS, so the claim cannot age in silence.
    # ★ WHAT IT DETECTS, stated so it is not over-read: LOCK MOVEMENT, not module-system drift. A
    # routine nixpkgs bump reds it with both laws byte-unchanged. That is intended — it is a prompt
    # to re-verify parity and re-stamp the rev, not an assertion that the law broke.
    test-parity-rev-stamp-matches-the-lock = {
      expr = {
        stated = statedRev;
        locked = lockedRev;
        agree = statedRev == lockedRev;
      };
      expected = {
        stated = "b5aa0fbd538984f6e3d201be0005b4463d8b09f8";
        locked = "b5aa0fbd538984f6e3d201be0005b4463d8b09f8";
        agree = true;
      };
    };

    # CONTROL for the oracle, same run: without it the comparison may not be wired to anything, and
    # a drift oracle that cannot fail is the defect it exists to prevent. It asserts that BOTH
    # readers actually read — that the stated rev came out of the file rather than out of a
    # default, and that the lock reader followed `root.inputs.nixpkgs` to a node that is NOT the
    # decoy literally named `nixpkgs`.
    test-control-both-drift-readers-are-live = {
      expr = {
        stated-is-a-full-rev = prelude.stringLength statedRev == 40;
        node-reached-by-indirection = lock.nodes.root.inputs.nixpkgs;
        decoy-node-is-a-different-rev = lock.nodes.nixpkgs.locked.rev != lockedRev;
      };
      expected = {
        stated-is-a-full-rev = true;
        node-reached-by-indirection = "nixpkgs_2";
        decoy-node-is-a-different-rev = true;
      };
    };
  };
}
