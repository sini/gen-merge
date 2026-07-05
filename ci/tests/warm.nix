# Warm re-eval path (design spec §§1-4) — the opt-in memoized-override eval.
#
# TWO layers, TWO commits:
#   • 2a (this file's first block) — the pure DECISION layer (`warmDecide` + `collectModules`), reached
#     through the internal `genMergeCore` seam (the classify-suite precedent): footprint contents, the
#     coarse freeform-reuse flag (both conditions), the disabledModules refusal, and the EDITED-tail
#     identity (the engine flattens `editedModules` itself; tail-k of the full flatten == the edited
#     flatten, imports included). No splicing yet — these assert the decision, not the merge.
#   • 2b (the byte-oracle block) — `evalModuleTree { warmFrom; editedModules; }` splice execution: warm
#     result toJSON == cold result toJSON on VALUES and PROVENANCE, across registry reuse, decl-side
#     dirtiness, the three freeform scenarios, the group-splice hazard, the two adversarial markers,
#     disabledModules fallback, and chained warm.
{ genMerge, genMergeCore, ... }:
let
  gm = genMerge;
  inherit (gm)
    evalModuleTree
    pureModule
    mkOption
    mkForce
    ;
  inherit (genMergeCore)
    warmDecide
    collectModules
    ;
  t = gm.types;

  # A hand-built merged decl tree for the `warmDecide` unit fixtures (isOptLeaf leaves at a/b/c/d).
  opt = mkOption { type = t.int; };
  allOptions4 = {
    a = opt;
    b = opt;
    c = opt;
    d = opt;
  };

  # ── flat-entry constructors (the `collectModules` output shape { _file; content; srcClass }) ──
  clean = file: content: {
    _file = file;
    inherit content;
    srcClass = "attrset";
  };
  markedPure = file: content: {
    _file = file;
    inherit content;
    srcClass = "marked-pure";
  };
  dirty = file: content: {
    _file = file;
    inherit content;
    srcClass = "dirty";
  };

  # identity callM — the `warmDecide`/`collectModules` fixtures are all plain attrset modules.
  idCallM = m: m;

  # ── the byte oracle (design spec §6 / the standing A2 tooth) ─────────────────────────────────────
  # `warmOf base edited` = re-eval of `base ++ edited` warm-started from cold(`base`), with `edited` the
  # appended list. `coldOf` is the reference. The tooth: warm result toJSON == cold result toJSON on
  # VALUES and PROVENANCE (toJSON drops nothing here — the fixtures are function-free data).
  coldOf = mods: evalModuleTree { modules = mods; };
  warmOf =
    base: edited:
    evalModuleTree {
      modules = base ++ edited;
      warmFrom = coldOf base;
      editedModules = edited;
    };
  jsonEq = a: b: builtins.toJSON a == builtins.toJSON b;
  byteOracle =
    base: edited:
    let
      w = warmOf base edited;
      c = coldOf (base ++ edited);
    in
    jsonEq w.config c.config && jsonEq w.provenance c.provenance;
in
{
  flake.tests.warm = {
    # ══ 2a — DECISION LAYER ═══════════════════════════════════════════════════════════════════════

    # Footprint: a dirty DEF (config.c) and a dirty DECL (options.d) each add their leaf; clean modules
    # (a, b) add nothing. Reasons distinguish def from decl, tagged with the originating file.
    test-footprint-dirty-def-and-decl = {
      expr =
        (warmDecide {
          flat = [
            (clean "clean-a" {
              options.a = opt;
              config.a = 1;
            })
            (clean "clean-b" { config.b = 2; })
            (dirty "dirty-c" { config.c = 3; })
            (dirty "dirty-d" { options.d = opt; })
          ];
          editedCount = 0;
          allOptions = allOptions4;
        }).footprint;
      expected = [
        {
          path = [ "c" ];
          reason = "dirty-def dirty-c";
        }
        {
          path = [ "d" ];
          reason = "dirty-decl dirty-d";
        }
      ];
    };

    # The clean/dirty/edited partition (module file lists) + the EDITED tail: the last `editedCount`
    # entries are EDITED regardless of srcClass (an edited attrset is still edited), and a marked-pure
    # non-edited entry is CLEAN.
    test-module-partition-and-edited-tail = {
      expr =
        (warmDecide {
          flat = [
            (clean "clean-a" { config.a = 1; })
            (markedPure "pure-b" { config.b = 2; })
            (dirty "dirty-c" { config.c = 3; })
            (clean "edited-d" { config.d = 4; })
          ];
          editedCount = 1;
          allOptions = allOptions4;
        }).modules;
      expected = {
        clean = [
          "clean-a"
          "pure-b"
        ];
        dirty = [ "dirty-c" ];
        edited = [ "edited-d" ];
      };
    };

    # An EDITED entry's footprint uses the "edited-def" reason for BOTH its decls and its defs.
    test-edited-entry-footprint = {
      expr =
        (warmDecide {
          flat = [
            (clean "clean-a" { config.a = 1; })
            (clean "edited-c" { config.c = 3; })
          ];
          editedCount = 1;
          allOptions = allOptions4;
        }).footprint;
      expected = [
        {
          path = [ "c" ];
          reason = "edited-def";
        }
      ];
    };

    # Freeform flag (a): a CLEAN-only freeform contributor leaves reuse ON (clean freeform is byte-
    # identical); a DIRTY freeform contributor (undeclared `extra`) flips it OFF.
    test-freeform-clean-only-reuses = {
      expr =
        (warmDecide {
          flat = [
            (clean "clean-a" { config.a = 1; })
            (clean "clean-free" { config.extra = 9; })
          ];
          editedCount = 0;
          allOptions.a = opt;
        }).reuseAllFreeform;
      expected = true;
    };
    test-freeform-dirty-contributor-remerges = {
      expr =
        (warmDecide {
          flat = [
            (clean "clean-a" { config.a = 1; })
            (dirty "dirty-free" { config.extra = 9; })
          ];
          editedCount = 0;
          allOptions.a = opt;
        }).reuseAllFreeform;
      expected = false;
    };

    # Freeform flag (b): an EDITED freeformType candidate at EITHER site (top-level `freeformType` or
    # `_module.freeformType`) flips reuse OFF even with NO freeform def contribution.
    test-freeform-edited-toplevel-freeformtype = {
      expr =
        (warmDecide {
          flat = [
            (clean "clean-a" { config.a = 1; })
            (clean "edited-ff" { freeformType = t.lazyAttrsOf t.str; })
          ];
          editedCount = 1;
          allOptions.a = opt;
        }).reuseAllFreeform;
      expected = false;
    };
    test-freeform-edited-module-freeformtype = {
      expr =
        (warmDecide {
          flat = [
            (clean "clean-a" { config.a = 1; })
            (clean "edited-ffm" { _module.freeformType = t.lazyAttrsOf t.str; })
          ];
          editedCount = 1;
          allOptions.a = opt;
        }).reuseAllFreeform;
      expected = false;
    };

    # disabledModules on an EDITED entry ⇒ refuse warm (cold fallback). A non-edited disabledModules
    # does NOT refuse (only the edit can disable a clean base module invisibly to the footprint).
    test-disabled-modules-edited-refuses = {
      expr =
        (warmDecide {
          flat = [
            (clean "clean-a" { config.a = 1; })
            (clean "edited-dis" {
              disabledModules = [ "x" ];
              config.a = 1;
            })
          ];
          editedCount = 1;
          allOptions.a = opt;
        }).disabledRefusal;
      expected = true;
    };
    test-disabled-modules-nonedited-does-not-refuse = {
      expr =
        (warmDecide {
          flat = [
            (clean "base-dis" {
              disabledModules = [ "x" ];
              config.a = 1;
            })
            (clean "edited-b" { config.b = 2; })
          ];
          editedCount = 1;
          allOptions = allOptions4;
        }).disabledRefusal;
      expected = false;
    };

    # EDITED-tail identity: the engine flattens `editedModules` itself (imports included), and tail-k of
    # the FULL flatten equals the edited flatten — collectModules is concatMap, flatten distributes over
    # ++, the appended list is a strict suffix. An imports-carrying appended module flattens to
    # [ import…, own ] (imports BEFORE own content, nixpkgs order).
    test-edited-tail-identity-with-imports = {
      expr =
        let
          imp = {
            _file = "imp";
            config.b = 2;
          };
          base = [
            {
              _file = "base1";
              config.a = 1;
            }
          ];
          edited = [
            {
              _file = "edit";
              imports = [ imp ];
              config.c = 3;
            }
          ];
          files = ms: map (e: e._file) (collectModules idCallM ms);
        in
        {
          full = files (base ++ edited);
          editedFlat = files edited;
        };
      expected = {
        full = [
          "base1"
          "imp"
          "edit"
        ];
        editedFlat = [
          "imp"
          "edit"
        ];
      };
    };

    # ══ 2b — SPLICE EXECUTION + the byte oracle ═══════════════════════════════════════════════════

    # 1 — registry reuse: clean data modules (a, b) + a dirty module (reads config.a, defines c) + a
    # 1-module edit (forces a). Reusable locs (b) splice BYTE-equal; the dirty (c) and edited (a) locs
    # re-merge; the WHOLE result == cold. The decision proves the split actually happened (not a vacuous
    # cold-equal): b reused, a/c re-merged with their reasons.
    test-registry-reuse-whole-result-and-decision =
      let
        base = [
          {
            options.a = mkOption { type = t.str; };
            options.b = mkOption { type = t.str; };
            options.c = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
          }
          {
            _file = "cb";
            b = "bv";
          }
          (
            { config, ... }:
            {
              _file = "dirty";
              c = "c-${config.a}";
            }
          )
        ];
        edited = [
          {
            _file = "edit";
            a = mkForce "ea";
          }
        ];
        w = warmOf base edited;
      in
      {
        expr = {
          byte = byteOracle base edited;
          reused = w.warmDecision.reused;
          remergedA = w.warmDecision.remerged.a or null;
          remergedC = w.warmDecision.remerged.c or null;
          mode = w.warmDecision.mode;
        };
        expected = {
          byte = true;
          reused = [ "b" ];
          remergedA = "edited-def";
          remergedC = "dirty-def dirty";
          mode = "warm";
        };
      };

    # 2 — decl-side dirtiness: a dirty module DECLARES an option (b); its loc lands in the footprint and
    # re-merges (reason "dirty-decl <file>"), even though its value is unchanged. A clean leaf (c) still
    # reuses. Whole result == cold.
    test-decl-side-dirtiness =
      let
        base = [
          {
            options.a = mkOption { type = t.str; };
            options.c = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
            c = "cv";
          }
          (
            { config, ... }:
            {
              _file = "dirty-decl";
              options.b = mkOption {
                type = t.str;
                default = "bd";
              };
            }
          )
        ];
        edited = [
          {
            _file = "edit";
            a = mkForce "ea";
          }
        ];
        w = warmOf base edited;
      in
      {
        expr = {
          byte = byteOracle base edited;
          remergedB = w.warmDecision.remerged.b or null;
          reusedC = builtins.elem "c" w.warmDecision.reused;
        };
        expected = {
          byte = true;
          remergedB = "dirty-decl dirty-decl";
          reusedC = true;
        };
      };

    # 3 — freeform, three scenarios, each == cold:
    #   (a) clean-only freeform reuses the whole prev layer (edit touches a declared leaf only);
    #   (b) an EDITED module contributes a NEW freeform key ⇒ ALL freeform re-merges (teeth: reusing prev
    #       would DROP the new key);
    #   (c) an EDITED freeformType at EITHER site ⇒ ALL freeform re-merges (the flag is soundness-forced).
    test-freeform-clean-only-reuses-byte =
      let
        base = [
          {
            freeformType = t.lazyAttrsOf t.str;
            options.a = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
            extra = "ev";
          }
        ];
        edited = [
          {
            _file = "edit";
            a = mkForce "ea";
          }
        ];
      in
      {
        expr = byteOracle base edited;
        expected = true;
      };
    test-freeform-edited-new-key-remerges-byte =
      let
        base = [
          {
            freeformType = t.lazyAttrsOf t.str;
            options.a = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
            extra1 = "e1";
          }
        ];
        edited = [
          {
            _file = "edit-free";
            extra2 = "e2";
          }
        ];
        w = warmOf base edited;
      in
      {
        expr = {
          byte = byteOracle base edited;
          # teeth: the new freeform key IS present (freeform was re-merged, not stale-reused)
          hasNewKey = w.config.extra2 or null;
        };
        expected = {
          byte = true;
          hasNewKey = "e2";
        };
      };
    test-freeform-edited-toplevel-freeformtype-remerges-byte =
      let
        base = [
          {
            _module.freeformType = t.lazyAttrsOf t.str;
            options.a = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
            extra = "ev";
          }
        ];
        edited = [
          {
            _file = "edit-fft";
            freeformType = t.lazyAttrsOf t.anything;
          }
        ];
      in
      {
        expr = byteOracle base edited;
        expected = true;
      };
    test-freeform-edited-module-freeformtype-remerges-byte =
      let
        base = [
          {
            freeformType = t.lazyAttrsOf t.str;
            options.a = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
            extra = "ev";
          }
        ];
        edited = [
          {
            _file = "edit-ffm";
            _module.freeformType = mkForce (t.lazyAttrsOf t.anything);
          }
        ];
      in
      {
        expr = byteOracle base edited;
        expected = true;
      };

    # 4 — group-splice hazard: a declared UNTYPED group (grp, holding ONLY the declared leaf grp.x), and
    # the edit INTRODUCES a freeform key nested under it (grp.free), globally re-merging freeform. Prev
    # has NO grp.free, so a WHOLE-GROUP splice of `grp` would pin prev's `{ x = "xv"; }` and DROP the new
    # grp.free entirely. Leaf-granularity splicing (grp.x only) + freeform re-merge yields both — warm ==
    # cold, with the new freeform descendant present. This is the fixture the leaf-granularity rule exists
    # for (spec §2).
    test-group-splice-hazard =
      let
        base = [
          {
            options.grp.x = mkOption { type = t.str; };
            freeformType = t.lazyAttrsOf t.anything;
          }
          {
            _file = "cg";
            grp.x = "xv";
          }
        ];
        edited = [
          {
            _file = "edit";
            grp.free = "fnew";
          }
        ];
        w = warmOf base edited;
      in
      {
        expr = {
          byte = byteOracle base edited;
          freshFree = w.config.grp.free; # present via freeform re-merge (a whole-group splice DROPS it)
          reusedX = w.config.grp.x; # "xv" (leaf-spliced)
        };
        expected = {
          byte = true;
          freshFree = "fnew";
          reusedX = "xv";
        };
      };

    # 5a — adversarial SAFE: an UNMARKED `@`-capture module reads config.a and defines b; it is DIRTY by
    # default, so b re-merges and sees the edited config.a. warm == cold (the whole point of
    # dirty-by-default: an unmarked config reader is never stale-reused).
    test-adversarial-unmarked-capture-safe =
      let
        base = [
          {
            options.a = mkOption { type = t.str; };
            options.b = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
          }
          (
            args@{ config, ... }:
            {
              _file = "capture";
              b = "b-${config.a}";
            }
          )
        ];
        edited = [
          {
            _file = "edit";
            a = mkForce "ea";
          }
        ];
        w = warmOf base edited;
      in
      {
        expr = {
          byte = byteOracle base edited;
          b = w.config.b; # "b-ea" (re-merged against the edited config.a)
        };
        expected = {
          byte = true;
          b = "b-ea";
        };
      };

    # 5b — adversarial LYING marker (pins the DOCUMENTED failure mode, spec §5): a `pureModule`-marked
    # module that LIES — it `@`-captures config and reads config.a, violating the contract. It classifies
    # CLEAN, so its leaf (b) is stale-spliced from prev. The edit changes config.a, so warm.b ("b-av",
    # stale) DIVERGES from cold.b ("b-ea"). The divergence is asserted VISIBLE so the docs' warning stays
    # true — a lying marker is an author bug the standing tooth catches, not a silent-forever hazard.
    test-adversarial-lying-marker-diverges-visibly =
      let
        base = [
          {
            options.a = mkOption { type = t.str; };
            options.b = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
          }
          (pureModule (
            args@{ config, ... }:
            {
              _file = "liar";
              b = "b-${config.a}";
            }
          ))
        ];
        edited = [
          {
            _file = "edit";
            a = mkForce "ea";
          }
        ];
        w = warmOf base edited;
        c = coldOf (base ++ edited);
      in
      {
        expr = {
          warmB = w.config.b; # STALE — spliced from prev (config.a was "av")
          coldB = c.config.b; # FRESH — "b-ea"
          diverges = w.config.b != c.config.b;
        };
        expected = {
          warmB = "b-av";
          coldB = "b-ea";
          diverges = true;
        };
      };

    # 6 — disabledModules on an EDITED entry ⇒ warm REFUSED (cold fallback): the trace says mode=cold
    # with the reason, and the result is byte-identical to the full cold eval (nothing spliced).
    test-disabled-modules-cold-fallback =
      let
        base = [
          {
            options.a = mkOption { type = t.str; };
          }
          {
            _file = "ca";
            a = "av";
          }
        ];
        edited = [
          {
            _file = "edit-dis";
            disabledModules = [ "x" ];
            config.a = mkForce "ea";
          }
        ];
        w = warmOf base edited;
      in
      {
        expr = {
          byte = byteOracle base edited;
          mode = w.warmDecision.mode;
          reason = w.warmDecision.reason;
          reused = w.warmDecision.reused;
        };
        expected = {
          byte = true;
          mode = "cold";
          reason = "disabledModules on an edited module (warm refused)";
          reused = [ ];
        };
      };

    # 7 — chained warm: warmFrom = a WARM result, a second append. warm2 reuses warm1's own re-merged
    # locs; the whole result == cold of the twice-appended list.
    test-chained-warm =
      let
        base = [
          {
            options.a = mkOption { type = t.str; };
            options.b = mkOption { type = t.str; };
            options.c = mkOption {
              type = t.str;
              default = "cd";
            };
          }
          {
            _file = "ca";
            a = "av";
          }
          {
            _file = "cb";
            b = "bv";
          }
        ];
        edit1 = [
          {
            _file = "e1";
            b = mkForce "b1";
          }
        ];
        edit2 = [
          {
            _file = "e2";
            c = mkForce "c2";
          }
        ];
        warm1 = warmOf base edit1;
        warm2 = evalModuleTree {
          modules = base ++ edit1 ++ edit2;
          warmFrom = warm1;
          editedModules = edit2;
        };
        cold2 = coldOf (base ++ edit1 ++ edit2);
      in
      {
        expr = {
          config = jsonEq warm2.config cold2.config;
          provenance = jsonEq warm2.provenance cold2.provenance;
          # warm2 spliced a AND b from warm1 (b was warm1's own re-merge); only c re-merged.
          reused = warm2.warmDecision.reused;
        };
        expected = {
          config = true;
          provenance = true;
          reused = [
            "a"
            "b"
          ];
        };
      };

    # 8 — cold-path untouched: a plain eval (no warmFrom) reports mode=cold with an empty partition and
    # is byte-identical to itself (the 145 pre-warm tests running UNMODIFIED are the real gate; this
    # pins the always-present trace's cold shape).
    test-cold-path-trace-shape =
      let
        r = evalModuleTree {
          modules = [
            {
              options.a = mkOption { type = t.str; };
            }
            {
              _file = "m";
              a = "av";
            }
          ];
        };
      in
      {
        expr = {
          mode = r.warmDecision.mode;
          reason = r.warmDecision.reason;
          reused = r.warmDecision.reused;
          remerged = r.warmDecision.remerged;
          config = r.config;
        };
        expected = {
          mode = "cold";
          reason = "no warmFrom (cold)";
          reused = [ ];
          remerged = { };
          config = {
            a = "av";
          };
        };
      };
  };
}
