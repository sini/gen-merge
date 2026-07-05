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
  };
}
