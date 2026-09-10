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

  # ══ region 2 fixtures — a warm re-compose that MOVES a minted identity ═════════════════════════
  #
  # gen-schema is not an input here and cannot be: it depends on this library. So the identity SHAPE
  # is reproduced rather than imported — `id_hash` is `"<kind>:<digest>"` over the declared,
  # non-internal `str` options, reflected from inside the fixpoint exactly the way the real stamp did
  # before its key set closed. The shape is all this engine ever sees of an identity, and it is the
  # whole of what the predicate reads.
  idOf =
    kind:
    (
      { config, options, ... }:
      {
        options.id_hash = mkOption { type = t.str; };
        config.id_hash =
          let
            # BOTH spellings, for the reason the real predicate carries both: gen-types names a
            # string "string" and nixpkgs `lib.types` names the same primitive "str". A fixture
            # matching only one of them selects NOTHING here, and an identity over no keys is a
            # CONSTANT — every arm agrees, the refusal correctly finds nothing moved, and the cell
            # reads green while measuring an engine that was never exercised.
            keys = builtins.filter (
              k:
              k != "id_hash"
              && builtins.elem (options.${k}.type.name or "") [
                "str"
                "string"
              ]
              && !(options.${k}.internal or false)
            ) (builtins.attrNames options);
          in
          "${kind}:" + builtins.hashString "sha256" (builtins.toJSON (map (k: config.${k}) keys));
      }
    );

  # FLAT — the instance IS the config root, so its `id_hash` is a declared leaf of this very tree and
  # a declaration-path predicate could in principle see it. This is the arm that shape reaches.
  flatBase = [
    (idOf "host")
    {
      options.name = mkOption { type = t.str; };
      options.role = mkOption { type = t.str; };
    }
    {
      _file = "flat-base";
      config.name = "igloo";
      config.role = "web";
    }
  ];
  # The two arms differ in ONE token. Both are decl-side contributions and both make the base module
  # dirty; only the first is an identity key, which is the whole discrimination.
  plantLive = [
    {
      _file = "plant";
      options.grommet = mkOption {
        type = t.str;
        default = "plain";
      };
    }
  ];
  plantInert = [
    {
      _file = "plant";
      options.grommet = mkOption {
        type = t.str;
        default = "plain";
        internal = true;
      };
    }
  ];

  # REGISTRY — the instances live BELOW a declared leaf. `declLeafEntries` stops at `isOptLeaf`, so
  # `options.hosts` is the leaf and no instance's `id_hash` is a path in `allOptions` at all. This is
  # the arm a declaration-path predicate cannot serve, and the reason the fact is a per-instance map.
  hostSub = t.submodule {
    imports = [
      (idOf "thimble")
      {
        options.spool = mkOption {
          type = t.str;
          default = "";
        };
        # NOT an identity key — an `int`, so it is a field an edit can move without moving anything
        # minted. It is what the arming arm edits.
        options.tally = mkOption {
          type = t.int;
          default = 0;
        };
      }
    ];
  };
  regBase = [
    {
      options.hosts = mkOption {
        type = t.attrsOf hostSub;
        default = { };
      };
    }
    {
      _file = "reg-base";
      config.hosts.pewter.spool = "silk";
      config.hosts.damask.spool = "linen";
    }
  ];
  regMoves = [
    {
      _file = "reg-edit";
      config.hosts.pewter.spool = mkForce "satin";
    }
  ];
  regHolds = [
    {
      _file = "reg-edit";
      config.hosts.pewter.tally = mkForce 7;
    }
  ];
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
        # `mkForce`, matching the `_module`-side twin below. The subject here is warm re-merge BYTE
        # IDENTITY, so the edit has to REPLACE the base freeformType rather than compete with it:
        # `lazyAttrsOf anything` and `lazyAttrsOf str` do not merge, and at equal priority the pair
        # is a conflict, not an edit. It used to be written bare and leaned on the freeform plane's
        # last-wins selection to do the replacing — which is the defect `den-hoag-5r1a7` removed, so
        # the intent is now stated in the fixture instead of being supplied by the engine. The old
        # shape is still asserted, as a refusal, by the cell below.
        edited = [
          {
            _file = "edit-fft";
            freeformType = mkForce (t.lazyAttrsOf t.anything);
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

    # ══ region 2 — THE ARMING ARMS ════════════════════════════════════════════════════════════════
    #
    # These are the cells that make the two refusals below mean something. A construction that
    # refused every decl-side contribution, or every warm re-compose at all, would satisfy both
    # refusals and fail here — and it would destroy reuse for every consumer of this engine while
    # doing it. The predicate has to see an identity MOVE, not an edit.

    # The same option as the live plant, carrying `internal = true`. It is still a decl-side
    # contribution and still makes the base module dirty, so `id_hash` is re-merged for a
    # declaration-side reason and comes back with the SAME value. Warm, no reason, no refusal.
    test-identity-inert-option-still-recomposes-warm =
      let
        w = warmOf flatBase plantInert;
      in
      {
        expr = {
          mode = w.warmDecision.mode;
          reason = w.warmDecision.reason;
          idHashHeld = w.config.id_hash == (coldOf flatBase).config.id_hash;
          remergedForADeclSideReason = w.warmDecision.remerged ? id_hash;
        };
        expected = {
          mode = "warm";
          reason = null;
          idHashHeld = true;
          remergedForADeclSideReason = true;
        };
      };

    # The registry arming arm, and the GRANULARITY FACT in the same cell. The edit moves a declared
    # field of `hosts.pewter` that is not an identity key: `hosts` is re-merged, nothing minted
    # moves, and warm serves the result. `remerged` names the declared LEAF and carries no `id_hash`
    # key on this shape at all — which is why the fact this engine hands the plane is a per-instance
    # identity map and not a set of declaration paths.
    test-registry-non-identity-edit-recomposes-warm =
      let
        w = warmOf regBase regHolds;
        c = coldOf regBase;
      in
      {
        expr = {
          mode = w.warmDecision.mode;
          reason = w.warmDecision.reason;
          remergedKeys = builtins.attrNames w.warmDecision.remerged;
          remergedNamesNoIdentity = w.warmDecision.remerged ? id_hash;
          pewterHeld = w.config.hosts.pewter.id_hash == c.config.hosts.pewter.id_hash;
          damaskHeld = w.config.hosts.damask.id_hash == c.config.hosts.damask.id_hash;
          editLanded = w.config.hosts.pewter.tally;
        };
        expected = {
          mode = "warm";
          reason = null;
          remergedKeys = [ "hosts" ];
          remergedNamesNoIdentity = false;
          pewterHeld = true;
          damaskHeld = true;
          editLanded = 7;
        };
      };
  };

  # THE OTHER HALF OF `test-freeform-edited-toplevel-freeformtype-remerges-byte`, AND THE ONLY WARM
  # CELL THAT STATES THIS. Both freeformType-edit cells above now `mkForce` their edit, so nothing on
  # the warm path would otherwise say what happens when a warm edit contributes a freeformType at the
  # SAME priority as the base's: the contributions compete, `lazyAttrsOf anything` and `lazyAttrsOf
  # str` do not merge, and the eval refuses by name. That is the shape the top-level cell used to
  # carry, where the freeform plane's last-wins selection silently discarded one of the two and the
  # byte oracle read `true` over a destroyed declaration (den-hoag-5r1a7). It was found by that cell
  # FLIPPING rather than by any oracle, which is why it is written down instead of left for the next
  # person to rediscover.
  #
  # The MESSAGE is asserted, not a bare throw: the reason names both element types, the file list
  # names both contributors, and `<gen-merge>` is the base module's `_file` fallback — it declares
  # none, which is exactly what an author hitting this needs told.
  #
  # ★ IT IS ON THE `testsError` PLANE THOUGH IT LIVES IN THIS FILE, and that is forced rather than
  # stylistic. `mkCi`'s `checks.default` asserter quantifies over `flake.tests` and evaluates every
  # cell's `expr` UNCONDITIONALLY, so a throwing `expr` CRASHES that gate instead of failing it —
  # measured here, not assumed: with this cell on `flake.tests.warm`, `nix flake check ./ci` died
  # carrying this refusal (exit 1), against exit 0 and "all checks passed!" on the same tree without
  # it. `ci/tests-error.nix`'s header states the same rule; the plane is the fix, the file is not.
  flake.testsError.warm = {
    test-freeform-edited-toplevel-freeformtype-at-equal-priority-refuses =
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
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the freeform type is defined with types that do not merge \\(`lazyAttrsOf' over `anything' and `lazyAttrsOf' over `string', whose element types do not merge\\); defined in edit-fft, <gen-merge>$";
        };
      };

    # ══ region 2 — THE REFUSAL, on both module shapes ═════════════════════════════════════════════
    #
    # A warm re-compose whose minted identity moved does not fall back to cold and does not populate
    # `reason`. Cold emits the SAME moved identity — the move is a property of the module set, not of
    # the reuse path — so there is no degraded arm that is correct and the plane throws instead.
    #
    # The MESSAGE is asserted rather than a bare throw, and each thing it names is load-bearing: the
    # COORDINATE is what the caller has to go look at, the KIND says which registry moved under it,
    # BOTH identities let a caller diff against whatever it pinned, and the re-merged declarations
    # are the contributing side in this engine's own vocabulary. A refusal that said only "an
    # identity moved" would send its reader back to a full diff of two configs.

    # FLAT — the moved instance is the config root, so its coordinate is the empty path.
    test-identity-move-on-a-flat-warm-recompose-refuses-by-name = {
      expr = (warmOf flatBase plantLive).config.id_hash;
      expectedError = {
        type = "ThrownError";
        msg = "^gen-memo\\.identitiesHeld: minted identity moved on a warm re-compose at '' \\(kind 'host', was 'host:[0-9a-f]{64}', now 'host:[0-9a-f]{64}', re-merged declarations: .*, 1 instance\\(s\\) moved\\)$";
      };
    };

    # REGISTRY — the moved instance is below a declared leaf, which is the shape `remerged` cannot
    # name. The coordinate is the instance's, and it is the one the arming arm above proves this
    # predicate does NOT produce for an edit that moves nothing minted.
    test-identity-move-on-a-registry-warm-recompose-refuses-by-name = {
      expr = (warmOf regBase regMoves).config.hosts.pewter.id_hash;
      expectedError = {
        type = "ThrownError";
        msg = "^gen-memo\\.identitiesHeld: minted identity moved on a warm re-compose at 'hosts\\.pewter' \\(kind 'thimble', was 'thimble:[0-9a-f]{64}', now 'thimble:[0-9a-f]{64}', re-merged declarations: hosts, 1 instance\\(s\\) moved\\)$";
      };
    };
  };
}
