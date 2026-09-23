# The undeclared-def report — `evalModuleTree` result gains an always-on lazy `undeclared` attr
# listing the definitions the eval did not merge into `config`.
#
# WHY: an unmatched def has three dispositions and no fourth — a `freeformType` absorbs it, `check`
# refuses it, or neither, in which case it is not merged at all. The third is the only one that
# returns neither a value nor a named refusal, and it is why this channel exists — but the channel is
# not scoped to it: every unmatched def the freeform plane did not absorb is listed, the REFUSED ones
# included (cell 8). The report is a SIBLING of `config`: `check = false` exists so that the merged
# value does NOT grow the undeclared key, so a report placed inside `config` would change what the flag
# produces instead of describing it. `check` therefore does not gate the report (checking and
# visibility are different questions) while the freeform plane gates this level's OWN definitions
# (there the defs are merged, and nothing was dropped). A nested tree's findings are never absorbed,
# so they are reported under every regime (cells 16-19).
{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption;
  t = gm.types;

  declared = {
    options.declared = mkOption {
      type = t.str;
      default = "d";
    };
  };
  report = args: (evalModuleTree args).undeclared;

  # Does forcing `e` whole succeed? Cells 11-15 are about WHAT THE CHANNEL FORCES, so they read a
  # success/failure bit rather than a value: the defect they pin turns a readable sibling into a throw.
  forces = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  # Cells 16-19: a lax nested tree (`check = false`), a definition of it carrying the undeclared key
  # `z`, and a freeform parent declaring it as `nest`.
  laxNest =
    (evalModuleTree {
      check = false;
      modules = [
        {
          options.a = mkOption { type = t.str; };
          options.id_hash = mkOption {
            type = t.str;
            default = "nest:0";
          };
        }
      ];
    }).type;
  laxNestDropping = {
    a = "declared";
    z = "dropped";
  };
  freeformNestDecl = {
    _module.freeformType = t.lazyAttrsOf t.anything;
    options.nest = mkOption { type = laxNest; };
  };
in
{
  flake.tests.undeclared = {
    # 1 — one record per DEF, not per key: two files defining the same undeclared name are both
    # named. Order mirrors `provenance.defs` — per key (`attrNames` order), reverse module order.
    test-reports-every-dropped-def-with-its-file = {
      expr = report {
        modules = [
          declared
          {
            _file = "A";
            config.orphan = "a";
          }
          {
            _file = "B";
            config.orphan = "b";
            config.other = "x";
          }
        ];
        check = false;
      };
      expected = [
        {
          file = "B";
          path = [ "orphan" ];
        }
        {
          file = "A";
          path = [ "orphan" ];
        }
        {
          file = "B";
          path = [ "other" ];
        }
      ];
    };

    # 2 — the report does not change what `check = false` produces: `config` carries the declared key
    # and nothing else, exactly as before the channel existed. The consumer contract (a downstream
    # caller reads the merged config and asserts it empty for an all-undeclared input) rests on this.
    test-report-stays-out-of-config = {
      expr =
        builtins.attrNames
          (evalModuleTree {
            modules = [
              declared
              { config.orphan = "a"; }
            ];
            check = false;
          }).config;
      expected = [ "declared" ];
    };

    # 3 — paths are absolute and multi-segment: an undeclared key under a DECLARED group is captured
    # at its own level (the orphan check is per level, not root-only), so the record names `grp.unknown`.
    test-nested-path-under-declared-group = {
      expr = report {
        modules = [
          {
            _file = "G";
            options.grp.known = mkOption {
              type = t.str;
              default = "k";
            };
            config.grp.unknown = "deep";
          }
        ];
        check = false;
      };
      expected = [
        {
          file = "G";
          path = [
            "grp"
            "unknown"
          ];
        }
      ];
    };

    # 4 — the capture path is the FIRST undeclared name on the branch, and the record covers that loc
    # with everything beneath it. Deeper rendering has no well-defined answer: with no declaration,
    # `config.nested.deep.key = "X"` and `config.nested = { deep.key = "X"; }` are the same def, so a
    # descent cannot tell a dropped option path from a dropped attrset VALUE.
    test-capture-is-the-first-undeclared-name = {
      expr = report {
        modules = [
          declared
          {
            _file = "N";
            config.nested.deep.key = "X";
          }
        ];
        check = false;
      };
      expected = [
        {
          file = "N";
          path = [ "nested" ];
        }
      ];
    };

    # 5 — `prefix` is honoured, so a record names the same location the refusal message would.
    test-paths-are-absolute-against-prefix = {
      expr = report {
        modules = [
          {
            _file = "P";
            config.orphan = "p";
          }
        ];
        check = false;
        prefix = [ "sub" ];
      };
      expected = [
        {
          file = "P";
          path = [
            "sub"
            "orphan"
          ];
        }
      ];
    };

    # 6 — ARMED CONTROL for the freeform gate: with a `freeformType` the key is ABSORBED into config
    # and the report says nothing. Without this the channel would fire on every freeform config, where
    # no definition was dropped at all.
    test-freeform-absorbs-and-reports-nothing = {
      expr =
        let
          r = evalModuleTree {
            modules = [
              declared
              { freeformType = t.lazyAttrsOf t.str; }
              {
                _file = "F";
                config.orphan = "a";
              }
            ];
            check = false;
          };
        in
        {
          configKeys = builtins.attrNames r.config;
          undeclared = r.undeclared;
        };
      expected = {
        configKeys = [
          "declared"
          "orphan"
        ];
        undeclared = [ ];
      };
    };

    # 7 — CONTROL against a channel that reports everything: a fully declared config yields an EMPTY
    # list, not a missing field and not a spurious record.
    test-fully-declared-reports-empty = {
      expr = report {
        modules = [
          declared
          { config.declared = "set"; }
        ];
        check = false;
      };
      expected = [ ];
    };

    # 8 — the report is not a substitute for the refusal: the same input under `check = true` still
    # throws at `config`. Live control in the same cell — `check = false` on that input evaluates.
    # And the report's extension is `check`-INDEPENDENT: under `check = true` the refused def is still
    # listed (the throw lives on `config`, not on the report). Without that assertion a later change
    # gating the report on `check` would redden no cell.
    test-check-true-still-refuses = {
      expr =
        let
          mods = [
            declared
            {
              _file = "C";
              config.orphan = "a";
            }
          ];
          ev =
            check:
            evalModuleTree {
              modules = mods;
              inherit check;
            };
          force = check: (builtins.tryEval (builtins.deepSeq (ev check).config null)).success;
        in
        {
          checkTrue = force true;
          checkFalse = force false;
          checkTrueReport = (ev true).undeclared;
        };
      expected = {
        checkTrue = false;
        checkFalse = true;
        checkTrueReport = [
          {
            file = "C";
            path = [ "orphan" ];
          }
        ];
      };
    };

    # 9 — reading the report forces no def VALUE: it carries names and files only. The bomb is live —
    # the control absorbs the same def through a freeformType, where forcing config does abort.
    test-report-does-not-force-values = {
      expr =
        let
          bomb = {
            _file = "X";
            config.orphan = throw "BOOM";
          };
          reportOk =
            (builtins.tryEval (
              builtins.deepSeq
                (evalModuleTree {
                  modules = [
                    declared
                    bomb
                  ];
                  check = false;
                }).undeclared
                null
            )).success;
          absorbedAborts =
            (builtins.tryEval (
              builtins.deepSeq
                (evalModuleTree {
                  modules = [
                    declared
                    { freeformType = t.lazyAttrsOf t.str; }
                    bomb
                  ];
                  check = false;
                }).config
                null
            )).success;
        in
        {
          inherit reportOk absorbedAborts;
        };
      expected = {
        reportOk = true;
        absorbedAborts = false;
      };
    };

    # 10 — the channel reaches gen-merge's OWN nesting seam too: an option typed with another
    # `evalModuleTree` call's `.type` directly (not `t.submodule`, which W6 refuses to mount by
    # name) is this engine talking to itself, and ADR-0025 item 1 does not carve out an exception
    # for that boundary — a def dropped one level down is reported at its full path, same as any
    # other undeclared def, and `.config` stays exactly what it was before this channel existed.
    # Live control, same cell: a mirrored fixture supplies the identical undeclared key at the
    # KIND'S OWN top level, where cell 1 already covers this discipline — proving the assertion
    # below exercises the nested seam specifically, not just re-confirming the top-level behaviour.
    test-nested-tree-as-type-leaf-reports-its-own-orphan =
      let
        innerType =
          (evalModuleTree {
            modules = [
              {
                options.known = mkOption {
                  type = t.str;
                  default = "k";
                };
              }
            ];
            check = false;
          }).type;
        r = evalModuleTree {
          modules = [
            {
              options.nest = mkOption {
                type = innerType;
                default = { };
              };
            }
            {
              _file = "C";
              config.nest = {
                known = "k2";
                bogus = "B";
              };
            }
          ];
          check = false;
        };
        control = report {
          modules = [
            declared
            {
              _file = "C";
              config.bogus = "B";
            }
          ];
          check = false;
        };
      in
      {
        expr = {
          undeclared = r.undeclared;
          config = r.config;
          inherit control;
        };
        expected = {
          undeclared = [
            {
              file = "C";
              path = [
                "nest"
                "bogus"
              ];
            }
          ];
          config = {
            nest = {
              known = "k2";
            };
          };
          control = [
            {
              file = "C";
              path = [ "bogus" ];
            }
          ];
        };
      };

    # 11 — THE REPORT DESCRIBES THE EVAL, IT DOES NOT CHANGE ITS EVALUATION ORDER. Every binding that
    # walks `realized.unmatched`'s spine forces each declared leaf's contribution to it, so a leaf
    # channel that reaches its answer THROUGH the merge forces every leaf's merge — and this engine's
    # contract is the opposite ("lazily (undefined+no-default throws only on access, matching
    # nixpkgs)", the comment above `realized`). Declared-and-never-defined with no default is the
    # supported shape that pays: the value arrives afterwards by `//` and the option is never read.
    # LIVE CONTROL, same cell: reading the undefined option ITSELF still throws. Without it this cell
    # also passes on an engine that has stopped refusing undefined options altogether.
    test-undeclared-report-does-not-force-an-undefined-sibling =
      let
        r = evalModuleTree {
          check = true;
          modules = [
            {
              options.defined = mkOption { type = t.str; };
              options.never = mkOption { type = t.str; };
              config.defined = "ok";
            }
          ];
        };
      in
      {
        expr = {
          siblingReadIsLazy = forces r.config.defined;
          undefinedThrowsOnAccess = !(forces r.config.never);
        };
        expected = {
          siblingReadIsLazy = true;
          undefinedThrowsOnAccess = true;
        };
      };

    # 12 — the same forcing point, reached through the OTHER message class: a `readOnly` option
    # defined twice has its arbiter (`mergeOptionWith`'s `_ro`) inside the merge, so forcing an
    # unrelated leaf's merge fires a read-only refusal nobody asked for.
    # LIVE CONTROL, same cell: the arbiter is un-forced, never removed — reading `locked` itself
    # still refuses.
    test-undeclared-report-does-not-force-a-readonly-arbiter =
      let
        r = evalModuleTree {
          check = true;
          modules = [
            {
              options.locked = mkOption {
                type = t.str;
                readOnly = true;
              };
              options.other = mkOption { type = t.str; };
              config.other = "ok";
            }
            { config.locked = "a"; }
            { config.locked = "b"; }
          ];
        };
      in
      {
        expr = {
          unrelatedReadIsLazy = forces r.config.other;
          readOnlyStillRefuses = !(forces r.config.locked);
        };
        expected = {
          unrelatedReadIsLazy = true;
          readOnlyStillRefuses = true;
        };
      };

    # 13 — THE FREEFORM REGIME'S READERS. At `check = false` UNDER a `freeformType`, `_orphanCheck`
    # is `null` twice over, yet `freeformConfigCold`'s branch condition
    # (`freeform == null || realized.unmatched == [ ]`) walks `realized.unmatched`'s spine, because `||`
    # evaluates its right operand when the left is false. Since the channel split, that spine holds
    # definitions only (no leaf contributes to it), so an eager LEAF decision no longer reaches this
    # cell: the leaf-channel forcing point is pinned by cells 11-12, which walk `realized.reported`
    # through the report. This cell pins that the freeform plane's own walk stays
    # off every declared sibling.
    # LIVE CONTROLS, same cell: `never` still throws on access, and `loose` proves the freeform plane
    # really absorbed an unmatched key here — so the reading above is taken over a tree whose
    # `realized.unmatched` had something in it to force, not one where there was nothing.
    test-undeclared-report-does-not-force-a-sibling-under-a-freeformtype =
      let
        r = evalModuleTree {
          check = false;
          modules = [
            {
              _module.freeformType = t.lazyAttrsOf t.str;
              options.defined = mkOption { type = t.str; };
              options.never = mkOption { type = t.str; };
              config.defined = "ok";
              config.loose = "absorbed";
            }
          ];
        };
      in
      {
        expr = {
          freeformSiblingLazy = forces r.config.defined;
          freeformUndefinedStillThrows = !(forces r.config.never);
          absorbed = r.config.loose or "ABSENT";
        };
        expected = {
          freeformSiblingLazy = true;
          freeformUndefinedStillThrows = true;
          absorbed = "absorbed";
        };
      };

    # 14 — ★ THE ARM DISCRIMINATOR, and the reason the fix is a HOISTED PREDICATE rather than a
    # structural-only `unmatched`. A nested tree at `check = false` typed into a parent at
    # `check = true` does NOT refuse on its own `check`: it refuses only because the parent's leaf
    # channel hands it the parent's strictness (`mergeDefs.reported strict`, the owner's `inherited`
    # arm of `_orphanCheck`). Every construction that takes the leaf channel out
    # of the refusal predicate greens cells 11-13 and loses this refusal silently; deciding the leaf's
    # contribution from its DECLARATION keeps both.
    # LIVE CONTROL, same cell: the report still names the dropped key, so a green here is the refusal
    # firing and not the report having been silenced along with it.
    test-a-lax-nested-tree-is-still-refused-by-a-strict-parent =
      let
        innerLax = evalModuleTree {
          check = false;
          modules = [ { options.a = mkOption { type = t.str; }; } ];
        };
        r = evalModuleTree {
          check = true;
          modules = [
            {
              options.nest = mkOption { type = innerLax.type; };
              config.nest = {
                a = "declared";
                z = "dropped";
              };
            }
          ];
        };
      in
      {
        expr = {
          laxNestedRefusedByParent = !(forces r.config);
          laxNestedReport = map (u: u.path) r.undeclared;
        };
        expected = {
          laxNestedRefusedByParent = true;
          laxNestedReport = [
            [
              "nest"
              "z"
            ]
          ];
        };
      };

    # 15 — A FORWARD PIN, NOT AN ARM DISCRIMINATOR. The guard reads `opts.${k}.type`, so a leaf whose
    # `type` is an EXPRESSION derived from this eval's own `config` reads that config while the
    # leaf's findings are decided. The bare form reads its value at `check = true`
    # (`test-a-config-derived-bare-leaf-type-reads-at-check`, ci/tests/bare-site.nix), since no
    # level walks a nested tree's findings on its own WHNF. This cell pins the `attrsOf` wrapper,
    # which reaches WHNF without forcing its element type, so the documented self-referential
    # registry idiom evaluates. It separates no arm; it pins the wrapper shape against a FUTURE
    # edit that makes a config-derived type recurse again, which is the only thing it is here to do.
    test-a-config-derived-leaf-type-is-a-declared-divergence =
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
                type = t.attrsOf (if r.config.kindName == "igloo" then t.str else t.int);
                default = { };
              };
              options.plain = mkOption { type = t.str; };
              config.plain = "ok";
            }
          ];
        };
      in
      {
        expr = {
          wrappedSelfRefSiblingLazy = forces r.config.plain;
          wrappedSelfRefValueReadable = forces r.config.registry;
          wrappedSelfRefKindName = r.config.kindName;
        };
        expected = {
          wrappedSelfRefSiblingLazy = true;
          wrappedSelfRefValueReadable = true;
          wrappedSelfRefKindName = "igloo";
        };
      };

    # 16 — A NESTED TREE'S FINDING UNDER A `freeformType`: REPORTED, NEVER ABSORBED. The finding
    # `nest.z` has an associated option (`nest`), so it is outside the freeform type's domain
    # (nixpkgs: "merge all definitions that don't have an associated option"; `lib.evalModules` on
    # this shape gives `nest`'s keys `[ "a" ]`). Absorbing it would graft `z` into a declared option's
    # value; dropping it silently is the third disposition. So `nest` keeps its type's merge, and the
    # report names the finding with the freeform plane active. `loose` is this level's own undeclared
    # key, which the freeform plane DOES absorb and the report therefore does not list.
    # LIVE CONTROL, same cell: the same tree with no dropped key reports nothing.
    test-a-nested-finding-under-a-freeformtype-is-reported-and-not-absorbed =
      let
        read = r: {
          nestKeys = builtins.attrNames r.config.nest;
          loose = r.config.loose or "ABSENT";
          report = map (u: u.path) r.undeclared;
        };
        ff = nestDef: {
          check = false;
          modules = [
            freeformNestDecl
            {
              _file = "C";
              config.nest = nestDef;
              config.loose = "absorbed";
            }
          ];
        };
      in
      {
        expr = {
          dropped = read (evalModuleTree (ff laxNestDropping));
          control = read (
            evalModuleTree (ff {
              a = "declared";
            })
          );
        };
        expected = {
          dropped = {
            nestKeys = [
              "a"
              "id_hash"
            ];
            loose = "absorbed";
            report = [
              [
                "nest"
                "z"
              ]
            ];
          };
          control = {
            nestKeys = [
              "a"
              "id_hash"
            ];
            loose = "absorbed";
            report = [ ];
          };
        };
      };

    # 17 — AND REFUSED AT `check = true`, WHATEVER `freeformType` IS. The report↔refusal
    # correspondence ("whatever `check = true` refuses, `check = false` reports") fixes the refusal
    # gate as `check` alone. The refusal is catchable (a named `throw`, not an interpreter error), and
    # the report still names the finding while `config` refuses.
    test-a-nested-finding-under-a-freeformtype-is-refused-at-check =
      let
        r = evalModuleTree {
          check = true;
          modules = [
            freeformNestDecl
            {
              _file = "C";
              config.nest = laxNestDropping;
            }
          ];
        };
      in
      {
        expr = {
          refused = !(forces r.config);
          report = map (u: u.path) r.undeclared;
        };
        expected = {
          refused = true;
          report = [
            [
              "nest"
              "z"
            ]
          ];
        };
      };

    # 18 — EACH KIND IN ONE FRAME. This level's own undeclared key is RELATIVE to `prefix` and is
    # prefixed once; a nested tree's finding is already ABSOLUTE (the nested eval ran at
    # `prefix = abs`) and is appended as is. At `prefix = [ ]` the frames coincide, so only a
    # non-empty prefix can see a finding prefixed twice.
    test-a-nested-finding-is-absolute-and-not-prefixed-twice = {
      expr =
        map (u: u.path)
          (evalModuleTree {
            check = false;
            prefix = [ "sub" ];
            modules = [
              { options.nest = mkOption { type = laxNest; }; }
              {
                _file = "C";
                config.nest = laxNestDropping;
                config.orphan = "o";
              }
            ];
          }).undeclared;
      expected = [
        [
          "sub"
          "orphan"
        ]
        [
          "sub"
          "nest"
          "z"
        ]
      ];
    };

    # 19 — TWO NESTING LEVELS AT `prefix = [ ]`: the finding climbs two moduleTree boundaries and is
    # named once, `a.b.z`. LIVE CONTROL, same cell: `.config` is the two declared keys only.
    test-a-finding-two-nesting-levels-down-is-named-once =
      let
        middle =
          (evalModuleTree {
            check = false;
            modules = [ { options.b = mkOption { type = laxNest; }; } ];
          }).type;
        r = evalModuleTree {
          check = false;
          modules = [
            { options.a = mkOption { type = middle; }; }
            {
              _file = "C";
              config.a.b = laxNestDropping;
            }
          ];
        };
      in
      {
        expr = {
          report = map (u: u.path) r.undeclared;
          inherit (r) config;
        };
        expected = {
          report = [
            [
              "a"
              "b"
              "z"
            ]
          ];
          config = {
            a.b = {
              a = "declared";
              id_hash = "nest:0";
            };
          };
        };
      };
  };
}
