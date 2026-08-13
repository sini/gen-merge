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
# visibility are different questions) while the freeform plane does (there the defs are merged, and
# nothing was dropped).
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
    # and nothing else, exactly as before the channel existed. The consumer contract (gen-flake reads
    # the merged config and asserts it empty for an all-undeclared input) rests on this.
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
  };
}
