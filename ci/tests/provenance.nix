# Provenance channel (A2 design spec §1) — `evalModuleTree` result gains an always-on lazy
# `provenance` attr mirroring `config`'s loc structure. Per DECLARED-option loc a rich record
# ({ defs; winners; priority; defaulted }); per FREEFORM loc a REDUCED record ({ defs; winners=null;
# priority=null; defaulted=null }). This suite pins the record shapes AND the values-untouched tooth
# (forcing provenance disturbs nothing — the byte-parity of the value path is proven by the oracle +
# merge + core-kernel suites running UNMODIFIED). TDD-first; RED before the engine half lands.
{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm)
    evalModuleTree
    mkOption
    mkMerge
    mkIf
    mkForce
    mkCoreValue
    ;
  t = gm.types;
  prov = args: (evalModuleTree args).provenance;
in
{
  flake.tests.provenance = {
    # 1 — multi-def option, two files: `defs` lists every contributing def (reverse module order,
    # each with its discharged priority), `winners` the priority pass's kept defs, `priority` the
    # effective (default-override) priority. Two bare defs tie at 100 ⇒ both are winners.
    test-multidef-defs-winners-priority = {
      expr =
        (prov {
          modules = [
            { options.x = mkOption { type = t.str; }; }
            {
              _file = "A";
              x = "a";
            }
            {
              _file = "B";
              x = "b";
            }
          ];
        }).x;
      expected = {
        defs = [
          {
            file = "B";
            priority = 100;
          }
          {
            file = "A";
            priority = 100;
          }
        ];
        winners = [
          { file = "B"; }
          { file = "A"; }
        ];
        priority = 100;
        defaulted = false;
      };
    };

    # 2 — mkForce winner: `priority` collapses to 50, the winning def is the ONLY winner, and the
    # bare loser still appears in `defs` (the priority pass filters winners, it does not erase defs).
    test-mkforce-winner-loser-in-defs = {
      expr =
        (prov {
          modules = [
            { options.x = mkOption { type = t.str; }; }
            {
              _file = "A";
              x = "bare";
            }
            {
              _file = "B";
              x = mkForce "forced";
            }
          ];
        }).x;
      expected = {
        defs = [
          {
            file = "B";
            priority = 50;
          }
          {
            file = "A";
            priority = 100;
          }
        ];
        winners = [ { file = "B"; } ];
        priority = 50;
        defaulted = false;
      };
    };

    # 3 — default-only option: the synthetic `<default>` def is the sole def AND winner (priority
    # 1500), and `defaulted = true`.
    test-default-only-defaulted = {
      expr =
        (prov {
          modules = [
            {
              options.x = mkOption {
                type = t.str;
                default = "d";
              };
            }
          ];
        }).x;
      expected = {
        defs = [
          {
            file = "<default>";
            priority = 1500;
          }
        ];
        winners = [ { file = "<default>"; } ];
        priority = 1500;
        defaulted = true;
      };
    };

    # 4 — attribution THROUGH mkMerge/mkIf discharge: a property-wrapped def keeps its originating
    # file; a false-`mkIf` sub-def DROPS from a declared loc's `defs` (discharge resolves it to
    # nothing). The `mkForce "kept"` half survives at priority 50; the appended default rides at 1500.
    test-discharge-attribution = {
      expr =
        (prov {
          modules = [
            {
              options.x = mkOption {
                type = t.str;
                default = "d";
              };
            }
            {
              _file = "M";
              x = mkMerge [
                (mkIf false "dropped")
                (mkForce "kept")
              ];
            }
          ];
        }).x;
      expected = {
        defs = [
          {
            file = "M";
            priority = 50;
          }
          {
            file = "<default>";
            priority = 1500;
          }
        ];
        winners = [ { file = "M"; } ];
        priority = 50;
        defaulted = false;
      };
    };

    # 5 — freeform loc: a REDUCED record (defs present; winners/priority/defaulted all null). null
    # means "freeform / not observable", never "no override present".
    test-freeform-reduced-record = {
      expr =
        (prov {
          modules = [
            {
              freeformType = t.lazyAttrsOf t.str;
              options.known = mkOption {
                type = t.str;
                default = "k";
              };
            }
            {
              _file = "F";
              extra = "e";
            }
          ];
        }).extra;
      expected = {
        defs = [ { file = "F"; } ];
        winners = null;
        priority = null;
        defaulted = null;
      };
    };

    # 6 — nested-group loc: `options.a.b.c` puts the rich record at `provenance.a.b.c` (the tree
    # mirrors config's nested structure, assembled by the same recursive descent as `value`).
    test-nested-group-record = {
      expr =
        (prov {
          modules = [
            {
              options.a.b.c = mkOption {
                type = t.int;
                default = 1;
              };
            }
            {
              _file = "N";
              a.b.c = 7;
            }
          ];
        }).a.b.c;
      expected = {
        defs = [
          {
            file = "N";
            priority = 100;
          }
          {
            file = "<default>";
            priority = 1500;
          }
        ];
        winners = [ { file = "N"; } ];
        priority = 100;
        defaulted = false;
      };
    };

    # 7 — values-untouched tooth: deep-forcing the WHOLE provenance tree (declared + nested +
    # freeform) then reading `config` yields exactly the merged value. A provenance impl that forced
    # the wrong thunk, threw, or corrupted the value path would fail here (the oracle/merge/core
    # suites run UNMODIFIED for the full byte-parity guarantee).
    test-provenance-does-not-disturb-values = {
      expr =
        let
          r = evalModuleTree {
            modules = [
              {
                options.x = mkOption { type = t.str; };
                options.a.b.c = mkOption {
                  type = t.int;
                  default = 1;
                };
                freeformType = t.lazyAttrsOf t.str;
              }
              {
                _file = "A";
                x = mkForce "v";
                a.b.c = 9;
                extra = "e";
              }
            ];
          };
        in
        builtins.deepSeq r.provenance r.config;
      expected = {
        x = "v";
        a.b.c = 9;
        extra = "e";
      };
    };

    # 8 — coreShortCircuit: a sole fixed-input core def at a declared leaf short-circuits the spine;
    # the record is SYNTHESIZED from the marker (core def as sole def+winner at the bare priority,
    # defaulted=false) — the skip stays a skip, no spine re-run.
    test-core-synthesized-record = {
      expr =
        (evalModuleTree {
          coreShortCircuit = true;
          modules = [
            { options.z = mkOption { type = t.anything; }; }
            {
              _file = "C";
              z = mkCoreValue {
                digest = "d";
                values = {
                  real = 1;
                };
              };
            }
          ];
        }).provenance.z;
      expected = {
        defs = [
          {
            file = "C";
            priority = 100;
          }
        ];
        winners = [ { file = "C"; } ];
        priority = 100;
        defaulted = false;
      };
    };

    # 9 — declared and freeform records coexist in one provenance tree (the root assembly is
    # `recursiveUpdate freeformProv declaredProv`, declared winning at shared paths — mirroring
    # config's `recursiveUpdate freeform declared`).
    test-declared-and-freeform-coexist = {
      expr =
        let
          p = prov {
            modules = [
              {
                options.known = mkOption {
                  type = t.str;
                  default = "k";
                };
                freeformType = t.lazyAttrsOf t.str;
              }
              {
                _file = "F";
                known = "kv";
                extra = "e";
              }
            ];
          };
        in
        {
          knownDefaulted = p.known.defaulted;
          knownWinnerFile = (builtins.head p.known.winners).file;
          knownPriority = p.known.priority;
          extraDefs = p.extra.defs;
          extraPriority = p.extra.priority;
        };
      expected = {
        knownDefaulted = false;
        knownWinnerFile = "F";
        knownPriority = 100;
        extraDefs = [ { file = "F"; } ];
        extraPriority = null;
      };
    };
  };
}
