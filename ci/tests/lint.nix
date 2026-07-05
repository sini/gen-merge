# Portable-subset lint suite (README "Portable-subset lint") — the byte-mode-boundary checker.
#
# Oracle (roadmap, binding):
#   • ACCEPT — `lint` returns `[]` on EVERY fixture of the shared parity corpus (`_fixtures/corpus.nix`,
#     the exact set oracle.nix proves byte-identical). If a corpus module were portable in name only,
#     an accept test here fails.
#   • REJECT — a dedicated fixture per unsupported construct produces exactly the expected finding
#     (kind + loc), pinned as a projected list so no extra/missing finding slips through. Negative
#     CONTROLS (a `config`-arg function, an `apply`-only re-declaration) prove each detector is
#     specific, not a blanket flag.
#
# `lint`/`mkOption`/`mkOptionType`/`types` come from gen-merge; the order-pass constructors do NOT
# (gen-merge omits the order pass), so this suite builds the `_type = "order"` marker directly — the
# exact shape nixpkgs `mkOrder`/`mkBefore`/`mkAfter` emit.
{ lib, genMerge, ... }:
let
  gm = genMerge;
  inherit (gm) lint mkOption mkOptionType;
  t = gm.types;

  # Constructor pack for the corpus fixtures (mirrors oracle.nix's `gmP`).
  gmP = {
    inherit (gm)
      mkOption
      mkMerge
      mkIf
      mkForce
      mkDefault
      ;
    inherit (gm) types;
  };
  fixtures = import ./_fixtures/corpus.nix;

  # Project a finding to its identity (kind + loc) — pins the assertion without the human `detail`.
  proj = map (f: {
    inherit (f) kind loc;
  });

  # nixpkgs order markers, built directly (gen-merge deliberately exports no `mkOrder`).
  mkOrder = priority: content: {
    _type = "order";
    inherit priority content;
  };
  mkAfter = mkOrder 1500;
  mkBefore = mkOrder 500;

  # A `functionTo`-named type record (gen-merge omits `functionTo`; `mkOptionType` is identity).
  functionToType = mkOptionType { name = "functionTo"; };

  # ── REJECT fixtures (one construct each) ───────────────────────────────────
  orderConfigMods = [
    {
      options.xs = mkOption {
        type = t.listOf t.str;
        default = [ ];
      };
    }
    { config.xs = mkAfter [ "z" ]; }
  ];
  orderDefaultMods = [
    {
      options.ys = mkOption {
        type = t.listOf t.str;
        default = mkBefore [ "a" ];
      };
    }
  ];
  optionsArgMods = [ ({ options, ... }: { }) ];
  typeMergeMods = [
    { options.a = mkOption { type = t.str; }; }
    { options.a = mkOption { type = t.int; }; }
  ];
  functionToMods = [ { options.guard = mkOption { type = functionToType; }; } ];
  nestedFunctionToMods = [ { options.guards = mkOption { type = t.listOf functionToType; }; } ];

  # ── negative CONTROLS (portable look-alikes) ───────────────────────────────
  # A `config`-arg function is NOT options-introspection.
  configArgMods = [ ({ config, ... }: { }) ];
  # A second module layering `apply` onto an earlier typed leaf carries NO type ⇒ NOT a typeMerge
  # reliance (this is exactly the gen-schema ref-binding field-union the engine relies on).
  applyRedeclareMods = [
    {
      options.a = mkOption {
        type = t.str;
        default = "x";
      };
    }
    { options.a = mkOption { apply = v: v; }; }
  ];

  # ── aggregation + ordering (functionTo, then order, then cross-module typeMerge) ──
  combinedMods = [
    { options.g = mkOption { type = functionToType; }; }
    { options.a = mkOption { type = t.str; }; }
    {
      options.a = mkOption { type = t.str; };
      config.c = mkAfter [ "z" ];
    }
  ];

  # An accept case NOT in the corpus: a `deferredModule` leaf must not be mistaken for `functionTo`.
  deferredMods = [
    {
      options.c = mkOption {
        type = t.deferredModule;
        default = { };
      };
    }
    {
      c = {
        x = 11;
      };
    }
  ];

  acceptTests = lib.mapAttrs' (name: fx: {
    name = "test-accept-${name}";
    value = {
      expr = lint { modules = fx gmP; };
      expected = [ ];
    };
  }) fixtures;
in
{
  flake.tests.lint = acceptTests // {
    # ACCEPT — extra portable shapes beyond the corpus.
    test-accept-empty = {
      expr = lint { modules = [ ]; };
      expected = [ ];
    };
    test-accept-deferred-not-function-to = {
      expr = lint { modules = deferredMods; };
      expected = [ ];
    };
    test-accept-config-arg-is-not-options-introspection = {
      expr = lint { modules = configArgMods; };
      expected = [ ];
    };
    test-accept-apply-redeclare-is-not-type-merge = {
      expr = lint { modules = applyRedeclareMods; };
      expected = [ ];
    };

    # REJECT — one construct per fixture, exact finding (kind + loc) pinned.
    test-reject-order-pass-in-config = {
      expr = proj (lint {
        modules = orderConfigMods;
      });
      expected = [
        {
          kind = "order-pass";
          loc = [ "xs" ];
        }
      ];
    };
    test-reject-order-pass-in-default = {
      expr = proj (lint {
        modules = orderDefaultMods;
      });
      expected = [
        {
          kind = "order-pass";
          loc = [ "ys" ];
        }
      ];
    };
    test-reject-options-introspection = {
      expr = proj (lint {
        modules = optionsArgMods;
      });
      expected = [
        {
          kind = "options-introspection";
          loc = [ ];
        }
      ];
    };
    test-reject-type-merge = {
      expr = proj (lint {
        modules = typeMergeMods;
      });
      expected = [
        {
          kind = "type-merge";
          loc = [ "a" ];
        }
      ];
    };
    test-reject-function-to = {
      expr = proj (lint {
        modules = functionToMods;
      });
      expected = [
        {
          kind = "function-to";
          loc = [ "guard" ];
        }
      ];
    };
    # functionTo nested under a structural type (listOf) — proves the recursive type walk.
    test-reject-function-to-nested = {
      expr = proj (lint {
        modules = nestedFunctionToMods;
      });
      expected = [
        {
          kind = "function-to";
          loc = [ "guards" ];
        }
      ];
    };

    # AGGREGATION — findings across modules, in a deterministic order (per-module, then typeMerge).
    test-reject-aggregates-in-order = {
      expr = proj (lint {
        modules = combinedMods;
      });
      expected = [
        {
          kind = "function-to";
          loc = [ "g" ];
        }
        {
          kind = "order-pass";
          loc = [ "c" ];
        }
        {
          kind = "type-merge";
          loc = [ "a" ];
        }
      ];
    };

    # SHAPE — a finding is a `{ detail; kind; loc }` attrset (attrNames sorted).
    test-finding-shape = {
      expr = builtins.attrNames (
        builtins.head (lint {
          modules = functionToMods;
        })
      );
      expected = [
        "detail"
        "kind"
        "loc"
      ];
    };
  };
}
