# Portable-subset lint suite (README "Portable-subset lint") — the byte-mode-boundary checker.
#
# Oracle (roadmap, binding):
#   • ACCEPT — `lint` returns `[]` on EVERY fixture of the shared parity corpus (`_fixtures/corpus.nix`,
#     the exact set oracle.nix proves byte-identical). If a corpus module were portable in name only,
#     an accept test here fails.
#   • REJECT — a dedicated fixture per unsupported construct produces exactly the expected finding
#     (kind + loc + file), pinned as a projected list so no extra/missing finding slips through.
#   • TOTALITY — the lint inherits the engine's forcing profile: it never forces what the engine would
#     not (mkIf-false-guarded throws drop; deep data-leaf payloads stay lazy). Pinned by deepSeq accept
#     tests that would THROW under the old plain-attrset walk.
#   • Negative CONTROLS (a `config`-arg function, an `apply`-only re-declaration) prove each detector is
#     specific, not a blanket flag.
#
# `lint`/`mkOption`/`mkOptionType`/`raw`/`types` come from gen-merge; the order-pass constructors do NOT
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

  # Project a finding to its identity (kind + loc + file) — pins the assertion without the human `detail`.
  proj = map (f: {
    inherit (f) kind loc file;
  });
  # Force the finding list fully, then return it — a lint that over-forces a portable input throws here.
  strict = r: builtins.deepSeq r r;

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
  # order markers at TWO declared leaves — deterministic sorted-key ordering (p before q).
  multiOrderMods = [
    {
      options.p = mkOption {
        type = t.listOf t.str;
        default = [ ];
      };
      options.q = mkOption {
        type = t.listOf t.str;
        default = [ ];
      };
    }
    {
      config.p = mkAfter [ "x" ];
      config.q = mkBefore [ "y" ];
    }
  ];
  # an order marker nested under mkMerge/mkIf-true — discharged the way the engine discharges.
  orderUnderMergeMods = [
    {
      options.xs = mkOption {
        type = t.listOf t.str;
        default = [ ];
      };
    }
    {
      config.xs = gm.mkMerge [
        (gm.mkIf true (mkAfter [ "z" ]))
      ];
    }
  ];
  optionsArgMods = [ ({ options, ... }: { }) ];
  typeMergeMods = [
    { options.a = mkOption { type = t.str; }; }
    { options.a = mkOption { type = t.int; }; }
  ];
  # the same loc declared with a type in THREE modules — one finding, file list of 3.
  typeMerge3Mods = [
    {
      _file = "m1.nix";
      options.a = mkOption { type = t.str; };
    }
    {
      _file = "m2.nix";
      options.a = mkOption { type = t.str; };
    }
    {
      _file = "m3.nix";
      options.a = mkOption { type = t.int; };
    }
  ];
  functionToMods = [ { options.guard = mkOption { type = functionToType; }; } ];
  nestedFunctionToMods = [ { options.guards = mkOption { type = t.listOf functionToType; }; } ];
  # a type nested deeper than the type-walk fuel (32) — undecidable ⇒ `unverifiable`, not silent-accept.
  deepType = lib.foldl' (acc: _: t.listOf acc) t.str (lib.range 1 40);
  unverifiableMods = [ { options.deep = mkOption { type = deepType; }; } ];
  # provenance: findings carry the declaring module's `_file`.
  provFunctionToMods = [
    {
      _file = "prov.nix";
      options.guard = mkOption { type = functionToType; };
    }
  ];

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

  # ── TOTALITY (MAJOR-1) — portable inputs the lint must NOT force into a throw ──
  # A data attrset at a raw leaf with a throwing DEEP field; the engine only forces to WHNF, so must lint.
  lazyDataLeafMods = [
    {
      options.z = mkOption {
        type = gm.raw;
        default = { };
      };
      options.keep = mkOption {
        type = gm.raw;
        default = 1;
      };
    }
    {
      config.z = {
        deep.marker = throw "descended-into-data-leaf";
      };
    }
  ];
  # `mkIf false { … }` discharges to nothing — its throwing content is never forced by the engine.
  mkIfFalseThrowMods = [
    {
      options.x = mkOption {
        type = gm.raw;
        default = "ok";
      };
    }
    { config = gm.mkIf false { x = throw "guard-never-taken"; }; }
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

    # TOTALITY — the lint inherits the engine's forcing profile (deepSeq would throw under a naive walk).
    test-accept-lazy-data-leaf-not-forced = {
      expr = strict (lint {
        modules = lazyDataLeafMods;
      });
      expected = [ ];
    };
    test-accept-mkif-false-guarded-throw-not-forced = {
      expr = strict (lint {
        modules = mkIfFalseThrowMods;
      });
      expected = [ ];
    };

    # REJECT — one construct per fixture, exact finding (kind + loc + file) pinned.
    test-reject-order-pass-in-config = {
      expr = proj (lint {
        modules = orderConfigMods;
      });
      expected = [
        {
          kind = "order-pass";
          loc = [ "xs" ];
          file = "<gen-merge>";
        }
      ];
    };
    # order markers at two leaves, deterministic sorted order.
    test-reject-order-pass-multi = {
      expr = proj (lint {
        modules = multiOrderMods;
      });
      expected = [
        {
          kind = "order-pass";
          loc = [ "p" ];
          file = "<gen-merge>";
        }
        {
          kind = "order-pass";
          loc = [ "q" ];
          file = "<gen-merge>";
        }
      ];
    };
    # order marker discharged out of mkMerge/mkIf-true (engine-faithful discharge).
    test-reject-order-pass-under-merge = {
      expr = proj (lint {
        modules = orderUnderMergeMods;
      });
      expected = [
        {
          kind = "order-pass";
          loc = [ "xs" ];
          file = "<gen-merge>";
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
          file = "<gen-merge>";
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
          file = [
            "<gen-merge>"
            "<gen-merge>"
          ];
        }
      ];
    };
    # count-3: one finding, file list of all three declaring modules.
    test-reject-type-merge-count-3 = {
      expr = proj (lint {
        modules = typeMerge3Mods;
      });
      expected = [
        {
          kind = "type-merge";
          loc = [ "a" ];
          file = [
            "m1.nix"
            "m2.nix"
            "m3.nix"
          ];
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
          file = "<gen-merge>";
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
          file = "<gen-merge>";
        }
      ];
    };
    # a type past the walk fuel is UNVERIFIABLE (fails toward reject, not silent-accept).
    test-reject-unverifiable-deep-type = {
      expr = proj (lint {
        modules = unverifiableMods;
      });
      expected = [
        {
          kind = "unverifiable";
          loc = [ "deep" ];
          file = "<gen-merge>";
        }
      ];
    };

    # PROVENANCE — findings carry the declaring module's `_file` (MAJOR-2).
    test-finding-file-provenance = {
      expr = proj (lint {
        modules = provFunctionToMods;
      });
      expected = [
        {
          kind = "function-to";
          loc = [ "guard" ];
          file = "prov.nix";
        }
      ];
    };

    # AGGREGATION — findings across modules, in a deterministic order (per-module, then order, then typeMerge).
    test-reject-aggregates-in-order = {
      expr = proj (lint {
        modules = combinedMods;
      });
      expected = [
        {
          kind = "function-to";
          loc = [ "g" ];
          file = "<gen-merge>";
        }
        {
          kind = "order-pass";
          loc = [ "c" ];
          file = "<gen-merge>";
        }
        {
          kind = "type-merge";
          loc = [ "a" ];
          file = [
            "<gen-merge>"
            "<gen-merge>"
          ];
        }
      ];
    };

    # SHAPE — a finding is a `{ detail; file; kind; loc }` attrset (attrNames sorted).
    test-finding-shape = {
      expr = builtins.attrNames (
        builtins.head (lint {
          modules = functionToMods;
        })
      );
      expected = [
        "detail"
        "file"
        "kind"
        "loc"
      ];
    };
  };
}
