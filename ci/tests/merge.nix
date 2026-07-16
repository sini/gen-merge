# The 7-item merge primitive (design spec §1) + the priority subset (§7). Pure — no nixpkgs.
{ genMerge, genTypes, ... }:
let
  inherit (genMerge)
    evalModuleTree
    mkOption
    mkOptionType
    mkMerge
    mkIf
    mkDefault
    mkForce
    submodule
    listOf
    attrsOf
    deferredModule
    ;
  t = genMerge.types;
  cfg = args: (evalModuleTree args).config;
in
{
  flake.tests.merge = {
    # (1) typed options + defaults
    test-default-used-when-undefined = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption {
              type = t.str;
              default = "d";
            };
          }
        ];
      };
      expected = {
        x = "d";
      };
    };
    test-def-overrides-default = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption {
              type = t.str;
              default = "d";
            };
          }
          { x = "v"; }
        ];
      };
      expected = {
        x = "v";
      };
    };
    test-apply-runs = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption {
              type = t.str;
              default = "d";
              apply = v: v + "!";
            };
          }
          { x = "v"; }
        ];
      };
      expected = {
        x = "v!";
      };
    };

    # priority subset (§7) — one min-priority-wins rule
    test-bare-beats-mkDefault = {
      expr = cfg {
        modules = [
          { options.x = mkOption { type = t.str; }; }
          { x = mkDefault "lo"; }
          { x = "hi"; }
        ];
      };
      expected = {
        x = "hi";
      };
    };
    test-mkForce-beats-bare = {
      expr = cfg {
        modules = [
          { options.x = mkOption { type = t.str; }; }
          { x = "bare"; }
          { x = mkForce "forced"; }
        ];
      };
      expected = {
        x = "forced";
      };
    };
    test-optionDefault-loses-to-mkDefault = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption {
              type = t.str;
              default = "optdef";
            };
          }
          { x = mkDefault "mkdef"; }
        ];
      };
      expected = {
        x = "mkdef";
      };
    };

    # A LOSING option default must never be forced. nixpkgs `dischargeProperties` leaves an
    # mkOverride's content lazy (priority resolved by `filterOverrides`, wrapper stripped only on
    # winners) so a default that would throw when evaluated is dropped, not forced. Regression: den's
    # host `intoAttr` default `{…}.${config.class}` throws for `class == "droid"`, but a real def
    # overrides it — the losing default must not be evaluated. `listOf` exercises the concat path too.
    test-throwing-optionDefault-not-forced-when-overridden = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption {
              type = t.listOf t.str;
              default = throw "LOSING_DEFAULT_FORCED";
            };
          }
          { x = [ "real" ]; }
        ];
      };
      expected = {
        x = [ "real" ];
      };
    };

    # combinators
    test-mkMerge = {
      expr = cfg {
        modules = [
          { options.x = mkOption { type = t.str; }; }
          { x = mkMerge [ "a" ]; }
        ];
      };
      expected = {
        x = "a";
      };
    };
    test-mkIf-false-drops = {
      expr = cfg {
        modules = [
          { options.x = mkOption { type = t.str; }; }
          { x = mkIf false "no"; }
          { x = "yes"; }
        ];
      };
      expected = {
        x = "yes";
      };
    };
    test-mkIf-attrset-pushdown = {
      expr = cfg {
        modules = [
          {
            options.a = mkOption {
              type = t.str;
              default = "da";
            };
            options.b = mkOption {
              type = t.str;
              default = "db";
            };
          }
          {
            config = mkIf true {
              a = "A";
              b = "B";
            };
          }
        ];
      };
      expected = {
        a = "A";
        b = "B";
      };
    };

    # (5) imports — own bare def overrides an imported mkDefault
    test-imports-own-overrides = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption { type = t.str; };
            imports = [ { x = mkDefault "imported"; } ];
            config.x = "own";
          }
        ];
      };
      expected = {
        x = "own";
      };
    };
    # equal-priority scalar defs conflict (byte-mode = nixpkgs mergeEqualOption)
    test-conflict-throws = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq (cfg {
            modules = [
              { options.x = mkOption { type = t.str; }; }
              { x = "a"; }
              { x = "b"; }
            ];
          }) null
        )).success;
      expected = false;
    };

    # listOf — REVERSE module-order concat (byte-identical to nixpkgs; see oracle suite)
    test-listOf-reverse-order = {
      expr = cfg {
        modules = [
          {
            options.xs = mkOption {
              type = listOf t.str;
              default = [ ];
            };
          }
          {
            xs = [
              "a"
              "b"
            ];
          }
          { xs = [ "c" ]; }
        ];
      };
      expected = {
        xs = [
          "c"
          "a"
          "b"
        ];
      };
    };

    # (2) freeform lazyAttrsOf — unknown keys routed
    test-freeform = {
      expr = cfg {
        modules = [
          {
            freeformType = t.lazyAttrsOf t.str;
            options.known = mkOption {
              type = t.str;
              default = "k";
            };
          }
          {
            unknown1 = "u1";
            unknown2 = "u2";
          }
        ];
      };
      expected = {
        known = "k";
        unknown1 = "u1";
        unknown2 = "u2";
      };
    };

    # (3)+(4) per-key name binding + self-referential config fixpoint
    test-name-and-selfref = {
      expr = cfg {
        modules = [
          {
            options.entries = mkOption {
              default = { };
              type = attrsOf (
                submodule (
                  { name, config, ... }:
                  {
                    config._module.args.self = config;
                    options.n = mkOption {
                      type = t.str;
                      default = name;
                    };
                    options.label = mkOption {
                      type = t.str;
                      default = "L-" + config.n;
                    };
                  }
                )
              );
            };
          }
          {
            entries.foo = { };
            entries.bar = {
              n = "custom";
            };
          }
        ];
      };
      expected = {
        entries = {
          foo = {
            n = "foo";
            label = "L-foo";
          };
          bar = {
            n = "custom";
            label = "L-custom";
          };
        };
      };
    };

    # (6) the (loc, defs) custom-merge escape hatch — defs in reverse module order
    test-custom-merge-hook = {
      expr = cfg {
        modules = [
          {
            options.c = mkOption {
              type = mkOptionType {
                name = "custom";
                merge = loc: defs: {
                  inherit loc;
                  vals = map (d: d.value) defs;
                };
              };
            };
          }
          { c = "one"; }
          { c = "two"; }
        ];
      };
      expected = {
        c = {
          loc = [ "c" ];
          vals = [
            "two"
            "one"
          ];
        };
      };
    };
  };

  # nixpkgs-parity introspection — structural types expose `nestedTypes.elemType` so a consumer's
  # type-tree walker (gen-schema's mkCoerceChain reads `t.nestedTypes.elemType`) recurses unchanged.
  flake.tests.introspection = {
    test-listOf-nestedTypes = {
      expr = (listOf t.str).nestedTypes.elemType.name;
      expected = "string";
    };
    test-attrsOf-nestedTypes = {
      expr = (attrsOf t.str).nestedTypes.elemType.name;
      expected = "string";
    };
    # the recursive walk gen-schema does: listOf (attrsOf str) → down two levels
    test-nested-walk = {
      expr = (listOf (attrsOf t.str)).nestedTypes.elemType.nestedTypes.elemType.name;
      expected = "string";
    };
  };

  # freeformType is priority-resolved (nixpkgs treats it as an option). A `_module.freeformType =
  # mkDefault throwType` (the strict/closed-world default, gen-schema strict.nix) must YIELD to a
  # kind's own bare top-level freeformType.
  flake.tests.freeform.test-freeformType-priority = {
    expr = cfg {
      modules = [
        {
          _module.freeformType = mkDefault (mkOptionType {
            name = "strict";
            merge = loc: _defs: throw "STRICT: unexpected key at ${genMerge.showOption loc}";
          });
        }
        { freeformType = genMerge.types.lazyAttrsOf t.str; }
        { anything = "goes"; }
      ];
    };
    expected = {
      anything = "goes";
    };
  };
  flake.tests.freeform.test-mergeOneOption = {
    expr = genMerge.mergeOneOption [ "x" ] [ { value = "solo"; } ];
    expected = "solo";
  };

  # `_module` is a CONFIG path, not a structural marker: a top-level `{ _module.args.x = y; }` in a
  # config-shorthand module must still be collected, and a downstream module reads the injected arg.
  # (Regression guard — gen-schema strict/instance emit top-level `_module.freeformType`.)
  flake.tests.moduleArgs.test-toplevel-module-shorthand = {
    expr = cfg {
      modules = [
        { options.out = mkOption { type = t.str; }; }
        { _module.args.injected = "HELLO"; }
        (
          { injected, ... }:
          {
            out = injected;
          }
        )
      ];
    };
    expected = {
      out = "HELLO";
    };
  };

  # nullOr / either / oneOf — merge-aware type combinators (gen-schema ref/union fields).
  flake.tests.combinators = {
    test-nullOr-null = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption {
              type = genMerge.nullOr t.str;
              default = null;
            };
          }
        ];
      };
      expected = {
        x = null;
      };
    };
    test-nullOr-value = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption {
              type = genMerge.nullOr t.str;
              default = null;
            };
          }
          { x = "v"; }
        ];
      };
      expected = {
        x = "v";
      };
    };
    test-nullOr-verifies = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq (cfg {
            modules = [
              { options.x = mkOption { type = genMerge.nullOr genTypes.int; }; }
              { x = "not-int"; }
            ];
          }) null
        )).success;
      expected = false;
    };
    test-either-left = {
      expr = cfg {
        modules = [
          { options.x = mkOption { type = genMerge.either t.str genTypes.int; }; }
          { x = "s"; }
        ];
      };
      expected = {
        x = "s";
      };
    };
    test-either-right = {
      expr = cfg {
        modules = [
          { options.x = mkOption { type = genMerge.either t.str genTypes.int; }; }
          { x = 42; }
        ];
      };
      expected = {
        x = 42;
      };
    };
    test-oneOf = {
      expr = cfg {
        modules = [
          {
            options.x = mkOption {
              type = genMerge.oneOf [
                t.str
                genTypes.int
                genTypes.bool
              ];
            };
          }
          { x = true; }
        ];
      };
      expected = {
        x = true;
      };
    };
    test-nullOr-nestedTypes = {
      expr = (genMerge.nullOr t.str).nestedTypes.elemType.name;
      expected = "string";
    };
  };

  # (7) deferredModule is NEVER forced by composition — reading the merged value's structure must
  # not force a throwing class body.
  flake.tests.deferred.test-not-forced = {
    expr =
      let
        r = cfg {
          modules = [
            {
              options.d = mkOption {
                type = deferredModule;
                default = { };
              };
            }
            {
              d = {
                boom = throw "FORCED-CLASS-CONTENT";
              };
            }
          ];
        };
      in
      builtins.isList r.d.imports && builtins.length r.d.imports == 1;
    expected = true;
  };

  # type checking is gen-types' job — a leaf type error throws at the merged leaf (§4 boundary)
  flake.tests.checking.test-verify-throws = {
    expr =
      (builtins.tryEval (
        builtins.deepSeq (cfg {
          modules = [
            { options.n = mkOption { type = genTypes.int; }; }
            { n = "not-an-int"; }
          ];
        }) null
      )).success;
    expected = false;
  };
  flake.tests.checking.test-verify-passes = {
    expr = cfg {
      modules = [
        {
          options.n = mkOption {
            type = genTypes.int;
            default = 0;
          };
        }
        { n = 7; }
      ];
    };
    expected = {
      n = 7;
    };
  };
}
