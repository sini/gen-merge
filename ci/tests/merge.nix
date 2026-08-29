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

  # ── freeform-selection fixtures (den-hoag-5r1a7) ───────────────────────────────────────────────
  # Shared by the cells near `test-freeformType-priority`. Each carries its own `_file` because the
  # refusal arm names every contributing file, and the value arm's cells read better against the
  # same vocabulary the refusal cells in ci/tests-error.nix use.
  ffSubA = {
    _file = "A";
    freeformType = t.attrsOf (
      t.submodule {
        options.a = mkOption {
          type = t.str;
          default = "a";
        };
      }
    );
  };
  ffSubB = {
    _file = "B";
    freeformType = t.attrsOf (
      t.submodule {
        options.b = mkOption {
          type = t.str;
          default = "b";
        };
      }
    );
  };
  ffSubC = {
    _file = "C";
    freeformType = t.attrsOf (
      t.submodule {
        options.c = mkOption {
          type = t.str;
          default = "c";
        };
      }
    );
  };
  ffStrA = {
    _file = "A";
    freeformType = t.attrsOf t.str;
  };
  ffUseK = {
    _file = "Z";
    config.k = { };
  };
  ffUseX = {
    _file = "Z";
    config.x = "s";
  };
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
    # nixpkgs' EMPTY-DEFINITION rule (modules.nix `mergeDefinitions`): with no surviving definition the
    # TYPE gets to supply a value before this is an error. A container nobody added to is legitimately
    # empty; a value nobody supplied is a mistake. `emptyValue` is what tells the two apart, and gen-merge
    # had it stubbed `{ }` on every type, so both arrived at the same throw.
    #
    # Two ways to arrive with nothing, and both reach the ONE `emptyValue` site in the fold: an option
    # never defined at all, and an option whose every definition was discharged away.
    test-emptyValue-mkIf-false-sole-def = {
      expr = cfg {
        modules = [
          {
            options.a = mkOption { type = t.attrsOf t.str; };
            options.l = mkOption { type = t.listOf t.str; };
            options.n = mkOption { type = t.nullOr t.str; };
            options.s = mkOption { type = t.submodule { }; };
          }
          {
            a = mkIf false { k = "v"; };
            l = mkIf false [ "x" ];
            n = mkIf false "x";
            s = mkIf false { };
          }
        ];
      };
      expected = {
        a = { };
        l = [ ];
        n = null;
        s = { };
      };
    };
    test-emptyValue-undefined-option = {
      expr = cfg {
        modules = [
          {
            options.a = mkOption { type = t.attrsOf t.str; };
            options.l = mkOption { type = t.listOf t.str; };
            options.n = mkOption { type = t.nullOr t.str; };
          }
        ];
      };
      expected = {
        a = { };
        l = [ ];
        n = null;
      };
    };
    # THE ARMING CONTROLS. The empty value must not swallow a real definition, must not swallow a
    # DEFAULT, and must not extend to a type that declares none — a leaf, `raw`, `anything`,
    # `deferredModule` and `either` all still throw, exactly as nixpkgs does.
    test-emptyValue-does-not-shadow-a-definition = {
      expr = cfg {
        modules = [
          {
            options.a = mkOption { type = t.attrsOf t.str; };
            options.l = mkOption { type = t.listOf t.str; };
            options.n = mkOption { type = t.nullOr t.str; };
          }
          {
            a.k = "v";
            l = [ "x" ];
            n = "x";
          }
        ];
      };
      expected = {
        a = {
          k = "v";
        };
        l = [ "x" ];
        n = "x";
      };
    };
    test-emptyValue-does-not-shadow-a-default = {
      expr = cfg {
        modules = [
          {
            options.a = mkOption {
              type = t.attrsOf t.str;
              default = {
                d = "fromDefault";
              };
            };
          }
        ];
      };
      expected = {
        a = {
          d = "fromDefault";
        };
      };
    };
    # Each type is probed on BOTH arrivals, because they are guarded by DIFFERENT code: an option never
    # defined short-circuits in the realizer, while an option whose every definition was discharged away
    # reaches the empty-value site inside the fold. Probing only the first leaves the second uncovered —
    # measured, not assumed: an empty-value rule that hands EVERY type a value passes an undefined-only
    # version of this test and still resolves a `mkIf false`-only `raw`/`anything`/`deferredModule`/
    # `either` to `{ }`. A leaf is the wrong sentinel for that break, since its `verify` rejects the
    # bogus value and hides it; `raw` and friends carry no verify and are what actually catch it.
    test-emptyValue-absent-on-types-that-declare-none = {
      expr =
        let
          resolves = e: (builtins.tryEval (builtins.deepSeq e null)).success;
          probe = ty: {
            undefined = resolves (cfg {
              modules = [ { options.x = mkOption { type = ty; }; } ];
            });
            discharged = resolves (cfg {
              modules = [
                { options.x = mkOption { type = ty; }; }
                { x = mkIf false "whatever"; }
              ];
            });
          };
        in
        builtins.mapAttrs (_: probe) {
          leaf = t.str;
          raw = t.raw;
          anything = t.anything;
          deferredModule = t.deferredModule;
          either = t.either t.str t.int;
          # control on the same instrument: an empty-able type resolves on BOTH arrivals, so a
          # uniformly-throwing engine cannot satisfy this row either.
          attrsOf = t.attrsOf t.str;
        };
      expected = {
        leaf = {
          undefined = false;
          discharged = false;
        };
        raw = {
          undefined = false;
          discharged = false;
        };
        anything = {
          undefined = false;
          discharged = false;
        };
        deferredModule = {
          undefined = false;
          discharged = false;
        };
        either = {
          undefined = false;
          discharged = false;
        };
        attrsOf = {
          undefined = true;
          discharged = true;
        };
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
  # ── freeform selection consults the type algebra (spec §2, den-hoag-5r1a7) ────────────────────
  # Two equal-priority `freeformType` contributions used to be resolved by `prelude.last`: one
  # declaration was destroyed, in every order, with `undeclared` still reading `[ ]`. They now fold
  # through `mergeTypes` — the same relation `redeclareDecl` runs one plane over.
  #
  # THE CELLS ASSERT THE WHOLE VALUE, NOT THAT THE EVAL SUCCEEDED. The old site succeeded and was
  # wrong, so a success-only cell passes the defect. Both orders are asserted because the old site
  # gave two DIFFERENT wrong answers (`{ k.b }` for `[A B]`, `{ k.a }` for `[B A]`), so a one-order
  # cell would only ever catch half of it.
  flake.tests.freeform.test-freeform-mergeable-pair-merges-in-both-orders = {
    expr = {
      ab = cfg {
        modules = [
          ffSubA
          ffSubB
          ffUseK
        ];
      };
      ba = cfg {
        modules = [
          ffSubB
          ffSubA
          ffUseK
        ];
      };
      # The loss report is now TRUTHFUL rather than merely quiet. It read `[ ]` while option `a` was
      # being destroyed, so on its own this literal discriminates nothing — it is asserted HERE,
      # beside the value it is a claim about, and not as a cell of its own.
      undeclared =
        (evalModuleTree {
          modules = [
            ffSubA
            ffSubB
            ffUseK
          ];
        }).undeclared;
    };
    expected = {
      ab = {
        k = {
          a = "a";
          b = "b";
        };
      };
      ba = {
        k = {
          a = "a";
          b = "b";
        };
      };
      undeclared = [ ];
    };
  };

  # A fold, not a pair: three contributions all survive. The old site kept only the last.
  flake.tests.freeform.test-freeform-mergeable-triple-folds = {
    expr = cfg {
      modules = [
        ffSubA
        ffSubB
        ffSubC
        ffUseK
      ];
    };
    expected = {
      k = {
        a = "a";
        b = "b";
        c = "c";
      };
    };
  };

  # ── controls for the above, live in the same run ──────────────────────────────────────────────
  # A SINGLE contribution attempts no merge and keeps its current identity — what catches a fold
  # that mishandles the singleton.
  flake.tests.freeform.test-control-freeform-single-contribution = {
    expr = cfg {
      modules = [
        ffStrA
        ffUseX
      ];
    };
    expected = {
      x = "s";
    };
  };

  # Two contributions at DISTINCT priorities still resolve BY PRIORITY. `filterOverrides` drops the
  # `mkDefault` before the fold sees it, so this is what fails if the fold is given `candidates`
  # instead of `winners` — a slip that would turn every priority-shadowed freeform type into a merge
  # partner and make `strict.nix`'s throw-on-unknown default refuse against a kind's own freeform.
  # It restates `test-freeformType-priority` above on this vocabulary; both must stay green.
  flake.tests.freeform.test-control-freeform-distinct-priorities-resolve-by-priority = {
    expr = cfg {
      modules = [
        ffStrA
        {
          _file = "B";
          config._module.freeformType = mkDefault (t.attrsOf t.int);
        }
        ffUseX
      ];
    };
    expected = {
      x = "s";
    };
  };

  # The `_module` feeder is collected PER MODULE, so the weaker contribution arriving LAST no longer
  # collapses over the stronger one before the priority pass runs. Under the old `recursiveUpdate`
  # feeder this fixture threw: `mkDefault (attrsOf int)` won the collapse and then rejected `"s"`.
  flake.tests.freeform.test-module-freeform-collected-per-module-not-collapsed = {
    expr = cfg {
      modules = [
        {
          _file = "A";
          config._module.freeformType = t.attrsOf t.str;
        }
        {
          _file = "B";
          config._module.freeformType = mkDefault (t.attrsOf t.int);
        }
        ffUseX
      ];
    };
    expected = {
      x = "s";
    };
  };

  flake.tests.freeform.test-mergeOneOption = {
    expr = genMerge.mergeOneOption [ "x" ] [ { value = "solo"; } ];
    expected = "solo";
  };

  # ── `anything`'s non-structural arm consults the leaf fold (den-hoag-1fu0a) ────────────────────
  # The arm ended `prelude.last vals` and now ends `mergeLeaf`. These are the VALUE half of that
  # oracle — the arms that must still produce a value — and they are the live controls for the
  # refusal cells in `ci/tests-error.nix`, which cannot state a value at all. Every one of them
  # passed against the OLD fold too, which is exactly what makes them controls rather than the test:
  # they are what fails if the refusal was bought by making the arm refuse too much.
  #
  # ★ THE STRUCTURAL ARMS ARE HERE BECAUSE THE REWRITE TOUCHED THEM. `loc` and `file` are now
  # threaded through the list and per-key recursion that used to run over bare values, so the arms
  # that were never the defect are the ones with a fresh way to break, and nothing else in the suite
  # exercises them.
  flake.tests.anything.test-control-anything-equal-definitions-merge = {
    expr = cfg {
      modules = [
        { options.o = mkOption { type = t.anything; }; }
        {
          _file = "A";
          o = "x";
        }
        {
          _file = "B";
          o = "x";
        }
      ];
    };
    expected = {
      o = "x";
    };
  };

  # Definitions at DISTINCT priorities still resolve BY PRIORITY: `filterOverrides` drops the loser
  # before the arm sees it, so exactly one winner reaches the fold and no agreement is demanded.
  # This is what fails if the refusal were placed above the priority pass instead of inside the fold.
  flake.tests.anything.test-control-anything-distinct-priorities-resolve-by-priority = {
    expr = cfg {
      modules = [
        { options.o = mkOption { type = t.anything; }; }
        {
          _file = "A";
          o = "x";
        }
        {
          _file = "B";
          o = mkForce "y";
        }
      ];
    };
    expected = {
      o = "y";
    };
  };

  # ★★ A STATED DIVERGENCE FROM THE FOREIGN PROTOCOL, ASSERTED RATHER THAN INHERITED
  # (den-hoag-1fu0a). nixpkgs' `anything` has NO list arm: `commonType` agrees on `"list"`, the
  # `mergeFunction` table has no entry for it, and it falls to `mergeEqualOption` — so `[ 1 ]` and
  # `[ 2 ]` are a REFUSAL there (measured at the pinned rev) and a CONCATENATION here. gen-merge's
  # divergence is declared in the type's own header ("lists concat") and is deliberate, but a
  # divergence with no cell is one nobody can find; this is the cell. It records WHAT IS and changes
  # nothing — the arm was left exactly as it was.
  #
  # ★ ITS RED IS ANY CHANGE TO THE LIST ARM, in either direction: adopting nixpkgs' refusal, or
  # folding lists some other way. A characterisation cell passes today by construction, so what
  # earns it its lines is that it is what goes red — deliberately — the day someone closes the
  # divergence, rather than the divergence closing unremarked.
  flake.tests.anything.test-list-definitions-concatenate-where-nixpkgs-refuses = {
    expr = cfg {
      modules = [
        { options.o = mkOption { type = t.anything; }; }
        {
          _file = "A";
          o = [ 1 ];
        }
        {
          _file = "B";
          o = [ 2 ];
        }
      ];
    };
    # Reverse module order, as everywhere else on the def path.
    expected = {
      o = [
        2
        1
      ];
    };
  };

  # The structural arms: all-list definitions concatenate, all-attrset definitions recurse per key,
  # and a key only one definition supplies passes through as the sole winner. The nested `same` key
  # is defined twice and EQUALLY — the descent's own agree-or-refuse, one level down, answering with
  # a value.
  flake.tests.anything.test-control-anything-structural-arms-fold = {
    expr = cfg {
      modules = [
        {
          options.l = mkOption { type = t.anything; };
          options.a = mkOption { type = t.anything; };
        }
        {
          _file = "A";
          l = [ 1 ];
          a = {
            onlyA = "a";
            deep.same = "s";
          };
        }
        {
          _file = "B";
          l = [ 2 ];
          a = {
            onlyB = "b";
            deep.same = "s";
          };
        }
      ];
    };
    expected = {
      # Reverse module order, as everywhere else on the def path.
      l = [
        2
        1
      ];
      a = {
        onlyA = "a";
        onlyB = "b";
        deep.same = "s";
      };
    };
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

  # `config._module.args` is READABLE INSIDE a module (nixpkgs parity: `config._module.args` resolves
  # in a module body; the returned `.config` stays `_module`-free). A module reads the WHOLE arg map —
  # which gen-schema's `mkInstanceType` and den's `resolvedCtxModule` rely on to enumerate entity args
  # dynamically (`config._module.args.${kind} = config` set on one side, read back on the other). The
  # RETURNED config never surfaces `_module`, so `cfg` sees only the declared surface.
  flake.tests.moduleArgs.test-module-args-readable-inside-module = {
    expr =
      (cfg {
        modules = [
          { config._module.args.host = "H"; }
          { config._module.args.user = "U"; }
          (
            { config, ... }:
            {
              options.seen = mkOption {
                type = t.attrsOf t.str;
                default = config._module.args;
              };
            }
          )
        ];
      }).seen;
    expected = {
      host = "H";
      user = "U";
    };
  };

  # The RETURNED config stays `_module`-free (nixpkgs strips it from `(evalModules).config`).
  flake.tests.moduleArgs.test-returned-config-has-no-module = {
    expr =
      (cfg {
        modules = [
          { config._module.args.host = "H"; }
          {
            options.out = mkOption {
              type = t.str;
              default = "o";
            };
          }
        ];
      }) ? _module;
    expected = false;
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

    # A UNION MERGES THROUGH THE MEMBER THAT ACCEPTS ITS DEFINITIONS, and the container members now
    # answer whether they do. Both container rows below were an INTERPRETER ABORT before that — a
    # LONE, unambiguously valid string definition, dispatched into the container member because the
    # container's inherited `check` accepted it, then handed to a merge that walks lists (`expected a
    # list but found a string: "b"`) or takes a key union (`expected a set but found a string: "b"`).
    # The leaf-first row is the ARMED CONTROL: it selected the right member before this rule and
    # still does, so a green table cannot come from the dispatch having stopped discriminating.
    test-either-dispatches-to-the-member-that-accepts-the-definition = {
      expr =
        let
          one =
            ty: v:
            cfg {
              modules = [
                { options.x = mkOption { type = ty; }; }
                { x = v; }
              ];
            };
        in
        {
          strIntoListFirst = (one (genMerge.either (genMerge.listOf t.str) t.str) "b").x;
          strIntoAttrsFirst = (one (genMerge.either (genMerge.attrsOf t.str) t.str) "b").x;
          listIntoListFirst = (one (genMerge.either (genMerge.listOf t.str) t.str) [ "a" ]).x;
          strIntoLeafFirst = (one (genMerge.either t.str genTypes.int) "b").x;
        };
      expected = {
        strIntoListFirst = "b";
        strIntoAttrsFirst = "b";
        listIntoListFirst = [ "a" ];
        strIntoLeafFirst = "b";
      };
    };

    # DEFINITIONS ONE MEMBER TAKES WHOLE MERGE THROUGH IT, unchanged — the compatibility obligation
    # on the rule above, pinned by VALUE rather than by "it evaluates". Two list definitions still
    # concatenate through the list member, in the same order and to the same bytes as before the
    # dispatch consulted every definition. The refusal these share a construction with is asserted in
    # ci/tests-error.nix `union-merge`, where a message is the only observable.
    test-either-homogeneous-defs-merge-unchanged = {
      expr = cfg {
        modules = [
          { options.x = mkOption { type = genMerge.either (genMerge.listOf t.str) t.str; }; }
          { x = [ "a" ]; }
          { x = [ "b" ]; }
        ];
      };
      expected = {
        x = [
          "b"
          "a"
        ];
      };
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
