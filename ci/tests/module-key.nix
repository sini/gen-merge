# `_module.<x>` — THE VALUES (den-hoag-lnleu). nixpkgs declares four `_module` options; this engine
# reads `args` and `freeformType`, takes `specialArgs` at `evalModuleTree`'s door, honours `check` as
# the option it is, at this level only, and meets every other sub-key in the realizer as an ordinary
# config path (`moduleDefOf`). Its refusals
# are `ci/tests-error.nix`'s `refusal-messages` group; here, what a `freeformType` absorbs, what a
# declared `options._module.<x>` merges, that warm agrees with cold, and the controls that read the
# same before and after. Each expected value is nixpkgs' on the same input.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption;
  t = gm.types;

  decl = {
    options.x = mkOption { default = "dflt"; };
  };
  ff = t.lazyAttrsOf t.raw;
  reader =
    f:
    { config, ... }:
    {
      options.r = mkOption { };
      config.r = f config;
    };
  readPkgs =
    { pkgs, ... }:
    {
      options.r = mkOption { };
      config.r = pkgs;
    };
  cfgOf = modules: (evalModuleTree { } modules).config;
  # A child at `n.k`, reading its `name`, under an `apply` that rewrites it.
  readName =
    { name, ... }:
    {
      options.v = mkOption { default = name; };
    };
  renameApply.options._module.args = mkOption { apply = a: a // { name = "Q"; }; };
  childTree = modules: (evalModuleTree { } modules).type;
  nestedName =
    child:
    (cfgOf [
      {
        options.n = mkOption {
          type = t.attrsOf child;
          default = { };
        };
        config.n.k = { };
      }
    ]).n.k.v;
  names = modules: builtins.attrNames (cfgOf modules);
  # An evaluation beside an undeclared `y`: what it reports, and what its `config` carries.
  checkRead =
    args: modules:
    let
      r = evalModuleTree args (
        [
          decl
          { y = 1; }
        ]
        ++ modules
      );
    in
    {
      und = map (u: u.path) r.undeclared;
      names = builtins.attrNames r.config;
    };

  # V7, V8: a base evaluation, the same set plus one edited module warm from it, and the cold control.
  warmCold =
    base: edit:
    let
      prev = evalModuleTree { } base;
      warm = evalModuleTree {
        warmFrom = prev;
        editedModules = [ edit ];
      } (base ++ [ edit ]);
      cold = evalModuleTree { } (base ++ [ edit ]);
    in
    {
      warm = warm.config.r;
      cold = cold.config.r;
      mode = warm.warmDecision.mode;
    };
in
{
  flake.tests.module-key = {
    # A `freeformType` absorbs `_module.bogus` as it absorbs any undeclared key, and a module reads
    # it back; the returned `config` stays `_module`-free.
    test-a-freeformtype-absorbs-a-module-unknown-key = {
      expr =
        let
          c = cfgOf [
            decl
            {
              config._module.bogus = 1;
              config._module.freeformType = ff;
            }
            (reader (c: c._module.bogus or "ABSENT"))
          ];
        in
        {
          inherit (c) r;
          names = builtins.attrNames c;
        };
      expected = {
        r = 1;
        names = [
          "r"
          "x"
        ];
      };
    };
    # `freeformType` under a property is pushed down, as `args` is.
    test-a-freeformtype-under-mkif-absorbs = {
      expr = names [
        decl
        { y = 1; }
        { config._module = gm.mkIf true { freeformType = ff; }; }
      ];
      expected = [
        "x"
        "y"
      ];
    };
    # A declared `options._module.foo` merges as a declared option, readable by a module, and never
    # leaks into the returned `config`.
    test-a-declared-module-sub-option-merges = {
      expr =
        (cfgOf [
          decl
          {
            options._module.foo = mkOption { };
            config._module.foo = 1;
          }
          (reader (c: c._module.foo or "ABSENT"))
        ]).r;
      expected = 1;
    };
    test-a-declared-module-sub-option-stays-out-of-the-returned-config = {
      expr = names [
        decl
        {
          options._module.foo = mkOption { };
          config._module.foo = 1;
        }
      ];
      expected = [ "x" ];
    };
    # Warm agrees with cold: an edited module adding an absorbed `_module.bogus` refuses the
    # freeform-layer reuse, and a declared `_module` leaf never splices from prev's `_module`-free
    # `config`.
    test-warm-agrees-with-cold-on-an-absorbed-module-key = {
      expr = warmCold [
        decl
        { config._module.freeformType = ff; }
        (reader (c: c._module.bogus or "ABSENT"))
      ] { config._module.bogus = 1; };
      expected = {
        warm = 1;
        cold = 1;
        mode = "warm";
      };
    };
    test-warm-agrees-with-cold-on-a-declared-module-sub-option = {
      expr = warmCold [
        decl
        {
          options._module.foo = mkOption { };
          config._module.foo = 1;
        }
        (reader (c: c._module.foo or "ABSENT"))
      ] { config.x = "edited"; };
      expected = {
        warm = 1;
        cold = 1;
        mode = "warm";
      };
    };
    # An unknown `_module.<x>` is no lint finding: both engines refuse it under `check` and absorb it
    # under a `freeformType`. Live control, same instrument: an `mkAfter` definition is one.
    test-a-module-unknown-key-is-not-a-lint-finding = {
      expr =
        let
          lint =
            m:
            gm.lint [
              decl
              m
            ];
        in
        {
          bogus = lint { config._module.bogus = 1; };
          control = builtins.length (lint {
            config.x = gm.mkAfter "a";
          });
        };
      expected = {
        bogus = [ ];
        control = 1;
      };
    };

    # `_module.check` IS HONOURED AT THIS LEVEL ONLY (H′). It is an option of the evaluation's own
    # `_module` group: a module's value merges with priorities over the door's `mkDefault`, decides
    # this level's refusal of an undeclared key, and a nested tree keeps the door's strictness
    # (`test-a-lax-nested-tree-is-still-refused-by-a-strict-parent`). Each value is nixpkgs'.
    test-a-module-check-false-lists-an-undeclared-key = {
      expr = checkRead { } [ { config._module.check = false; } ];
      expected = {
        und = [ [ "y" ] ];
        names = [ "x" ];
      };
    };
    test-a-shorthand-module-check-false-lists-an-undeclared-key = {
      expr = checkRead { } [ { _module.check = false; } ];
      expected = {
        und = [ [ "y" ] ];
        names = [ "x" ];
      };
    };
    test-a-forced-module-check-false-lists-an-undeclared-key = {
      expr = checkRead { } [ { config._module.check = gm.mkForce false; } ];
      expected = {
        und = [ [ "y" ] ];
        names = [ "x" ];
      };
    };
    test-a-module-check-under-mkif-false-changes-nothing = {
      expr = names [
        decl
        { config._module = gm.mkIf false { check = false; }; }
      ];
      expected = [ "x" ];
    };
    # computed from `config`: modules read this level's unchecked merge, so the read is no cycle
    test-a-module-check-computed-from-config-lists-an-undeclared-key = {
      expr = checkRead { } [
        { options.flag = mkOption { default = false; }; }
        ({ config, ... }: { config._module.check = config.flag; })
      ];
      expected = {
        und = [ [ "y" ] ];
        names = [
          "flag"
          "x"
        ];
      };
    };
    # the door's `check` is a `mkDefault`, so a weaker module definition yields to it
    test-a-module-check-weaker-than-the-callers-yields-to-it = {
      expr = checkRead { check = false; } [ { config._module.check = gm.mkOverride 1200 true; } ];
      expected = {
        und = [ [ "y" ] ];
        names = [ "x" ];
      };
    };
    # a check computed from a lax nested tree's value, under a caller's `false`: a value, the nested
    # finding reported
    test-a-module-check-from-a-lax-nested-value-under-a-caller-false-reports-it = {
      expr =
        map (u: u.path)
          (evalModuleTree { check = false; } [
            decl
            {
              options.nest = mkOption {
                type = (evalModuleTree { check = false; } [ { options.a = mkOption { type = t.str; }; } ]).type;
              };
              config.nest = {
                a = "declared";
                z = "dropped";
              };
            }
            ({ config, ... }: { config._module.check = config.nest.a == "declared"; })
          ]).undeclared;
      expected = [
        [
          "nest"
          "z"
        ]
      ];
    };
    # Both engines honour it, so it is no lint finding. Live control, same instrument: `mkAfter`.
    test-a-module-check-is-not-a-lint-finding = {
      expr = {
        check = gm.lint [
          decl
          { config._module.check = false; }
        ];
        control = builtins.length (
          gm.lint [
            decl
            { config.x = gm.mkAfter "a"; }
          ]
        );
      };
      expected = {
        check = [ ];
        control = 1;
      };
    };
    # An edited `_module.check` refuses warm: the prior's `config` carries the prior's refusal, so a
    # reused leaf would refuse here where cold lists `y`.
    test-warm-is-refused-when-an-edited-module-sets-check = {
      expr =
        let
          base = [
            decl
            { y = 1; }
            (reader (c: c.x))
          ];
          edit = {
            config._module.check = false;
          };
          warm = evalModuleTree {
            warmFrom = evalModuleTree { } base;
            editedModules = [ edit ];
          } (base ++ [ edit ]);
        in
        {
          r = warm.config.r;
          inherit (warm.warmDecision) mode reason;
        };
      expected = {
        r = "dflt";
        mode = "cold";
        reason = "_module.check on an edited module (warm refused)";
      };
    };
    # CONTROLS: what reads the same before and after.
    test-control-module-args-read = {
      expr =
        (cfgOf [
          decl
          { config._module.args.pkgs = "P"; }
          readPkgs
        ]).r;
      expected = "P";
    };
    test-control-module-args-under-mkif-read = {
      expr =
        (cfgOf [
          decl
          { config._module = gm.mkIf true { args.pkgs = "P"; }; }
          readPkgs
        ]).r;
      expected = "P";
    };
    test-control-freeformtype-absorbs = {
      expr = names [
        decl
        { y = 1; }
        { config._module.freeformType = ff; }
      ];
      expected = [
        "x"
        "y"
      ];
    };
    test-control-caller-check-false-lists-an-undeclared-key = {
      expr =
        map (u: u.path)
          (evalModuleTree { check = false; } [
            decl
            { y = 1; }
          ]).undeclared;
      expected = [ [ "y" ] ];
    };
    test-control-empty-module-attrset = {
      expr = names [
        decl
        { config._module = { }; }
      ];
      expected = [ "x" ];
    };
    test-control-plain-module = {
      expr = names [ decl ];
      expected = [ "x" ];
    };
    # A `submodule`-typed `options._module` takes every `_module.<x>` the engine does not own, as
    # nixpkgs' submodule does once its own `_module` options are merged into it; `args` is still the
    # engine's, so both reads give nixpkgs' `[ 2 "P" ]`.
    test-a-submodule-typed-module-option-takes-the-rest = {
      expr =
        (cfgOf [
          decl
          {
            options._module = mkOption {
              type = t.submodule { options.foo = mkOption { default = 1; }; };
              default = { };
            };
            config._module.foo = 2;
            config._module.args.pkgs = "P";
          }
          (
            { config, pkgs, ... }:
            {
              options.r = mkOption { };
              config.r = [
                config._module.foo
                pkgs
              ];
            }
          )
        ]).r;
      expected = [
        2
        "P"
      ];
    };
    test-a-submodule-typed-module-option-reads-its-default = {
      expr =
        (cfgOf [
          decl
          {
            options._module = mkOption {
              type = t.submodule { options.foo = mkOption { default = 1; }; };
              default = { };
            };
          }
          (reader (c: c._module.foo))
        ]).r;
      expected = 1;
    };
    # An engine-owned `_module.<k>` re-declared where nixpkgs' `mergeOptionDecls` accepts it: its own
    # type with an `example` changes nothing, and an `apply` maps the merged value, as nixpkgs' does.
    test-an-owned-key-redeclared-with-its-own-type-changes-nothing = {
      expr =
        (cfgOf [
          decl
          {
            options._module.args = mkOption {
              type = t.lazyAttrsOf t.raw;
              example = { };
            };
            config._module.args.pkgs = "P";
          }
          readPkgs
        ]).r;
      expected = "P";
    };
    test-an-owned-key-redeclared-with-an-apply-maps-the-merged-set = {
      expr =
        (cfgOf [
          decl
          {
            options._module.args = mkOption { apply = a: a // { pkgs = "Q"; }; };
            config._module.args.pkgs = "P";
          }
          readPkgs
        ]).r;
      expected = "Q";
    };
    test-a-freeformtype-redeclared-with-an-apply-absorbs = {
      expr = names [
        decl
        { options._module.freeformType = mkOption { apply = _: ff; }; }
        { y = 1; }
      ];
      expected = [
        "x"
        "y"
      ];
    };
    # An `apply` on `args` declared inside a `submodule`-typed `_module` leaf maps the merged set, as
    # nixpkgs' does once it merges its own `_module` options into the leaf.
    test-an-owned-key-apply-inside-a-submodule-leaf-maps-the-merged-set = {
      expr =
        (cfgOf [
          decl
          {
            options._module = mkOption {
              type = t.submodule {
                options.foo = mkOption { default = 1; };
                options.args = mkOption { apply = a: a // { pkgs = "Q"; }; };
              };
              default = { };
            };
            config._module.foo = 2;
            config._module.args.pkgs = "P";
          }
          (
            { config, pkgs, ... }:
            {
              options.r = mkOption { };
              config.r = [
                config._module.foo
                pkgs
              ];
            }
          )
        ]).r;
      expected = [
        2
        "Q"
      ];
    };
    # Two modules' `apply`s on one owned key keep the later, as every redeclaration in this engine
    # right-biases a doubled field (ADR-0029's ordered fold). nixpkgs refuses the pair.
    test-two-applies-on-an-owned-key-keep-the-later = {
      expr =
        (cfgOf [
          decl
          { options._module.args = mkOption { apply = a: a // { pkgs = "Q1"; }; }; }
          {
            options._module.args = mkOption { apply = a: a // { pkgs = "Q2"; }; };
            config._module.args.pkgs = "P";
          }
          readPkgs
        ]).r;
      expected = "Q2";
    };
    # A nixpkgs `submodule` leaf is judged by nixpkgs with the engine's own declarations taking part,
    # and an untyped `apply` there merges with them, so it maps the merged set as nixpkgs' does.
    test-an-owned-key-apply-inside-a-nixpkgs-submodule-leaf-maps-the-merged-set = {
      expr =
        (cfgOf [
          decl
          {
            options._module = mkOption {
              type = nixpkgsLib.types.submodule {
                options.foo = nixpkgsLib.mkOption { default = 1; };
                options.args = nixpkgsLib.mkOption { apply = a: a // { pkgs = "Q"; }; };
              };
              default = { };
            };
            config._module.foo = 2;
            config._module.args.pkgs = "P";
          }
          (
            { config, pkgs, ... }:
            {
              options.r = mkOption { };
              config.r = [
                config._module.foo
                pkgs
              ];
            }
          )
        ]).r;
      expected = [
        2
        "Q"
      ];
    };
    # In a nested child, the set an `apply` on `_module.args` maps holds the position's `name`, and the
    # `name` its modules receive is the applied one, as in nixpkgs' `submoduleWith`: for the
    # tree-as-a-type and for `types.submodule` alike. The control reads the position without one.
    test-an-owned-key-apply-maps-a-nested-tree-child-name = {
      expr = nestedName (childTree [
        readName
        renameApply
      ]);
      expected = "Q";
    };
    test-an-owned-key-apply-maps-a-submodule-child-name = {
      expr = nestedName (
        t.submodule {
          imports = [
            readName
            renameApply
          ];
        }
      );
      expected = "Q";
    };
    test-a-nested-child-name-without-an-apply-is-the-position = {
      expr = nestedName (childTree [ readName ]);
      expected = "k";
    };
  };
}
