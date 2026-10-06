# THE MODULE-VISIBLE `_module` VIEW (den-hoag-eoka4). Inside a module, `config._module` carries the four
# keys nixpkgs' `internalModule` declares, in every evaluation: `args`, `check` (the strictness that
# governs this evaluation's refusal), `freeformType` (the resolved one, or `null`) and `specialArgs` (the
# caller's set, through a re-declared `type` or `apply`). Each expected value is nixpkgs' `evalModules` on
# the same input, except the one cell named `departure`. The view is stated per branch (a module declares
# `options._module`, the evaluation is positioned, or neither), so each key is read on each branch.
{
  evalRequest,
  genMerge,
  ...
}:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption;
  t = gm.types;

  decl = {
    options.x = mkOption { default = "dflt"; };
  };
  reader =
    f:
    { config, ... }:
    {
      options.r = mkOption { };
      config.r = f config;
    };
  rootRead =
    args: f: modules:
    (evalRequest (args // { modules = [ decl ] ++ modules ++ [ (reader f) ]; })).config.r;
  # A child at `n`, its modules reading their own view.
  childRead =
    args: ty: f:
    (evalRequest (
      args
      // {
        modules = [
          decl
          {
            options.n = mkOption {
              type = ty [ (reader f) ];
              default = { };
            };
          }
        ];
      }
    )).config.n.r;
  # An option typed by an evaluation's own `.type`, that evaluation called with `check = false`; with
  # `defined`, the option has a definition (its default), so its child is positioned.
  uncheckedTreeRead =
    args: defined: f: childModules:
    (evalRequest (
      args
      // {
        modules = [
          decl
          {
            options.n = mkOption (
              {
                type = (evalModuleTree { check = false; } (childModules ++ [ (reader f) ])).type;
              }
              // (if defined then { default = { }; } else { })
            );
          }
        ];
      }
    )).config.n.r;
  declaresModule = {
    options._module.foo = mkOption { default = 1; };
  };
  freeformed = {
    config._module.freeformType = t.lazyAttrsOf t.raw;
  };
  names = c: builtins.attrNames c._module;
  saS = c: c._module.specialArgs.s;
  redeclared = attrs: { options._module.specialArgs = mkOption attrs; };
in
{
  flake.tests.module-view = {
    test-a-module-reads-the-four-keys-when-no-module-sets-args = {
      expr = rootRead { } names [ ];
      expected = [
        "args"
        "check"
        "freeformType"
        "specialArgs"
      ];
    };
    test-a-module-reads-the-four-keys-beside-a-module-setting-args = {
      expr = rootRead { } names [ { config._module.args.pkgs = "P"; } ];
      expected = [
        "args"
        "check"
        "freeformType"
        "specialArgs"
      ];
    };
    test-a-declared-module-sub-option-sits-beside-the-four-keys = {
      expr = rootRead { } names [ { options._module.foo = mkOption { default = 1; }; } ];
      expected = [
        "args"
        "check"
        "foo"
        "freeformType"
        "specialArgs"
      ];
    };
    test-check-reads-true-by-default = {
      expr = rootRead { } (c: c._module.check) [ ];
      expected = true;
    };
    test-check-reads-the-callers-false = {
      expr = rootRead { check = false; } (c: c._module.check) [ ];
      expected = false;
    };
    test-check-reads-a-modules-false = {
      expr = rootRead { } (c: c._module.check) [ { config._module.check = false; } ];
      expected = false;
    };
    test-check-reads-a-modules-true-over-the-callers-false = {
      expr = rootRead { check = false; } (c: c._module.check) [ { config._module.check = true; } ];
      expected = true;
    };
    test-a-nested-child-check-is-its-own-not-the-callers = {
      expr = childRead { check = false; } t.submodule (c: c._module.check);
      expected = true;
    };
    # A child of an unchecked tree's `.type` under a strict root runs strict (it refuses an undeclared
    # key), and nixpkgs' child reads `true`: the view reads `strict`, not the nested `check`.
    test-a-child-of-an-unchecked-trees-type-reads-check-true = {
      expr = uncheckedTreeRead { } true (c: c._module.check) [ ];
      expected = true;
    };
    test-a-child-of-an-unchecked-trees-type-declaring-module-reads-check-true = {
      expr = uncheckedTreeRead { } true (c: c._module.check) [ declaresModule ];
      expected = true;
    };
    # The same child with no definition is evaluated unpositioned, and reads the same.
    test-an-undefined-child-of-an-unchecked-trees-type-reads-check-true = {
      expr = uncheckedTreeRead { } false (c: c._module.check) [ ];
      expected = true;
    };
    # departure: under a root `check = false` that child runs lax where nixpkgs' refuses (its `.type`
    # carries the evaluation's `check`), and the view reports the child's own strictness. nixpkgs reads
    # `true`.
    test-departure-a-lax-child-of-an-unchecked-trees-type-reads-check-false = {
      expr = uncheckedTreeRead { check = false; } true (c: c._module.check) [ ];
      expected = false;
    };
    test-check-reads-the-callers-false-where-a-module-declares-module = {
      expr = rootRead { check = false; } (c: c._module.check) [ declaresModule ];
      expected = false;
    };
    test-freeformtype-reads-null-without-one = {
      expr = rootRead { } (c: c._module.freeformType) [ ];
      expected = null;
    };
    test-freeformtype-reads-the-resolved-type = {
      expr = rootRead { } (c: c._module.freeformType.name) [
        freeformed
      ];
      expected = "lazyAttrsOf";
    };
    test-freeformtype-reads-the-resolved-type-where-a-module-declares-module = {
      expr = rootRead { } (c: c._module.freeformType.name) [
        declaresModule
        freeformed
      ];
      expected = "lazyAttrsOf";
    };
    test-a-submodule-reads-its-own-resolved-freeformtype = {
      expr = childRead { } (mods: t.submodule ([ freeformed ] ++ mods)) (c: c._module.freeformType.name);
      expected = "lazyAttrsOf";
    };
    test-specialargs-reads-the-callers-set = {
      expr = rootRead { specialArgs.s = "S"; } saS [ ];
      expected = "S";
    };
    test-specialargs-reads-empty-without-a-callers-set = {
      expr = rootRead { } (c: c._module.specialArgs) [ ];
      expected = { };
    };
    test-a-submodule-reads-its-own-specialargs-not-the-parents = {
      expr = childRead { specialArgs.s = "S"; } t.submodule (c: c._module.specialArgs);
      expected = { };
    };
    test-a-submodule-reads-the-specialargs-its-type-carries = {
      expr = childRead { } (mods: (t.submodule mods).withArgs { t = "T"; }) (c: c._module.specialArgs.t);
      expected = "T";
    };
    test-specialargs-redeclared-with-an-apply-maps-the-read = {
      expr = rootRead { specialArgs.s = "S"; } saS [ (redeclared { apply = v: v // { s = "A"; }; }) ];
      expected = "A";
    };
    test-specialargs-redeclared-with-an-admitting-type-reads-the-set = {
      expr = rootRead { specialArgs.s = "S"; } saS [ (redeclared { type = t.attrsOf t.str; }) ];
      expected = "S";
    };
    test-specialargs-redeclared-read-only-reads-the-set = {
      expr = rootRead { specialArgs.s = "S"; } saS [ (redeclared { readOnly = true; }) ];
      expected = "S";
    };
    # The read changes, the arguments do not: a module still receives the caller's `s`.
    test-control-an-applied-specialargs-leaves-the-module-argument = {
      expr = rootRead { specialArgs.s = "S"; } (c: c.y) [
        (redeclared { apply = v: v // { s = "A"; }; })
        (
          { s, ... }:
          {
            options.y = mkOption { default = s; };
          }
        )
      ];
      expected = "S";
    };
    test-control-args-read-is-unchanged = {
      expr = rootRead { } (c: c._module.args) [ { config._module.args.pkgs = "P"; } ];
      expected = {
        pkgs = "P";
      };
    };
  };
}
