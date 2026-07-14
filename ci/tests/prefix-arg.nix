# `prefix` as a readable module argument — a module can read its own option path (= the merge `loc`).
#
# WHY: gen-merge's `submodule.merge` already passes `prefix = loc` into the nested eval (types.nix) and
# threads `name = last loc` to bodies via specialArgs — but `prefix` (the full path) was internal
# plumbing only (option-location math, modules.nix), never surfaced to bodies. Surfacing it lets a type's
# submodule body know its own location intrinsically (gen-aspects A-IDENT: `meta.aspect-chain = init
# prefix`). Additive: modules that don't declare a `prefix` formal are unaffected (function modules bind
# only their declared formals).
{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption submodule;

  # A submodule at option `sub` — its body reads `prefix`, which must be its option path `[ "sub" ]`.
  nested = evalModuleTree {
    modules = [
      {
        options.sub = mkOption {
          type = submodule ({ prefix, ... }: { options.p = mkOption { default = prefix; }; });
          default = { };
        };
      }
      { config.sub = { }; }
    ];
  };

  # A root module reads `prefix == [ ]` (no throw — the additive arg is present at the root too).
  root = evalModuleTree {
    modules = [
      ({ prefix, ... }: { options.q = mkOption { default = prefix; }; })
    ];
  };
in
{
  flake.tests.prefix.test-submodule-reads-own-prefix = {
    expr = nested.config.sub.p;
    expected = [ "sub" ];
  };
  flake.tests.prefix.test-root-prefix-empty = {
    expr = root.config.q;
    expected = [ ];
  };
}
