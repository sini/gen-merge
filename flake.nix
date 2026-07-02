{
  description = "gen-merge — pure-Nix byte-mode module MERGE engine (evalModuleTree) for the pure-gen module system";

  # Class layering: gen-prelude → gen-types → gen-merge → { gen-schema, gen-aspects }; BELOW
  # gen-resolve (the schedule-only conductor). The library (./lib) is nixpkgs-lib-free (checked by
  # ci/tests/purity.nix) — it REPLACES lib.evalModules. nixpkgs is pulled ONLY in ci/ (the nix-unit
  # harness + the evalModules-equivalence oracle's reference side).
  #
  # gen-types supplies the leaf CHECKERS; gen-merge owns the def→value MERGE. gen-types is a leaf
  # dep here (must stay standalone — a lib below gen-schema consuming it, else a flake cycle).
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";
    gen-types.url = "github:sini/gen-types";
  };

  outputs =
    {
      gen-prelude,
      gen-types,
      ...
    }:
    {
      lib = import ./lib {
        prelude = gen-prelude.lib;
        types = gen-types.lib;
      };
    };
}
