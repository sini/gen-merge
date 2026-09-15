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
    # The incremental plane (ADR-0008 item 2): gen-merge computes the FACT (the bipartite
    # contribution relation between module entries and declared-leaf locations), gen-memo DECIDES
    # reuse over it via `warmDecision`. One incremental plane, not a second one grown in this repo.
    gen-memo.url = "github:sini/gen-memo";
  };

  outputs =
    {
      gen-prelude,
      gen-types,
      gen-memo,
      ...
    }:
    {
      # `nix flake check` forces the WHNF of every top-level output and nothing deeper, so this root's
      # green quantified over the `lib` SPINE alone: a member of the published surface could throw and
      # the check still exited 0 (measured — den-hoag-z1ta6). Hanging the force on that spine is what
      # makes the green mean "the surface evaluates", and a library needs no new output name for it.
      # The depth is each member's WHNF and no deeper: a retirement tombstone is a published `throw`
      # by design (gen-scope's `buildNodes`), so a deep force is red on a healthy tree.
      lib =
        let
          surface = import ./. {
            prelude = gen-prelude.lib;
            types = gen-types.lib;
            memo = gen-memo.lib;
          };
        in
        builtins.deepSeq (builtins.mapAttrs (_: builtins.typeOf) surface) surface;
    };
}
