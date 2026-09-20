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
    # The ONE universal graph evaluator (ADR-0006, ADR-0008 §1). gen-merge's module-tree fixpoint is
    # an ordinary attribute on it, not a second driver — this library declares no `fix` of its own.
    #
    # ★ THIS EDGE CLOSES NO CYCLE, and gen-scope's own header states why the absence on the other
    # side is a dependency fact rather than an omission: it declares {gen-prelude, gen-graph,
    # gen-identity} and nothing else, gen-graph declares {gen-prelude}, and the other two declare
    # none — so nothing reachable from here declares gen-merge. The back-edge that WOULD close one
    # is gen-scope declaring gen-schema, which this adds nothing to. What the edge does cost is a
    # pin that a consumer declaring both must `follows`; that is ergonomics rather than correctness
    # (ADR-0014's corollary) and it is one line at the one tree declaring both.
    gen-scope.url = "github:sini/gen-scope";
  };

  outputs =
    {
      gen-prelude,
      gen-types,
      gen-memo,
      gen-scope,
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
            scope = gen-scope.lib;
          };
        in
        builtins.deepSeq (builtins.mapAttrs (_: builtins.typeOf) surface) surface;
    };
}
