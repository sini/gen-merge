# gen-merge — byte-mode module merge engine (`evalModuleTree`)

[![CI](https://github.com/sini/gen-merge/actions/workflows/ci.yml/badge.svg)](https://github.com/sini/gen-merge/actions/workflows/ci.yml) [![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-pink?logo=github)](https://github.com/sponsors/sini)

Pure-Nix, `nixpkgs.lib`-free module **merge** engine — the drop-in replacement for
`lib.evalModules` + `lib.types`-merge in the pure-gen module system. `evalModuleTree` collects a tree
of modules, ties the self-referential `config` fixpoint, resolves per-option definitions by priority,
recurses into structural types, routes unknown keys through a freeform type, and verifies leaves —
reproducing nixpkgs' merge **output**, byte-for-byte, on the surface a real configuration uses, with
zero nixpkgs.

gen-merge is the **MERGE half** of a two-part split: [gen-types](https://github.com/sini/gen-types)
answers *"is this value well-typed?"* (a `verify : v → null|err` checker), gen-merge answers *"how do
these definitions combine into one value?"* (a def-list → value fold). They meet only at leaves,
post-merge.

Design spec: `den-architecture/gen-specs/gen-resolve/2026-07-02-evalmoduletree-byte-mode-design.md`.

## Layering

```
gen-prelude → gen-types → gen-merge → { gen-schema, gen-aspects }      (BELOW gen-resolve)
```

gen-merge is the *within-node* definition merge; [gen-resolve](https://github.com/sini/gen-resolve)
is the *cross-node* D>I>P schedule conductor — a distinct, higher layer. gen-merge depends only on
gen-prelude (pure utilities) and takes gen-types' leaf checkers as an **injected** value.

## Gen Ecosystem

| Library | Role |
|---------|------|
| [gen-prelude](https://github.com/sini/gen-prelude) | Pure nixpkgs-lib-free utility base (builtins re-exports + vendored lib utils) |
| [gen-algebra](https://github.com/sini/gen-algebra) | Pure primitives (record, search monad, either, intensional identity) |
| [gen-types](https://github.com/sini/gen-types) | Clean-room MIT structural type checker (leaf/poly checkers; `verify: v → null\|err`) |
| [gen-merge](https://github.com/sini/gen-merge) | **This lib** — Byte-mode module merge engine (`evalModuleTree`, byte-identical to nixpkgs `lib.evalModules` over the priority subset) |
| [gen-schema](https://github.com/sini/gen-schema) | Typed registries (kinds, instances, collections, refs); re-hosted on gen-merge |
| [gen-aspects](https://github.com/sini/gen-aspects) | Aspect type system (traits, classification, dispatch); re-hosted on gen-merge |
| [gen-scope](https://github.com/sini/gen-scope) | HOAG scope-graph evaluator (demand-driven, \_eval memoization, circular attributes) |
| [gen-graph](https://github.com/sini/gen-graph) | Accessor-based graph query combinators (traversal, condensation, phaseOrder) |
| [gen-select](https://github.com/sini/gen-select) | Selector algebra (pattern matching over graph positions) |
| [gen-bind](https://github.com/sini/gen-bind) | Module binding (inject external args into NixOS modules) |
| [gen-dispatch](https://github.com/sini/gen-dispatch) | Relational rule dispatch STEP (stratified phases, conflict resolution) |
| [gen-resolve](https://github.com/sini/gen-resolve) | Demand-driven RAG evaluator over scope graphs (attribute schedule + convergence loop) |
| [gen-rebuild](https://github.com/sini/gen-rebuild) | Pure-Nix incremental rebuilder (change propagation, AFFECTED set) |
| [gen-vars](https://github.com/sini/gen-vars) | Pure-Nix vars/secrets (den-agnostic) |
| [gen-flake](https://github.com/sini/gen-flake) | The nixpkgs boundary — compose purely, inject resolved values, build NixOS systems (value-injection) |

## The 7-item merge primitive

`evalModuleTree` reproduces exactly the primitive den's grammar/registry surface reduces to:

1. **typed options + defaults** — `mkOption { type; default?; apply?; readOnly? }`; a `default`
   desugars to a lowest-priority definition (no separate codepath).
1. **freeformType** — `lazyAttrsOf` / `attrsOf` routing of undeclared keys.
1. **per-key `name` + `_module.args`** binding under keyed collections.
1. **self-referential `config` fixpoint** — one local `fix` per call; `config._module.args.X = config` lets siblings cross-reference.
1. **`imports` merging** — recursive collect/flatten, imports before own config.
1. **the `(loc, defs)` custom-merge escape hatch** — `mkOptionType { merge = loc: defs: …; }`.
1. **`deferredModule`** — a lazy, import-usable module value, **never forced** by composition (handed
   opaque to the terminal). `functionTo` is intentionally omitted (consumers wrap guard functions as
   data).

## The priority subset

den + the gen corpus use only `mkDefault` / `mkForce` / `mkMerge` / `mkIf` (plus the implicit
`mkOptionDefault` behind a plain `default =`). gen-merge therefore implements **one** override rule —
lowest priority-number wins, ties merge — over the four anchor constructors (all instances of the
general `mkOverride N`) plus the two combinators `mkMerge` / `mkIf`. The entire nixpkgs **order pass**
(`mkOrder` / `mkBefore` / `mkAfter`) and the exotic named overrides are deliberately absent — zero
uses across the surface. Equal-priority definitions merge in **reverse module order**, byte-identical
to nixpkgs (observable in list-typed options: three modules contributing `[a]` `[b]` `[c]` merge to
`[c b a]`; a single module's `[a b]` beside another's `[c]` merges to `[c a b]`).

## Usage

```nix
let
  genMerge = import (fetchGit "https://github.com/sini/gen-merge").outPath {
    prelude = genPrelude;
    types = genTypes;               # the leaf checkers
  };
  inherit (genMerge) evalModuleTree mkOption mkForce;
  t = genMerge.types;               # gen-types leaves ⊎ gen-merge structural strategies

  result = evalModuleTree {
    modules = [
      { options.name = mkOption { type = t.str; default = "anon"; }; }
      { name = mkForce "pinned"; }
    ];
  };
in
  result.config                     # ⇒ { name = "pinned"; }
```

`evalModuleTree { modules; specialArgs ? {}; check ? true; prefix ? [] } → { config; options; type }`.
`.config` is the merged output; `.options` is the merged descriptor map (introspection, no nixpkgs
eval); `.type` carries a `.merge` so a tree nests inside a parent tree (submodule recursion).

## The `types` namespace

`genMerge.types` = gen-types leaf **checkers** ⊎ gen-merge structural **strategies** — the `lib.types`
drop-in the re-host points at (`lib.types.X` → `genMerge.types.X`):

- from gen-merge (merge-bearing): `submodule`, `listOf`, `attrsOf`, `lazyAttrsOf`, `deferredModule`,
  `either`, `raw`, `anything`, plus `mkOption` / `mkOptionType`.
- from gen-types (verify-only leaves): `str`, `int`, `bool`, `enum`, `path`, `union`, `refined`, …
  (the merge-bearing gen-merge versions of `listOf`/`attrsOf` win in the union).

## Byte-mode scope (and the deferred structural seam)

This is **byte-mode**: it reproduces nixpkgs' order-sensitive merge exactly — the cut-over
conformance oracle and the NixOS terminal contract. It does **not** implement the confluent
semilattice merge, structural equivalence (`≈ₛ`), or pre-eval identity dedup — those are a separate,
deferred mode. The per-option combine is a **swappable kernel**: byte-mode passes the
nixpkgs-faithful kernel; the structural mode later swaps a confluent-join kernel without changing the
engine skeleton (see `2026-07-02-structural-identity-dedup-spike.md`).

## Known byte-mode boundaries (deliberate)

- `raw` uses `mergeEqualOption` (multiple equal-valued defs collapse); nixpkgs `raw` is
  `mergeOneOption` (throws on >1 def even if equal). Not exercised by the surface — add a strict
  `raw` only if a consumer hits it.
- the order pass (`mkOrder` / `mkBefore` / `mkAfter`) is unsupported (0 uses on the surface).
- `_module.check`'s unknown-key error message is minimal (freeform absorbs unknown keys on the
  surface, so the throw path is rarely hit).

## Purity

The library (`lib/`) is `nixpkgs.lib`-free — it is the *replacement* for `lib.evalModules`, so it
never calls it (enforced by `ci/tests/purity.nix`). nixpkgs enters only in `ci/` (the nix-unit
harness + the equivalence oracle's reference side).

## Testing

`nix flake check ./ci` runs the nix-unit suites: `merge` (the 7-item primitive + priority subset),
`deferred` / `checking` (non-forcing + leaf verification), `oracle` (byte-identity vs
`lib.evalModules`, with mutation-teeth assertions), and `purity`.

## Theoretical foundations

- **byte-mode = the conformance oracle + terminal contract** (structural-dedup spike §3).
- **priority = one override rule**, the grepped subset (design spec §7); nixpkgs order pass dropped.
- **deferredModule = a lazy constructor**, inspectable before forcing (Lorenzen 2025 §2.3).
- **the `(loc, defs)` hook = the escape the engine rides** (nixpkgs `mkOptionType.merge`).
