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

`evalModuleTree { modules; specialArgs ? {}; check ? true; prefix ? [] } → { config; options; type; provenance }`. `.config` is the merged output; `.options` is the merged descriptor map (introspection,
no nixpkgs eval); `.type` carries a `.merge` so a tree nests inside a parent tree (submodule
recursion); `.provenance` is a lazy per-loc record of WHERE each value came from (see below).

## Provenance

`.provenance` is an always-on, lazy tree mirroring `.config`'s loc structure — one record per option
loc, answering "which files defined this, and which won?" It costs nothing until read (a forced option
pays ~one extra thunk when the channel is untouched).

**Forcing contract** (matters to the diff consumer). Reading ANY field of a **declared-option** record
(`defs` / `winners` / `priority` / `defaulted`) forces that loc's contributing defs to **WHNF** — the
same property discharge (`dischargeProperties`, which branches on `isAttrs`) the value path runs to
resolve priorities, so a def that is a bare `throw` fires on a plain `.defs` read. What it does NOT
force is the **deep / merged VALUE**: the structural `.merge`, leaf `verify`, and `apply` never run for
a provenance read (those live on the value path). A **freeform** record is stricter-free still — it
reads only definition FILES (never the def value), because unmatched keys are attributed by `_file`
without discharge. So: provenance forces the *shape* of who-defined-what (declared: defs to WHNF;
freeform: files only), never the resolved value. (This is weaker than nixpkgs `definitionsWithLocations`,
which forces nothing — byte-mode discharges eagerly to resolve priorities.)

Per **declared-option** loc — a rich record:

```nix
{
  defs      = [ { file; priority; } … ];  # ALL contributing defs, post property-discharge, pre
                                          # priority pass (a property tag keeps its originating
                                          # file; a false-`mkIf` sub-def has already dropped).
                                          # Per-def priority = its mkOverride wrapper's number,
                                          # else the default override priority (100).
  winners   = [ { file; } … ];            # the defs the priority pass kept (the merge's inputs).
  priority  = <int>;                      # the effective (min) priority the filter selected.
  defaulted = <bool>;                     # the option's own `default` supplied the value (the
                                          # synthetic `<default>` def was the sole winner).
}
```

Per **freeform** loc — a REDUCED record: `defs = [ { file; } … ]` (the files whose unmatched subtree
routes through this loc; **over-inclusive** — a false-`mkIf`-wrapped freeform def still appears here,
because the freeform pass discharges per key only inside its own `.merge`, which provenance does not
enter), with `winners` / `priority` / `defaulted` = `null`. `null` means "freeform / not observable",
**never** "no override present".

Declared records win over freeform at shared paths (mirroring config's `recursiveUpdate freeform declared`). One boundary: a nested `moduleTree`-as-type merge (a tree nested inside a parent tree via
`.type.merge`) surfaces its `.config` only — the inner tree's provenance is not threaded out through
the nested merge.

## Source classification & the `pureModule` marker

Every collected module entry carries a **source class** (`classifyModule` decides it on the
*pre-application* module), the substrate a memoized-override / warm re-eval path reuses to tell which
locs a clean re-merge may splice unchanged. The classes:

- **`"attrset"`** — an attrset module (or a path that imports to one). No body, cannot read anything
  ⇒ clean **unconditionally**. This is the provable core.
- **`"dirty"`** — every function module (bare lambda, `{ … }:` formals, `args@{ … }:` capture, a path
  that imports to a function, or an `__functor` attrset without the marker). **Dirty by default.**
- **`"marked-pure"`** — a `pureModule`-wrapped function (below). The author's clean assertion; the tag
  applies to that wrapper's own entry only — modules reached through its `imports` classify
  independently.

**Why function modules are dirty by default** (not decidable from formals): `builtins.functionArgs`
cannot prove a function clean. `args@{ genSchema, ... }: args.config.foo` reports only `genSchema` yet
the `@`-binding captures the whole argument set, and a bare lambda (`args: args.config.foo`) reports
`{ }` — either reads `config` regardless of visible formals. The engine applies **every** function
module with the full `specialArgs // extra` set (nixpkgs application semantics, which byte-mode
keeps), so a function module can always reach `config`. Only the author knows it doesn't.

### The `pureModule` contract

```nix
genMerge.pureModule ({ genSchema, ... }: { options.x = genSchema.mkThing; })
# ⇒ { __pureModule = true; __functor = self: <the fn>; }   (classifies "marked-pure")
```

`pureModule f` wraps `f` so the marker is readable **before** `callM` applies it (a bare function's
cleanliness is invisible once applied). The author asserts, and the engine **trusts**:

1. `f` reads **only its declared formals** — no `config` / `options` capture.
1. **every formal resolves from `specialArgs`** — not from `config`/`options`, and *not* from
   fixpoint-derived `_module.args`. Which side satisfies a formal is **non-local**: another module can
   define a `_module.args` entry of the same name, making an innocent-looking formal fixpoint-derived.

A **lying marker** (a marked module that reads `config`/`options` or a fixpoint arg) is an **author
bug**, not caught at classify time. Blast radius: **silent stale values** under a warm/reuse path —
the reused loc keeps a previous value that a cold merge would have recomputed — until a byte tooth
(the standing override oracle, a consumer's CI, or a bench byte gate) diverges warm from cold and
surfaces it. Unmarked `@`-capture / bare-lambda modules are **safe** (dirty ⇒ always re-merged); the
marker only ever *loses* safety, never gains it, so mark only modules you can prove satisfy both
clauses. den-hoag's emit layer can mark its data modules mechanically.

The marker key never reaches config: `callM` consumes the wrapper before the content entry is
recorded, and `configOf` strips `__pureModule` belt-and-braces.

## The `types` namespace

`genMerge.types` = gen-types leaf **checkers** ⊎ gen-merge structural **strategies** — the `lib.types`
drop-in the re-host points at (`lib.types.X` → `genMerge.types.X`):

- from gen-merge (merge-bearing): `submodule`, `listOf`, `attrsOf`, `lazyAttrsOf`, `deferredModule`,
  `either`, `raw`, `anything`, plus `mkOption` / `mkOptionType`.
- from gen-types (verify-only leaves): `str`, `int`, `bool`, `enum`, `path`, `union`, `refined`, …
  (the merge-bearing gen-merge versions of `listOf`/`attrsOf` win in the union).

## Compat mode

The `types` argument is an injection seam, so it can point at nixpkgs' own `lib.types` and run the
**same byte-mode engine** over unmodified nixpkgs option types — zero adapter code:

```nix
genMergeCompat = import (fetchGit "https://github.com/sini/gen-merge").outPath {
  prelude = genPrelude;
  types = (import "${nixpkgs}/lib").types;   # nixpkgs leaf/structural types, verbatim
};
```

nixpkgs option types already speak the `(loc, defs)` merge contract `mergeDefs` dispatches on — a
nixpkgs type carries a `.merge` (called `type.merge loc defs`) and no gen-types `.verify` (so the
post-merge verify is skipped) — and nixpkgs property tags (`_type = "override"/"merge"/"if"`) are
byte-compatible with gen-merge's priority pass, so `mkDefault`/`mkForce`/`mkIf`/`mkMerge` from nixpkgs
discharge identically. (Pinned by `ci/tests/compat-nixpkgs-types.nix`.)

**When to use it** — a migration on-ramp: bring a custom nixpkgs `mkOptionType` (or an odd leaf type)
along while porting a config onto the pure-gen module system, instead of rewriting it up front. An
escape hatch, **not** the fast path.

**Cost profile** (measured — [gen hub `BENCHMARKS.md`](https://github.com/sini/gen/blob/main/BENCHMARKS.md#compat-mode)):

- **leaf-type shims are free** — a nixpkgs leaf's `.merge` is trivial, so the engine keeps the full
  speedup: hybrid **0.62×** of nixpkgs cpu, vs pure gen-merge's **0.63×**, at `scalar` n=16000.
- **structural-type shims give the win back** — nixpkgs `submodule.merge` runs `lib.evalModules` per
  instance, dragging the nixpkgs engine into every subtree: hybrid **0.96×**, vs pure **0.44×**, at
  `registry` (`attrsOf submodule`) n=2000.

So keep den-hoag's hot registry/aspect paths on gen-merge's structural strategies; reserve compat
mode for the leaf/custom-type edges of a port.

**One-way boundary** — types flow nixpkgs → engine, not the reverse. A nixpkgs type plugs INTO
gen-merge because it carries `.merge`; a gen-types checker does **not** run inside nixpkgs'
`lib.evalModules`, because it is verify-only (no `.merge`). Compat mode injects nixpkgs types into the
gen-merge engine — it does not export gen-types checkers into `lib.evalModules`.

**Purity** — nixpkgs enters here as an injected VALUE (the `types` argument), exactly as gen-types
does; `lib/` never gains a nixpkgs dependency (enforced by `ci/tests/purity.nix`) — the same
value-injection philosophy as [gen-flake](https://github.com/sini/gen-flake).

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

These boundaries are mechanically checkable — see [Portable-subset lint](#portable-subset-lint).

## Portable-subset lint

`genMerge.lint { modules } → [ findings ]` (empty list ⇒ portable) statically flags the modules that
step outside the byte-mode surface, so the "runs on gen-merge and `lib.evalModules` byte-identically"
claim is verifiable, not asserted. The flagged kinds:

| kind | what it catches | why it diverges |
|------|-----------------|-----------------|
| `order-pass` | a config def carrying an `_type = "order"` marker (`mkOrder` / `mkBefore` / `mkAfter`) | gen-merge drops the whole order pass (see the priority subset) — the marker is carried as an ordinary value and mis-orders |
| `options-introspection` | a module **function** whose formals include `options` | byte-mode `.options` is a minimal descriptor map (the merged decl tree), not the nixpkgs-shaped `options` structure |
| `type-merge` | the same option loc declared **with a `type`** in more than one module | nixpkgs combines the declarations through a `typeMerge` functor; gen-merge field-unions them (later type wins) |
| `function-to` | an option type named `functionTo` | intentionally omitted from the type surface (wrap guard functions as data) |
| `unverifiable` | an option type nested deeper than the type-walk fuel | can't decide `functionTo` at that depth — reported rather than silently accepted (a portability lint must not false-negative) |

Each finding is `{ kind; loc; file; detail }` — `loc` is the option/config path (`[]` for a whole-module
finding like `options-introspection`); `file` is the def/decl provenance (`_file`), a **list** of files
for `type-merge`.

**The detection is a STATIC walk that inherits the engine's forcing profile** — it is *total* on
portable inputs (it never forces what the engine wouldn't). It reuses the engine's own classification
and property machinery (`dischargeProperties` / `pushDownProperties`), so order-pass is decided by
descending the merged option-decl tree like the realizer: properties are pushed down per level and defs
are discharged at declared leaves, so an `mkIf false { … }` branch drops (its throwing content is never
forced) and a data leaf's payload is only probed to WHNF, never deep-walked. The walk **stops at
declared leaves** — an order marker buried inside a structural-typed value (attrsOf/listOf/submodule
element defs) rides that strategy's own merge and is out of scope; option **defaults** are not
force-inspected (a `default = throw "must set"` stays portable), so order-pass is decided on config
*defs* only. Two further order-marker shapes sit outside this walk and are **not** flagged (both
zero-use on the den surface, named so the boundary is airtight): an order marker **at a
declared-group node** (`grp = mkBefore { … }` where `grp` is a group — `pushDownProperties` does
not distribute an `order` marker, so its fields are walked as child keys, never probed as a
marker), and an order marker **nested more than one level under a freeform/undeclared key**
(`free = { sub = mkAfter […]; }` — only the undeclared def's top value is probed for
`_type = "order"`). The lint never *applies* a module function (its body needs the `config`
fixpoint, which a lint must not force — it may throw, and catching throws is disallowed in pure
eval; the engine binds modules by static formals only). So a function module is opaque except
for its formals (only `options-introspection` is decidable on it); the other kinds are decided
on attrset modules, `import`ed path leaves, and the modules reached through `imports`. A
submodule's `getSubModules` is a separate nested eval — lint those by passing them to `lint`
directly.

Run it over a module list (or wire it into CI as an accept-gate — `ci/tests/lint.nix` asserts it
accepts the whole equivalence corpus and rejects one fixture per construct):

```nix
genMerge.lint {
  modules = [
    { options.tags = genMerge.mkOption { type = genMerge.types.listOf genMerge.types.str; default = [ ]; }; }
    { tags = genMerge.mkForce [ "a" ]; }                       # portable — a plain override
  ];
}
# ⇒ [ ]   (portable)

genMerge.lint {
  modules = [
    { options.tags = genMerge.mkOption { type = genMerge.types.listOf genMerge.types.str; default = [ ]; }; }
    { tags = lib.mkAfter [ "z" ]; }                            # NON-portable — an order marker
  ];
}
# ⇒ [ { kind = "order-pass"; loc = [ "tags" ]; file = "<gen-merge>"; detail = "…"; } ]
```

## Purity

The library (`lib/`) is `nixpkgs.lib`-free — it is the *replacement* for `lib.evalModules`, so it
never calls it (enforced by `ci/tests/purity.nix`). nixpkgs enters only in `ci/` (the nix-unit
harness + the equivalence oracle's reference side).

## Testing

`nix flake check ./ci` runs the nix-unit suites: `merge` (the 7-item primitive + priority subset),
`deferred` / `checking` (non-forcing + leaf verification), `oracle` (byte-identity vs
`lib.evalModules`, with mutation-teeth assertions), `compat` (nixpkgs `lib.types` on the engine),
`core-kernel` (the fixed-input short-circuit), `provenance` (the `.provenance` record shapes + forcing
contract), `lint` (the portable-subset checker — accepts the whole `oracle` corpus, rejects one fixture
per unsupported construct), and `purity`.

Running the suites directly through the nix-unit CLI (`nix-unit --flake ./ci#tests`, or the devshell
`ci` command) needs a raised stack — `ulimit -s unlimited` — at the default 8 MB: nix-unit's own
traversal of the deep module-system evals overflows it (the pre-commit hook and the devshell command
raise it automatically; `nix flake check ./ci` is a plain eval and does not need it).

## Theoretical foundations

- **byte-mode = the conformance oracle + terminal contract** (structural-dedup spike §3).
- **priority = one override rule**, the grepped subset (design spec §7); nixpkgs order pass dropped.
- **deferredModule = a lazy constructor**, inspectable before forcing (Lorenzen 2025 §2.3).
- **the `(loc, defs)` hook = the escape the engine rides** (nixpkgs `mkOptionType.merge`).
