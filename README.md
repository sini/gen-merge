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
| [gen-class](https://github.com/sini/gen-class) | Class-share mechanism (partition / contract / apply / gate), byte-gated; its tier-2 fixed-input path rides this engine's `coreShortCircuit` kernel |
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

`evalModuleTree { modules; specialArgs ? {}; check ? true; prefix ? [] } → { config; options; type; provenance; undeclared; deprecations }`. `.config` is the merged output; `.options` is the merged descriptor map (introspection,
no nixpkgs eval); `.type` carries a `.merge` so a tree nests inside a parent tree (submodule
recursion) — it is a nesting seam and NOT a mountable option type, so it carries a `nonMountable`
mark and refuses the rest of the option-type protocol by name (see below);
`.provenance` is a lazy per-loc record of WHERE each value came from (see below);
`.undeclared` lists the definitions the eval did not merge into `.config` (see below);
`.deprecations` lists the declared options whose TYPE carries a `deprecationMessage` (see below).

Every function module receives `config`, `options`, and `prefix` (the module's option path, equal to
the `loc` at the enclosing `submodule.merge` call — `[]` at the root, `["sub"]` inside an option
named `sub`) in addition to any `specialArgs` and `_module.args` entries.

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

## Undeclared definitions

An unmatched definition — a config key with no matching declaration — has three dispositions and no
fourth. A `freeformType` **absorbs** it; `check = true` **refuses** it (the orphan throw, naming the
option path); with neither, it is **not merged** at all. `.undeclared` exists for the third case — the
only one that returns neither a value nor a named refusal — but is **not scoped to it**: the list
carries every unmatched definition a `freeformType` did not absorb, **the refused ones included**, so
under `check = true` the same definitions are listed while `.config` throws. It is an always-on lazy
list, one record per DEF (two files defining the same undeclared name are both named), ordered per key
by reverse module order like `provenance.defs`.

```nix
[ { path = [ "grp" "unknown" ]; file = "…/some-module.nix"; } … ]
```

It is a **sibling of `config`, never a key inside it**: `check = false` exists so that the merged value
does *not* grow the undeclared key, so a report living in `config` would change what the flag produces
instead of describing it. `check` does not gate the list — whether the engine tells the truth about
what it consumed is a different question from whether it checks — while a `freeformType` does, since
there the definitions are merged and nothing was dropped. A fully declared config reports `[ ]`.

Reading it forces **no definition value**: the records carry names and originating files only (the
same data the freeform provenance records read), so a def that is a bare `throw` does not fire.
`path` is absolute against `prefix`, naming the same location the orphan throw would.

It is **over-inclusive in the same way the freeform provenance records are**: a def wrapped in a false
`mkIf` still appears, because properties are discharged per key only inside the freeform `.merge`,
which this pass does not enter. This is the report↔refusal correspondence holding, not a leak —
whatever `check = true` refuses, `check = false` reports, and that same `mkIf false` def does throw
under `check = true`. Filtering it here would desynchronise the report from the refusal.

**Capture granularity.** A path is the first undeclared name on its branch, and the record covers that
loc *with everything beneath it*. Deeper rendering has no well-defined answer: with no declaration,
`config.nested.deep.key = "X"` and `config.nested = { deep.key = "X"; }` are the same definition, so a
descent could not tell a dropped option path from a dropped attrset value. The nested-tree boundary is
provenance's: a tree merged as a type surfaces its `.config` only.

## Deprecated types

`deprecationMessage` is one of the 14 fields of the nixpkgs `optionType` protocol this library stamps
onto every completed type (below). It was, for a time, the one field the engine **stored and never
read** — which is not a neutral placeholder: a conformance check asserting the field's *presence*
passes while the *behaviour* the field exists for is absent, so a deprecated type was
indistinguishable from an undeprecated one at the only place that could tell. `.deprecations` is that
behaviour: an always-on lazy list, one record per declared option whose type carries a message.

```nix
[ { path = [ "grp" "d" ]; type = "depA"; message = "use `plainA' instead"; declarations = [ "…/a.nix" "…/b.nix" ]; } … ]
```

`path` is absolute against `prefix`; `type` is the type's **name**; `declarations` names every module
that declared the option, in authored order — a deprecation is fixed at the declaration, and the file
supplying the type need not be the only one declaring the option (a layering module adding an `apply`
carries no type of its own). These are the data nixpkgs' own `warnDeprecation` reports, read off the
same field.

**On the result, not on stderr**, and that is a mechanism decision: Nix's eval cache swallows
`trace`/`warn`, so a printed deprecation appears on the first eval and never again — a report that
disappears when the answer is reused reports nothing. A field on the result needs no new vocabulary
and cannot be silently dropped by a consumer. It is also **serialisable by construction** — carrying
the type's name rather than the type value is what lets a consumer print, diff or hand on the report
at all, since a type value carries functions.

Reading it forces each declared leaf's **type** — that is where the field lives — and **no definition
value**; leaving it unread costs nothing. An option declared with no type, and a type that never
reached protocol completion, are both simply not deprecated: neither aborts the report.

**Scope is one eval.** A `submodule`'s inner options are declared in a nested `evalModuleTree` that
runs *inside* the type's `merge`, and `merge` returns the merged **value** — byte-compat pins that
shape, so the nested eval has no way to hand its report back alongside the value it was called for.
That is why one eval is the scope, and it is **not** that the nested view is out of reach: the
declaration stratum is already exposed by the protocol, so a consumer that wants it re-derives it
without touching `merge` —

```nix
(evalModuleTree { modules = ty.getSubModules; }).deprecations
# ⇒ [ { path = [ "inner" ]; type = "depA"; message = "…"; declarations = [ "<gen-merge>" ]; } ]
```

`ty.getSubOptions` reaches the same declarations as a tree if that shape suits better. Note what the
re-derived records say about provenance: `declarations` reads `[ "<gen-merge>" ]`, because sub-modules
carry no `_file` — a reason for the parent not to fold this view into its own report, rather than a
reason it could not. Stamping the field is this engine's job; composing the strata belongs to whoever
composes the results. Same boundary as provenance's.

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

## Warm re-eval (memoized override)

`evalModuleTree` takes two opt-in knobs that turn a re-eval after an APPENDED edit into a *warm* one —
reusing the previous result's declared-leaf values/provenance for locs provably untouched by the edit,
re-merging only the rest inside the normal fixpoint:

```nix
evalModuleTree {
  modules       = base ++ edited; # the full list
  warmFrom      = prevResult;     # the PREVIOUS evalModuleTree result (its config/provenance/freeform ARE the memo)
  editedModules = edited;         # the APPENDED module list
}
```

Default (`warmFrom = null`, `editedModules = [ ]`) ⇒ **zero behaviour change**: the decision is never
forced, every leaf takes the cold merge, freeform re-merges cold (the `coreShortCircuit` precedent —
an opt-in knob with a documented firing contract). Warm is the reverse-cone reuse of adios's
`mkOverride`, but sound under gen-merge's config *fixpoint* (adios has none).

**Firing.** The engine flattens `editedModules` with its OWN `collectModules` — the EDITED entries are
the tail-k of the full flatten (k = `length (collectModules callM editedModules)`, never a caller
count, since `imports` expansion is config-dependent). Warm is REFUSED (cold fallback, stated in the
trace) when any edited entry carries `disabledModules` (it would disable a clean base module invisibly
to the footprint). Whether an override *reduces* to a modules-append at all is the caller's call
(gen-flake's `override`); the engine just splices when handed a `warmFrom`.

**The dirty footprint (the reusability predicate).** A module entry is CLEAN (`srcClass` attrset /
marked-pure — config-independent), DIRTY (function, `srcClass` dirty), or EDITED (in the appended
tail). The **dirty footprint** is the union, over DIRTY ∪ EDITED entries, of

- their **decl paths** (`declLeafPaths` of the entry's own `options`), and
- their **def paths** landing on a declared leaf (`moduleDefFootprint` — the portable-lint's
  discharge-based descent, recording PATHS not values: it pushes config-node properties down at each
  declared-group level and stops at a declared leaf or an undeclared key, **never forcing a leaf
  value** — only the config spine, bounded by the module's structural size, which a dirty/edited module
  re-merges anyway).

A declared leaf is **REUSABLE iff it is outside this footprint** — then both its decl set and its def
set come only from CLEAN modules (constant attrsets, or marked-pure modules applied with unchanged
`specialArgs`), so its inputs to the merge are identical to the previous eval and the value/provenance
are byte-identical.

**Splice at leaves only.** `prev.config` is `recursiveUpdate freeform declared`, so a whole *untyped
group* splice would capture stale freeform descendants whenever the freeform plane re-merges. At an
`isOptLeaf` loc (a declared scalar leaf OR a typed registry) the prev value is **declared-only**
(freeform never wins a declared leaf), so leaf-granularity splicing is sound; untyped declared groups
RECURSE and splice their leaves. A splice is `getAttrByPath` of prev's `config` / `provenance` — the
SAME memoized thunk, lazy (an unforced prev leaf stays unforced; a forced one is free).

**Freeform is coarse (soundness-forced).** Freeform is a single root-level opaque merge, and an edited
`freeformType` candidate flips the priority-resolved winner and changes EVERY freeform loc while naming
none of them. So the whole prev freeform layer is reused iff (a) NO dirty/edited entry contributes an
unmatched (freeform) def path AND (b) NO edited entry contributes a `freeformType` at EITHER site
(top-level `freeformType` or `_module.freeformType`); otherwise ALL freeform re-merges. Per-path
freeform reuse is deferred (perf impact is ~nil — the target shape is registry-heavy, freeform
incidental).

**Boundary.** A nested `moduleTree`-as-type merge is always COLD (no `warmFrom` threaded through
`.type.merge`) — the same boundary provenance draws.

**The decision trace.** Every result carries `.warmDecision` (always-on data; `mode = "cold"` on a
plain compose):

```nix
{
  mode     = "warm" | "cold";                     # cold = the fallback fired (reason stated)
  reason   = <string|null>;                       # why cold (no warmFrom / disabledModules refusal)
  reused   = [ <loc-string> … ];                  # the spliced declared leaves (dot-joined)
  remerged = { <loc-string> = <reason>; };        # "edited-def" | "dirty-def <file>" | "dirty-decl <file>" | "freeform-dirty <file>"
  modules  = { clean = [ file… ]; dirty = [ … ]; edited = [ … ]; };   # the classification
}
```

**Laziness contract.** `mode` / `modules` are cheap (classification only). `reused` / `remerged` are
`O(declared-locs)` spine-forcing when read (they enumerate the loc partition — never leaf values). This
is adios's "what was reused vs re-evaluated," delivered as data.

**The `pureModule` teeth here.** A lying marker's stale reuse surfaces as a warm-vs-cold byte
divergence — the standing override oracle (every consumer's CI), the in-bench byte gate, and the
adversarial suite fixture (a marked module that `@`-captures config, asserted to diverge visibly) all
pin it. The two internal memo fields `freeformConfig` / `freeformProv` on the result let a CHAINED warm
(warmFrom = a warm result) reuse the freeform layer directly.

**Result surface.** The public result is `config` / `options` / `provenance` / `undeclared` /
`deprecations` (+ `type`);
`warmDecision` (the decision trace) and `freeformConfig` / `freeformProv` (the freeform memo layers)
are internal fields — additive, threaded between chained evals, not part of the byte-identity contract.

## The `types` namespace

`genMerge.types` = gen-types leaf **checkers** ⊎ gen-merge structural **strategies** — the `lib.types`
drop-in the re-host points at (`lib.types.X` → `genMerge.types.X`):

- from gen-merge (merge-bearing): `submodule`, `listOf`, `attrsOf`, `lazyAttrsOf`, `deferredModule`,
  `either`, `raw`, `anything`, plus `mkOption` / `mkOptionType`.
- from gen-types (verify-only leaves): `str`, `int`, `bool`, `enum`, `path`, `union`, `refined`, …
  (the merge-bearing gen-merge versions of `listOf`/`attrsOf` win in the union).

## The nixpkgs `optionType` protocol

Every type in the `types` namespace is completed (`mkOptionType` → `completeType`) to the full
**14-field nixpkgs `mkOptionType` shape** — `_type`, `name`, `description`, `descriptionClass`,
`deprecationMessage`, `check`, `merge`, `emptyValue`, `getSubOptions`, `getSubModules`,
`substSubModules`, `typeMerge`, `nestedTypes`, `functor` — so the SAME type value serves both
engines. This is what lets gen-schema inject gen-merge-typed options into an instance submodule that
a **nixpkgs** `lib.evalModules` evaluates (the corpus path: `mkInstanceRegistry` inside flake-parts).
Pinned by `ci/tests/nixpkgs-protocol.nix`.

The scope of that sentence is the `types` namespace, and there is exactly one type-shaped value
outside it: an eval result's `.type`, which is a nesting seam and must NOT mount. It is covered
below.

The protocol has two halves. The **merge** half (`merge`, `emptyValue`, `typeMerge`) says how defs
combine; the **introspection** half (`getSubOptions`, `getSubModules`, `substSubModules`,
`nestedTypes`) says what a consumer can learn from a type *without any value* — how a documentation
generator, an LSP, or a registry-reflecting consumer reads a DECLARED surface.

`getSubOptions prefix` returns the option records one submodule level down. The nixpkgs rules, which
gen-merge reproduces:

```nix
# submoduleWith
getSubOptions = prefix: (evalModules { inherit modules prefix specialArgs; }).options;
# attrsOf / lazyAttrsOf
getSubOptions = prefix: elemType.getSubOptions (prefix ++ [ "<name>" ]);
# listOf
getSubOptions = prefix: elemType.getSubOptions (prefix ++ [ "*" ]);
```

```nix
# nullOr — pass straight through, adding NO segment: a nullable introduces no path level
getSubOptions = elemType.getSubOptions;
```

gen-merge's `submodule` reads `.options` off the same nested `evalModuleTree` its `merge` builds, with
no defs supplied, so the introspection and merge halves cannot disagree about what a submodule
declares, and nothing an instance authored is forced. A **leaf** type has no sub-options and returns
`{ }` — the `completeType` default, which stays correct for every non-structural type.

Two types report `{ }` **correctly**, and should not be "fixed" into reporting something else.
`deferredModule`'s sub-options in nixpkgs are its `staticModules`; gen-merge ships no
`deferredModuleWith`, so that set is empty by construction. And an element that is not
protocol-complete — a gen-types **parametric** leaf (`enum`, `struct`, `union`) reaches the unified
namespace as a bare constructor and is never completed — declares no sub-options either, so a wrapper
reports `{ }` rather than aborting on a missing attribute.

#### The module-set half: `null` and `[ ]` are two different answers

`getSubModules` reports the module set a type carries, and it distinguishes **not having one** from
**having an empty one**:

| answer | means |
|---|---|
| `null` | this type has no sub-module concept at all — a **leaf**'s answer |
| `[ ]` | this type has a module set and there is nothing in it — `deferredModule` |
| `[ … ]` | the modules it carries — `submodule`, and the containers, which report their element's |

One `null` cannot carry both facts. Reported as `null`, `deferredModule`'s *"has nothing to declare"*
was indistinguishable from `str`'s *"declares nothing"*, so a consumer walking the protocol could not
tell the two apart. `deferredModule`'s set is empty **by construction** — gen-merge ships no
`deferredModuleWith`/`staticModules` parameter — and that is a fact to report, not an absence.

The encoding and the **rebuild** are one decision rather than two, because the consumer reads them
together: nixpkgs `fixupOptionType` branches on `getSubModules == null` and, for every other type,
replaces the option's type with `substSubModules opt.options`. So a type reporting a module set owes a
`substSubModules` that returns a type. `deferredModule` rebuilds over its own empty set — the argument
a mount actually passes — and **refuses by name** over a non-empty one: with no static-module
parameter it could only drop the modules, and a rebuild that silently discards what it was handed is a
wrong answer with no diagnostic.

### Two export shapes — completing only one leaves half the namespace unmountable

gen-types exports its **nullary** leaves (`str`, `int`, `bool`, `path`, …) as attrsets and its
**parametric** ones (`enum`, `struct`, `union`, `tuple`, `refined`, `optionalAttr`, …) as
**constructors**. Completing the export only reaches the first shape — the type a constructor *returns*
arrived bare, and mounting one in a nixpkgs `lib.evalModules` hit the very crash the protocol
completion exists to prevent (nixpkgs reads `deprecationMessage` off every option type). The completion
therefore descends *through* the application, at any arity, and completes the first result that is a
gen-types type.

Two rules that look like details and are not:

- **The predicate is `? verify`, not `? verify || ? name`.** A gen-types *helper* can return a
  `name`-bearing record that is not a type — `mkValidator name pred message` yields
  `{ message; name; pred; }`. Completing that would stamp `_type = "option-type"` onto a validator.
- **A completed parametric leaf REFUSES `typeMerge`.** Its parameters live behind the checker closures
  and cannot be read, and neither substitute works: gen-types' `__id` is name-only (`enum "e" [ "a" ]`
  and `enum "e" [ "b" ]` share one), and value equality is pointer-based over the closures (two
  identical constructions compare unequal). On the nullary default it would report "mergeable" for any
  same-named partner and silently drop one declaration's allowed values. "Not mergeable" gets the
  consumer a named refusal — gen-merge's own on the declaration path, nixpkgs' `already declared`
  under a foreign mount — instead of a wrong type. This diverges from nixpkgs'
  `enum`, whose functor unions the value sets — gen-merge cannot reproduce that without reading
  parameters it cannot see. A **nullary** leaf keeps its self-merge: it has no parameters to compare.

### `emptyValue` — when "nothing was defined" is not an error

With no surviving definition, nixpkgs lets the **type** supply a value before this is an error
(`modules.nix`: `else if type.emptyValue ? value then type.emptyValue.value`). A container nobody
added to is legitimately empty; a value nobody supplied is a mistake. `emptyValue` is what tells the
two apart, and gen-merge stamped `{ }` — *no* `value` attr — on every type, so both landed on the same
throw.

| type | `emptyValue` |
|---|---|
| `attrsOf`, `lazyAttrsOf`, `submodule` | `{ value = { }; }` |
| `listOf` | `{ value = [ ]; }` |
| `nullOr` | `{ value = null; }` |
| `raw`, `anything`, `deferredModule`, `either`, every leaf | *declares none* — still an error |

The table matches nixpkgs entry for entry, and the second half is as load-bearing as the first: a type
that declares no empty value must keep throwing.

There are **two ways to arrive with nothing**, and both reach the same rule: an option that was never
defined at all, and an option whose every definition was discharged away — `mkIf false` as the sole
def. So `attrsOf` yields `{ }`, `listOf` yields `[ ]` and `nullOr` yields `null` in both situations,
while a `str` still reports that it was used but not defined. An option `default` is a definition (at
`mkOptionDefault` priority), so it always wins over the empty value.

### `check` — and the types whose default was wrong

`check` is nixpkgs' definition-level predicate. gen-merge's own engine never reads it — it validates
through a gen-types leaf's `verify` — so `check` exists for the forward boundary and for the
`nullOr`/`either` membership dispatch. `completeType` derives it in that order: a leaf's `verify`
gives a real `v -> bool`; a structural type with its own `check` keeps it; anything else gets
`_: true`, the nixpkgs `anything` posture.

That default is correct for a type whose merge really does accept any value. **`deferredModule`'s does
not.** Its merge wraps each def into an `imports` list, and the engine's `callM` can apply only a path,
a function, a `__functor` attrset, or a plain attrset — so a wrong-shaped definition used to be
accepted and then detonate at whoever imported it, with no option path and no definition file. It now
tests the three shapes, as nixpkgs `deferredModuleWith` does, and is **stricter on one**: nixpkgs
reuses `types.path.check`, which admits a string beginning with `/`, while `callM` dispatches on
`builtins.isPath` and would carry such a string through as a module value. A check must never admit
what the merge cannot consume.

**Nor did the rest of the structural surface's.** `listOf` walks every definition with `imap0`,
`attrsOf`/`lazyAttrsOf` take the key union with `//`, and a submodule's definitions *are* modules —
so each states its domain too, matching nixpkgs on every shape except the submodule string-that-looks-
like-a-path, where the `deferredModule` narrowing above applies for the same reason
(`test-structural-check-shapes-match-nixpkgs`). Only `raw` and `anything` keep `_: true`, which is
what their merges genuinely do.

That was previously described here as a diagnostic gap rather than a soundness one, on the ground
that a wrong-shaped definition aborts on both engines either way. **Inside a union it is a soundness
gap**, and the correction is worth stating because the reasoning is general: a union's `check` is the
**disjunction** over its members, so a single member answering "yes" to everything makes the union
unable to refuse anything, and its merge then hands a definition to a member that cannot consume it.
See "`either` — a union's merge is total" below.

The remaining shape difference is a *diagnostic* one and stays: where a definition reaches a merge
that cannot consume it without passing a union — through `mergeDefs`, which reads `verify` and never
`check` — gen-merge still aborts with a raw builtin error (`expected a set but found a list`) where
nixpkgs names the option and the defining file.

### `either` — a union's merge is total

**Every definition is merged through a member that accepts it, or the merge refuses by name.** The
member is chosen by asking each one about the whole definition set, not about the first definition:
a set the list member takes whole merges through the list member, a set the string member takes
whole merges through the string member, and a set neither takes whole is a refusal naming the option
path and, per member, the files whose definitions that member rejected.

```
gen-merge: option `x' has definitions no single `either' member accepts
  (`listOf' rejects str.nix; `string' rejects list.nix)
```

Picking from the first definition instead handed the rest to a member that could not consume them.
`oneOf` is right-nested `either` and inherits the rule, so an n-ary union refuses at whichever
nesting level runs out of members.

A definition set that merged before merges to the same value: the member selected from the first
definition *is* the member that accepts them all whenever one does. **The refusal reaches every
definition set no single member accepts — and what it replaces depends on which member the old
dispatch happened to land on, so it is two different improvements rather than one.**

- **Where the old dispatch picked a CONTAINER, the set reached the interpreter.** `either (listOf str) str` with `["a"]` and `"b"` produced `expected a list but found a string: "b"` — an error
  naming neither the option nor the file and, being a builtin type error rather than a `throw`,
  escaping `builtins.tryEval`, so no caller could turn it into a diagnostic either. Here the refusal
  converts an **uncatchable abort** into a catchable one.
- **Where it picked a LEAF, the set never reached the interpreter and the old error was already
  catchable — it was simply wrong about the problem.** `either str (listOf str)` with the same two
  definitions selected the string member and threw `` the option `x' has conflicting definitions ``,
  the leaf conflict message: catchable, but the definitions do not conflict — they belong to
  *different members*, and the merge had already discarded that fact by choosing one. Here the
  refusal changes nothing about catchability and replaces a **misleading message with an accurate
  one**.

Cells: `ci/tests/merge.nix` (dispatch and the unchanged merges), `ci/tests-error.nix` `union-merge`
(the messages). The before/after exit-code pair is `ci/bench/either-totality.sh` — the abort in the
first case above cannot be observed by either nix-unit output, so the sweep keeps both constructions
and reads their exit codes.

### `functor` / `typeMerge` — merging the TYPES, not the values

`typeMerge` is the one protocol field that is about two **declarations** rather than about defs: when
an option is declared with a type in more than one module, `mergeOptionDecls` asks the first type to
merge with the second's `functor`, and refuses the declaration outright if the answer is `null`.
gen-merge's own engine routes through it — a redeclared leaf's type is the algebra's answer about the
pair, and `null` is a refusal naming the option path and every declaring file. The **non-type** fields
keep their ordered bias (see "Redeclaring an option" below), and the field also serves the **forward
boundary**: a gen-merge type mounted in a nixpkgs `lib.evalModules`.

A type's `functor` carries the parameters it was built from, and two same-named types merge iff those
parameters do:

```nix
# nullary — raw, anything, deferredModule, every gen-types leaf
{ name; type; payload = null; binOp = _a: _b: null; }      # same name ⇒ the type itself
# one-element containers — listOf, attrsOf, lazyAttrsOf, nullOr
{ payload = { elemType; }; type = p: rebuild p.elemType;
  binOp = a: b: <merge the elements, recursively>; }
# submodule — the parameter is the MODULE LIST (nixpkgs `submoduleWith`)
{ payload = { modules; }; binOp = l: r: { modules = l.modules ++ r.modules; }; }
# either — the parameter is the member PAIR, positional
{ payload.elemType = [ a b ]; }
```

So `attrsOf str` and `attrsOf int` are **not** mergeable, while two `attrsOf str` are, and two
submodule declarations of one option merge to a submodule declaring the union of both. A
parameterised type left on the nullary functor would answer "mergeable" for any same-named partner
and silently keep one declaration — the type-level form of a dropped definition.

Two guards nixpkgs has no need of, because every functor nixpkgs meets is its own. gen-merge meets
**foreign** functors by construction, so a payload that is asymmetrically present, or present with a
different **shape**, is answered "not mergeable" rather than aborting or rebuilding a gen container
out of a payload it does not understand — nixpkgs `submoduleWith` carries `class`/`specialArgs`/… beside
`modules`, and truncating that into a gen-merge `submodule` would drop them silently. For the same
reason an element that is not protocol-complete (a gen-types **parametric** leaf — `enum`, `struct`,
`union` — reaches the unified namespace as a bare constructor and is never completed) makes its
container not mergeable instead of aborting on a missing attribute.

### Redeclaring an option

Two modules may declare the same option loc. The merge splits the record in two:

- **The `type` is the algebra's answer, or a refusal.** When both declarations carry a `type`, the
  merged type is `typeMerge`'s (above). `null` — "not mergeable" — is a named refusal carrying the
  option path and *every* declaring file. The outcome the routing removes is one declaration's field
  surviving beside the *other's* type on a record that then disagrees with itself.
- **The non-type fields are right-biased, and what they shadow stays reachable.** Later declarations
  win field by field: this fold is an *ordered* fold over the authored module order, so a later
  declaration is a later contribution rather than a stronger one, and a module layering `apply` onto
  an earlier typed leaf composes exactly as it reads. An ordered bias is a rule only while the loser
  is still reachable, so a merged record that actually shadowed a field carries what it shadowed:

```nix
(evalModuleTree { modules = [ a b ]; }).options.x
# ⇒ { _type = "option"; type = <str>; default = "from-B";
#     overridden = [ { file = "a.nix"; declaration = { type = <str>; default = "from-A"; }; } ]; }
```

Each entry's `file` names the module that most recently **contributed** to the record being
shadowed, which is not always the module that first declared the option: a module adding a field
shadows nothing and records no entry of its own, and when a later module restates that field the
entry names the module that wrote it.

**Against nixpkgs, measured on four shapes.** On the **type** the two engines agree: a type-only
`str`/`str` redeclaration merges under both, and `str`/`int` is refused by both, in nixpkgs' case
through the same functor. They part on the **other** fields — nixpkgs refuses a redeclaration
outright when both declarations carry any of `default`/`example`/`description`/`apply` (its
`bothHave` guard, which fires ahead of the functor), where gen-merge right-biases them under the
stated rule above. So the divergence runs one way: gen-merge accepts field-colliding redeclarations
that nixpkgs rejects. Note that nixpkgs prints the **same** `already declared` text on both of its
paths, so the message does not tell you which one refused — the `str`/`str` case merging is what
separates them.

`overridden` is oldest-first and appears **only** where a declaration really was shadowed — a module
that merely adds fields (the `apply`-layering shape) leaves the record exactly what a plain field
union produces. A third declaration appends to the chain rather than replacing it.

### The tree-as-a-type is NOT mountable, and it says so

`(evalModuleTree …).type` is the seam that lets a parent tree nest a child (submodule recursion,
freeform). It is not an option type, and the rest of this section does not apply to it.

It used to be indistinguishable from one at a glance. It answered `name` and `merge` and nothing else
— the two fields that make a value **look** like an option type, which is not the same thing as the
ones a foreign engine reads first. Measured, the first protocol field a real nixpkgs `lib.evalModules`
forces is `getSubModules` (in `fixupOptionType`), and neither `name` nor `merge` is forced before the
abort. So handing the tree-type to a real `lib.evalModules` produced an error raised **inside the
consumer** (`attribute 'deprecationMessage' missing`, at a nixpkgs line), which the caller could not
catch and which named nothing about gen-merge.

Completing the protocol is the wrong repair, and this is a boundary question rather than a
compatibility one: the boundary is the **eval**, not the repo, and what crosses a gen boundary is
plain data — a mounted option type is neither, so completion would build the bridge the rule removes.
Making a tree genuinely mountable is crossing work and belongs on that chain. What lands here instead
is the mark plus the refusal, and nothing is deleted: the nesting seam is a shipped capability and
still works.

| field | disposition |
|---|---|
| `name`, `merge` | **implemented** — the nesting seam |
| `nonMountable` | **the mark.** Presence is the predicate (testing it forces nothing); the value carries the reason |
| `deprecationMessage` ⇒ `null`, `emptyValue` ⇒ `{ }`, `nestedTypes` ⇒ `{ }` | **answered, and true of a tree** — it is not deprecated, supplies no value for an undefined nesting option, and wraps no element type. These are the answers gen-merge's own readers already derived from absence, so nothing internal changed. `deprecationMessage` does one thing more: it closes the consumer's one remaining **direct** (non-`or`) read of this type, the read that would abort *uncatchably* rather than refuse. The refusal does not depend on it — with the field removed the mount still refuses catchably, because `getSubModules` is forced first and is read through `or` |
| `check`, `description`, `descriptionClass`, `functor`, `getSubModules`, `getSubOptions`, `substSubModules`, `typeMerge` | **refuse by name**, each naming the field the caller reached for |
| `_type` | **deliberately absent.** It is the one field a refusal would make worse: a consumer that ASKS (`lib.isType "option-type"` reads it through `or`) gets a correct `false` today, and a throwing tombstone would turn the one working negative answer into an abort |

`mergeTypes` fences the pair it consults: a non-mountable operand answers "not mergeable" **before**
`typeMerge`/`functor` are read, because "do these two types merge?" has a true answer here — `null`,
they do not — and returning it keeps the declaration stratum's own refusal, which names both types
and every declaring file.

**One thing inside gen-merge changes, and it is deliberate.** Forcing a parent's whole `.options` tree
*deeply* now refuses, because the nested tree-type sits in that tree and a deep force reaches its
refusing fields; before the mark the same force succeeded, the fields being merely absent. That is the
mark working rather than a casualty of it — a deep force of a declaration tree **is** a protocol read
of every type in it, and a value that answered would be a value that lied. The value side is
unaffected (`.config` still forces), an ordinary type's declaration tree still deep-forces, and
shallow reads of the tree-type still answer. Pinned by
`test-tree-type-refuses-a-deep-force-of-the-declaration-tree`.

Refusals are pinned in `ci/tests-error.nix` (`tree-type.*`), including a real nixpkgs mount and both
live controls: a completed leaf still mounts, and a tree still nests.

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
| `type-merge` | the same option loc declared **with a `type`** in more than one module | on the type the engines agree (both route the pair through the `typeMerge` functor and refuse on `null`); nixpkgs *additionally* refuses outright when both declarations carry any of `default`/`example`/`description`/`apply` (`bothHave`, ahead of the functor), where gen-merge right-biases those fields. The flag over-approximates on purpose — only the field-colliding pairs actually diverge |
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
