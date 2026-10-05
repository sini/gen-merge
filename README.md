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

*Byte-mode* names the design's one yardstick: nixpkgs `lib.evalModules` is the reference, and the
same modules must yield the same `config`, down to the priority-resolved winner at every option. Every
place gen-merge departs from it on purpose is listed under
[Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate).

## Layering

```
gen-prelude → gen-types → gen-merge → { gen-schema, gen-aspects }      (BELOW gen-resolve)
```

gen-merge is the *within-node* definition merge; [gen-resolve](https://github.com/sini/gen-resolve)
is the *cross-node* D>I>P schedule conductor — a distinct, higher layer. gen-merge builds on
gen-prelude (pure utilities), and takes gen-types' leaf checkers, gen-memo's reuse plane and
gen-scope's graph evaluator as **injected** values — one incremental plane, and one evaluator, for
the whole gen ecosystem. It drives no fixpoint of its own: the module tree is a single node on
gen-scope's evaluator and the self-referential `config` knot is an ordinary attribute there.

## Gen Ecosystem

| Library                                              | Role                                                                                                                                               |
| ---------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------- |
| [gen-prelude](https://github.com/sini/gen-prelude)   | Pure nixpkgs-lib-free utility base (builtins re-exports + vendored lib utils)                                                                      |
| [gen-algebra](https://github.com/sini/gen-algebra)   | Pure primitives (record, either, intensional identity)                                                                                             |
| [gen-types](https://github.com/sini/gen-types)       | Clean-room MIT structural type checker (leaf/poly checkers; `verify: v → null\|err`)                                                               |
| [gen-merge](https://github.com/sini/gen-merge)       | **This lib** — Byte-mode module merge engine (`evalModuleTree`, byte-identical to nixpkgs `lib.evalModules` over the priority subset)              |
| [gen-schema](https://github.com/sini/gen-schema)     | Typed registries (kinds, instances, collections, refs); re-hosted on gen-merge                                                                     |
| [gen-aspects](https://github.com/sini/gen-aspects)   | Aspect type system (traits, classification, dispatch); re-hosted on gen-merge                                                                      |
| [gen-scope](https://github.com/sini/gen-scope)       | HOAG scope-graph evaluator (demand-driven, \_eval memoization, circular attributes)                                                                |
| [gen-graph](https://github.com/sini/gen-graph)       | Accessor-based graph query combinators (traversal, condensation, phaseOrder)                                                                       |
| [gen-select](https://github.com/sini/gen-select)     | Selector algebra (pattern matching over graph positions)                                                                                           |
| [gen-bind](https://github.com/sini/gen-bind)         | Module binding (inject external args into NixOS modules)                                                                                           |
| [gen-dispatch](https://github.com/sini/gen-dispatch) | Relational rule dispatch STEP (stratified phases, conflict resolution)                                                                             |
| [gen-class](https://github.com/sini/gen-class)       | Class-share mechanism (partition / contract / apply / gate), byte-gated; its tier-2 fixed-input path rides this engine's `coreShortCircuit` kernel |
| [gen-memo](https://github.com/sini/gen-memo)         | The incremental plane — decides reuse, never evaluates (change propagation, AFFECTED set)                                                          |
| [gen-vars](https://github.com/sini/gen-vars)         | Pure-Nix vars/secrets (den-agnostic)                                                                                                               |

## The 7-item merge primitive

`evalModuleTree` reproduces exactly the primitive den's grammar/registry surface reduces to:

1. **typed options + defaults** — `mkOption { type; default?; apply?; readOnly? }`; a `default`
   desugars to a lowest-priority definition (no separate codepath).
2. **freeformType** — `lazyAttrsOf` / `attrsOf` routing of undeclared keys.
3. **per-key `name` + `_module.args`** binding under keyed collections.
4. **self-referential `config` fixpoint** — one local `fix` per call; `config._module.args.X = config` lets siblings cross-reference.
5. **`imports` as graph edges** — each tree's modules are nodes keyed by nixpkgs' key rule; a diamond or
   a repeated key is one node (`ci/tests/module-graph.nix`). A merge collects them by a breadth-first
   level walk that keys only keyed and path modules. The identity-keyed `genericClosure` is the graph's,
   built only when the graph is read, and checked node by node against the merge's list first.
6. **the `(loc, defs)` custom-merge escape hatch** — `mkOptionType { merge = loc: defs: …; }`. A
   descriptor stating `name` and no fold takes nixpkgs' constructor default (see
   [`mergeDefaultOption`](#mergedefaultoption--the-shape-directed-law-interim-exported-beside-mergeleaf)).
7. **`deferredModule`** — a lazy, import-usable module value, **never forced** by composition (handed
   opaque to the terminal). `functionTo` is intentionally omitted (consumers wrap guard functions as
   data).

## The priority subset

den + the gen corpus use only `mkDefault` / `mkForce` / `mkMerge` / `mkIf` (plus the implicit
`mkOptionDefault` behind a plain `default =`). gen-merge therefore implements **one** override rule —
lowest priority-number wins, ties merge — over the four anchor constructors (all instances of the
general `mkOverride N`) plus the two combinators `mkMerge` / `mkIf`. The exotic named overrides are
deliberately absent — zero uses across the surface. Equal-priority definitions merge in
**reverse module order**, byte-identical
to nixpkgs (observable in list-typed options: three modules contributing `[a]` `[b]` `[c]` merge to
`[c b a]`; a single module's `[a b]` beside another's `[c]` merges to `[c a b]`).

### The order pass

The nixpkgs **order pass** (`mkOrder` / `mkBefore` / `mkAfter`, plus `sortProperties` behind them) is
implemented, and it runs **last** of the three: discharge → `filterOverrides` → `sortProperties`. It
strips the order wrapper and then stable-sorts the surviving definitions by their order priority
(`mkBefore` 500, unmarked 1000, `mkAfter` 1500), so `mkBefore [ "a" ]` · `[ "b" ]` · `mkAfter [ "c" ]`
merges to `[ "a" "b" "c" ]` whatever order the modules were authored in.

It closes a **leak** as much as it adds a feature. An order marker is an attrset carrying `_type`, and
`dischargeProperties` — faithfully to nixpkgs, which has no `"order"` branch there either — matches
none of its three cases and passes the whole marker on as the value. With no pass to unwrap it, a
single `mkBefore "x"` reached a permissively-typed option as the literal
`{ _type = "order"; priority = 500; content = "x"; }`. The missing pass was the missing unwrap.

> ⚠ `priority` names **two different number lines**. `dischargeProperties` stamps the *override*
> priority (100 default, `mkForce` 50); the order axis is `defaultOrderPriority` 1000. nixpkgs'
> `sortProperties` overwrites the one field with the other and is safe only because the override pass
> has already run. gen-merge's plain defs arrive at the pass **already stamped**, so a verbatim port of
> nixpkgs' `strip`/`compare` reads the stamped 100 as an order key and sorts every plain def first
> (`[ "b" "a" "c" ]`). This implementation therefore sorts on its own `orderPriority` field and leaves
> `priority` meaning the override axis on both sides of the pass.

**The order vocabulary is compat surface, not gen's authority model.** gen expresses precedence by
graph position and provenance rather than by an integer priority lattice; these constructors exist
because gen accepts nixpkgs module vocabulary and a definition written in it must not leak its wrapper
into the value domain.

### `mergeDefaultOption` — the shape-directed law (INTERIM, exported beside `mergeLeaf`)

`genMerge.mergeDefaultOption loc defs` is the nixpkgs `lib.mergeDefaultOption` analogue: the law
nixpkgs applies where no *per-key* type was authored. It combines by the definitions' **runtime
shape** — one def ⇒ its value · all functions ⇒ applied **pointwise**, results merged by the same law
(this is not composition; a function is what nixpkgs' `lib.isFunction` accepts, so a `setFunctionArgs`
wrapper counts) · all lists ⇒ concatenated · all attrsets ⇒ `//`-folded, **shallow,
last-wins** · all bools ⇒ OR-folded · all strings ⇒ concatenated · all ints **and all equal** ⇒ that
value · anything else ⇒ a named refusal. **Only differing ints and type-heterogeneous definition lists
refuse**; differing bools and strings combine.

★ **It is an INTERIM surface and it does NOT replace `mergeLeaf`.** `mergeLeaf` remains the engine's
no-`.merge` default with its agree-or-refuse posture, and no existing consumer's merge semantics move.
The one route inside this library is `mkOptionType`'s default, below. It claims one law at one arm, never
whole-pipeline parity: nixpkgs' own `attrsOf`/`listOf` merge each key *through* the element type where
this law's attrset arm never consults it, so two definitions of `attrsOf (listOf str)` sharing a key
concatenate under nixpkgs and drop the first here.

★ **One declared divergence, in the multi-function arm.** nixpkgs writes that arm
`x: mergeDefaultOption loc (map (f: f x) list)` — passing raw values into a parameter whose first act
is `getValues`. For functions returning anything but an attrset carrying a `value` attribute it
therefore dies *uncatchably*; for functions that do, the stray `getValues` unwraps that field. Neither
is reproduced: the recursion here re-enters with each definition's value applied, which is what the arm
plainly means, and `[ (x: [x]) (x: [x+1]) ]` applied to `1` gives `[ 1 2 ]`. The terminal refusal is
the engine's one conflict text, naming every definition's file. Every other arm is byte-equal to nixpkgs' on
the same input, asserted against the live nixpkgs in `ci/tests/parity-surface.nix`.

**`mkOptionType`'s default is this law, with two arms kept as refusals.** nixpkgs' `mkOptionType`
takes `merge ? mergeDefaultOption`, so a descriptor stating `name` and no `merge`, `mergeDefs` or
`verify` folds here by the law above: lists and strings concatenate (equal strings too: `"a"`,`"a"` ⇒
`"aa"`), bools OR, equal ints pass. Two arms keep a named refusal, by the parity criterion ruled
2026-09-25 (take nixpkgs' value except where that value is silent): attrsets sharing a key whose
values are **not `==`**, which nixpkgs' shallow `//` settles by keeping the first file's value and
dropping the rest without a word, and functions (functors included, rendered `<a set>` in the conflict
text), where nixpkgs aborts or unwraps silently. Attrsets
with disjoint keys, or whose shared keys carry `==` values, are `//`-folded: `{ a = 1; b = 1; }`,
`{ a = 1; c = 2; }` ⇒ `{ a = 1; b = 1; c = 2; }`, nixpkgs' value, which 6a508e3 refused. "Equal" is
the running evaluator's `==` applied to each definer's own value, and nothing wider. Between
functions that is identity, which is sound (no evaluator accepts two different functions), so
`{ a = f; }`,`{ a = f; }` over one binding `f` is kept on Nix, Determinate and Lix alike, as is one
value passed to both modules through `specialArgs`; two distinct closures refuse on all three. The
evaluators split only where the definitions hold one function, or one value with an attribute that
throws when forced, in *different* value slots (a selection written at each site, a `_module.args`
module argument, …): that case, and why it stays, is under
[Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate). A functor is a function to
nixpkgs' `lib.isFunction`, so two functors refuse through the function arm, as two lambdas do. And
deciding a shared key forces its values, so `{ a = 1; b = 1; }`,`{ a = throw …; }` throws on reading
`.b`, where nixpkgs gives `1`. A descriptor stating `verify` is a gen leaf and keeps
`mergeLeaf`. Cells: `ci/tests/parity-surface.nix` (both engines) and `ci/tests-error.nix`
`mkoptiontype-default-merge`. The price is listed under
[Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate).

**The parity claim is watched live, not stamped.** Every law cell in `ci/tests/parity-surface.nix` runs
through `bothLaws`, whose `nixpkgs` arm calls `nixpkgsLib.mergeDefaultOption` at whatever rev
`ci/flake.lock` resolves, and asserts both sides against literal expected values — so an upstream change
to the merge law reds those cells on the property. `lib/` is nixpkgs-free, which is what makes that a
real comparison rather than a wrapper checking itself. A rev-stamp drift cell used to bind a stated pin
to the lock as well; it was retired 2026-09-22 by ruling, because it watched lock movement rather than
the law and a routine bump redded it with both laws byte-unchanged. What that gave up is notification
when the pin moves.

## Usage

```nix
let
  # All four are REQUIRED and none is defaulted — omitting one aborts at this call site naming it.
  genMerge = import (fetchGit "https://github.com/sini/gen-merge").outPath {
    prelude = genPrelude;
    types = genTypes;               # the leaf checkers
    memo = genMemo;                 # the one incremental plane's reuse DECISION
    scope = genScope;               # the one graph evaluator; this library drives no fixpoint
  };
  inherit (genMerge) evalModuleTree mkOption mkForce;
  t = genMerge.types;               # gen-types leaves ⊎ gen-merge structural strategies

  result = evalModuleTree { } [
    { options.name = mkOption { type = t.str; default = "anon"; }; }
    { name = mkForce "pinned"; }
  ];
in
  result.config                     # ⇒ { name = "pinned"; }
```

`evalModuleTree { specialArgs ? {}; check ? true; prefix ? []; coreShortCircuit ? false; warmFrom ? null; editedModules ? [] } modules → { config; options; type; provenance; undeclared; deprecations }`. `.config` is the merged output; `.options` is the merged descriptor map (introspection,
no nixpkgs eval); `.type` carries a `.merge` so a tree nests inside a parent tree (submodule
recursion) — and it is an option type named `submodule`, which a real nixpkgs `lib.evalModules`
mounts (see below);
`.provenance` is a lazy per-loc record of WHERE each value came from (see below);
`.undeclared` lists the definitions the eval did not merge into `.config` (see below);
`.deprecations` lists the declared options whose TYPE carries a `deprecationMessage` (see below).

Every function module receives `config`, `options`, and `prefix` (the module's option path, equal to
the `loc` at the enclosing `submodule.merge` call — `[]` at the root, `["sub"]` inside an option
named `sub`) in addition to any `specialArgs` and `_module.args` entries. The engine's three win over
an entry of the same name: a `specialArgs` key among them is refused by name, since the caller's value
would reach no module, and a `_module.args` entry of that name stays readable as
`config._module.args.<name>` but does not bind the formal. Inside a module, `config._module` carries
`args`, `check`, `freeformType` and `specialArgs`, as nixpkgs' does. `specialArgs` reads through a
re-declared `type` or `apply`, while the arguments a module receives stay the caller's set. A nested
tree's modules also receive
`name`, the last step of their position: `types.submodule` and the tree-as-a-type state it as
nixpkgs' `submoduleWith` does, an overridable `_module.args.name` definition. **That is the whole of the injected argument set, and it is the argument-side compat
boundary:** nixpkgs injects `lib` at every
`evalModules` level and gen-merge injects none, so a module reading `lib` is refused by name
(`` module argument `lib' is not defined ``) until the caller threads it through `specialArgs`.

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

A declared loc **nobody defined** has a record too: `{ defs = [ ]; winners = [ ]; priority = null; defaulted = false; }`. That holds whether or not its type has an empty value. The refusal "used but not
defined" belongs to the loc's VALUE and fires when `.config` reads it. This matches nixpkgs'
`definitionsWithLocations = [ ]`. `winners` reads more than the other fields: its order pass forces each
winning def's value to WHNF (`isOrderMarker`), so reading `winners` fires a declared
`default = throw …`, which reading `defs`, `priority` or `defaulted` does not.

## Priority bands

`priorityBand p` maps an override number to the band a contributor moves it at. `bandedLeaves scope result` maps every leaf of one `evalModuleTree` result to a record.

The bands follow the owner's ruling, on the numbers above:

| band      | priority       | moves                                                                         |
| --------- | -------------- | ----------------------------------------------------------------------------- |
| `force`   | below 100      | yes                                                                           |
| `set`     | 100 to 999     | yes                                                                           |
| `default` | 1000 to 1499   | yes                                                                           |
| `unset`   | 1500 and above | nothing; only option defaults survive here, and the receiver declares its own |

`bandedLeaves` is an attrset mirroring `provenance`, and it is lazy per loc. Reading one leaf costs what
reading its `provenance` record costs: one discharge and one priority pass over its defs, forced to
WHNF. It never forces the merged value. Each leaf is one of these records:

```nix
{ scope; loc; band; priority; winners; value; }                    # moves at `band`
{ scope; loc; reason = "unset: default-only"; priority; defaulted; } # priority 1500 or above
{ scope; loc; reason = "unset: no definition"; }                   # a declared leaf nobody defined
{ scope; loc; reason = "unset: freeform"; }                        # a leaf with no declaration
```

The classification happens before the priority is read, because two states carry `priority = null`. An
error raised while a leaf's defs are collected propagates from its record, and it is never read as
"no definition". `loc` is the path within `config`.

`scope` is the caller's. A result carries no contributor identity, so `scope` is stamped once per call.
Every other field is read from that one `result`. Whether `scope` names the contributor `result` was
evaluated for is decided by the caller that pairs them. gen-view's `headPositions` places the moved
records, and `joinedTrace` joins each contribution back to its record.

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
what it consumed is a different question from whether it checks — while a `freeformType` gates **this
level's own definitions only**, since there those definitions are merged and nothing was dropped. A
fully declared config reports `[ ]`. A `_module.<x>` the engine does not own (anything but `args`,
`freeformType`, `check` and `specialArgs`) is an ordinary unmatched path: `config._module.bogus = 1`
is listed as `[ "_module" "bogus" ]`.

**A nested tree's findings.** A leaf whose declared type carries `mergeDefs.reported` — a tree merged as a
type, `(evalModuleTree { … } modules).type` — reports the definitions *its own* eval did not merge, and they
surface here with their full absolute path (`nest.z`, or `sub.nest.z` at `prefix = [ "sub" ]`). Such a
finding is **never absorbed** by an outer `freeformType`: its key has an associated option (the
declared leaf `nest`), so it is outside the freeform domain (nixpkgs: *"merge all definitions that
don't have an associated option"*), and absorbing it would change a declared option's value. So it is
reported under every regime, and refused whatever `freeformType` is when the nested tree is strict: by
its own `check`, or because an evaluation carrying its report is at `check = true`. The refusal is the
owner's, at the owner's level, when that level is read (nixpkgs' per-level rule): reading `config.nest`
or deeper refuses, a sibling read does not, and neither does an `apply` that discards the nested value.
A lax tree under a strict carrier refuses as
`` gen-merge: option `nest.z' is not declared by the nested tree that owns it ``; a tree at
`check = true` refuses in nixpkgs' words, `` The option `nest.z' does not exist. Definition values: ``
followed by the one definition's `` - In `file': value `` line, the value pretty-printed as nixpkgs'
`showDefs` prints it (its first 5 lines, nested deeper than 10 as `"<unevaluated>"`; a value whose print
throws is omitted), then nixpkgs' `` Did you mean `x'? `` over the sibling option names and, where the
evaluation declares no option, its hint paragraph. That print renders deeper than gen-prelude's
`renderValue`, whose WHNF-only contract the conflict refusal keeps: a nested `abort`, missing attribute,
type error, infinite recursion or missing import in the misplaced value aborts the refusal, as in
nixpkgs, with nixpkgs' two trace lines naming the option and the defining file.
The domain is exactly
the leaves whose declared type carries `mergeDefs.reported`; a nested tree inside a wrapper (an `attrsOf`
of a moduleTree) has no report channel, so it refuses its own level's findings by name when that level
is read (see [the tree-as-a-type](#the-tree-as-a-type-is-not-mountable-bare-and-it-says-so)). Order: this level's own definitions first, then nested findings;
order is promised per key only.

Reading it forces **no definition value of this level's own**: the records carry names and originating
files only (the same data the freeform provenance records read), so an own-level def that is a bare
`throw` does not fire. That claim is about `.config`'s neighbours and this level's records; it does
**not** extend to a leaf whose declared type carries `mergeDefs.reported`, whose definitions the report
does force, since a nested tree's findings cannot be named without its key set. `path` is absolute
against `prefix`, naming the same location the orphan throw would.

It is **over-inclusive in the same way the freeform provenance records are**: a def wrapped in a false
`mkIf` still appears, because properties are discharged per key only inside the freeform `.merge`,
which this pass does not enter. This is the report↔refusal correspondence holding, not a leak —
whatever `check = true` refuses, `check = false` reports, and that same `mkIf false` def does throw
under `check = true`. Filtering it here would desynchronise the report from the refusal.

**Capture granularity.** A path is the first undeclared name on its branch, and the record covers that
loc *with everything beneath it*. Deeper rendering has no well-defined answer: with no declaration,
`config.nested.deep.key = "X"` and `config.nested = { deep.key = "X"; }` are the same definition, so a
descent could not tell a dropped option path from a dropped attrset value.

★ **One declared divergence from `lib.evalModules`, on this channel's leaf binding.** Deciding a
leaf's contribution to the list reads that leaf's **declaration** — `opts.<k>.type` — so that no
*definition* is forced to learn the answer.

**A strict parent over a lax nested tree refuses the nested tree's finding when the nested tree's
value is reachable from the read**, where nixpkgs admits it.
`test-a-lax-nested-tree-is-still-refused-by-a-strict-parent` pins it without a `freeformType`, and the
refusal holds under one too (`test-a-nested-finding-under-a-freeformtype-is-refused-at-check`): the
finding is outside the freeform domain. The refusal gate is the owner's effective strictness (its own
`check`, or a carrying evaluation's), and it fires at the owner's level, so a finding can be reported
and not refused. A sibling read, or an `apply` that discards the tree's value
(`test-a-strict-parent-whose-apply-discards-a-lax-nested-tree-reads-the-apply-value`), reads what nixpkgs
reads.

No level walks a nested tree's findings on its own WHNF, so **a leaf whose `type` is an expression
derived from this eval's own `config` is not a divergence**: it reads its value at `check = true`, typed
bare (`test-a-config-derived-bare-leaf-type-reads-at-check`) and wrapped in `attrsOf`
(`test-a-config-derived-leaf-type-is-a-declared-divergence`, which pins the wrapper shape), and so does
a nested `mkIf` reading the tree's own config
(`test-a-bare-tree-reads-a-self-referential-nested-mkif`), as in nixpkgs.

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
(evalModuleTree { } ty.getSubModules).deprecations
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

That makes cleanliness a **declared** fact rather than a derived one, and the reason is an argued
impossibility, not a convenience: what a function body reads from its argument is sealed in the
closure until it runs. **What would have to change** for the engine to derive it: apply each function
module with *only its named formals* (`intersectAttrs (functionArgs m) args`) instead of the whole
set. A hidden `config` read then fails loudly (`attribute 'config' missing`) instead of succeeding
silently, so the formals become the module's complete read set — a module whose formals name no
fixpoint-derived argument is clean by derivation, and `pureModule` becomes checked rather than
trusted. The price is nixpkgs application parity for `args@`-capturing and bare-lambda modules, which
is why the engine keeps the whole-set application and function modules stay dirty by default.

### The `pureModule` contract

```nix
genMerge.pureModule ({ genSchema, ... }: { options.x = genSchema.mkThing; })
# ⇒ { __pureModule = true; __functor = self: <the fn>; }   (classifies "marked-pure")
```

`pureModule f` wraps `f` so the marker is readable **before** `callM` applies it (a bare function's
cleanliness is invisible once applied). The author asserts, and the engine **trusts**:

1. `f` reads **only its declared formals** — no `config` / `options` capture.
2. **every formal resolves from `specialArgs`** — not from `config`/`options`, and *not* from
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
  warmFrom      = prevResult;     # the PREVIOUS evalModuleTree result (its config/provenance/freeform ARE the memo)
  editedModules = edited;         # the APPENDED module list
} (base ++ edited)                # the full list
```

Default (`warmFrom = null`, `editedModules = [ ]`) ⇒ **zero behaviour change**: the decision is never
forced, every leaf takes the cold merge, freeform re-merges cold (the `coreShortCircuit` precedent —
an opt-in knob with a documented firing contract). Warm is the reverse-cone reuse of adios's
`mkOverride`, but sound under gen-merge's config *fixpoint* (adios has none).

**Firing.** The engine takes the EDITED entries from its OWN identity-keyed closure (`closeModules`
over the tree's top-level elements, never a caller count, since `imports` expansion is
config-dependent): they are the nodes the edited roots reach, paired with the merge's list after a
node-by-node agreement check. A list that imports nothing keeps its edited entries as its tail. The closure is breadth-first, so an appended module's imports are no tail of the full closure,
and the entries are partitioned by ORIGIN. Warm is REFUSED (cold fallback, `reason = "an edited module reaches a module node the base also reaches (warm refused)"`) when a node is reached from both a base
root and an edited root, since it has no single origin. Warm is also REFUSED (cold fallback, stated in the
trace) when any edited entry carries `disabledModules` (it would disable a clean base module invisibly
to the footprint) — defence only; unreachable through `evalModuleTree` while module removal is
refused, since the module reader refuses `disabledModules` by presence on its first read, before any
warm decision (see
[Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate)). Warm is also REFUSED (cold
fallback, `reason = "check differs from warmFrom's (warm refused)"`) when `warmFrom` was evaluated under
a different effective strictness, or records none, as a result from an evaluator that predates the
`strict` field does: every reused leaf reads the prior's `config`, whose refusals are the prior's
regime's. With that clause a warm evaluation equals the cold one across a change of `check`, under the
warm plane's standing assumption that `specialArgs` are unchanged between evaluations (below): a nested
tree whose own `check` is derived from a `specialArg` changes underneath a warm evaluation invisibly,
as any other `specialArg`-derived value does. Whether an override *reduces* to a modules-append at all is the caller's call
(the `override` handle — the hub's `lib.compose`, formerly gen-flake's); the engine just splices when handed a `warmFrom`.

**The contribution relation (the FACT) and gen-memo's decision.** A module entry is
CLEAN (`srcClass` attrset / marked-pure — config-independent), DIRTY (function, `srcClass` dirty), or
EDITED (in the appended tail). gen-merge computes only the FACT: a bipartite contribution relation
between DIRTY ∪ EDITED entries and the declared-leaf locations they touch, built from

- their **decl paths** (`declLeafPaths` of the entry's own `options`), and
- their **def paths** landing on a declared leaf (`moduleDefFootprint` — the portable-lint's
  discharge-based descent, recording PATHS not values: it pushes config-node properties down at each
  declared-group level and stops at a declared leaf or an undeclared key, **never forcing a leaf
  value** — only the config spine, bounded by the module's structural size, which a dirty/edited module
  re-merges anyway).

Each declared-leaf location is keyed by the injective `builtins.toJSON path` id (a dot-join display
name collides — `["a.b"]."c"` and `["a"]."b.c"` both read `"a.b.c"`). gen-merge hands this relation to
**gen-memo** (`memo.warmDecision`, the incremental plane's one reuse DECISION for the whole gen
ecosystem — gen-merge decides only ADMISSION (whether warm participates at all: the
`disabledModules` refusal above — defence only; unreachable through `evalModuleTree` while module
removal is refused —, the regime key above, which keeps a prior of a different effective strictness
cold, and the freeform reuse gate below), never the per-location REUSE
verdict, which is gen-memo's `isClean` alone; otherwise gen-merge only reports what an entry can
perturb). A declared
leaf is **REUSABLE iff gen-memo's `isClean` admits its location** — sound whenever the relation is
complete, since an admitted location's decl set and def set come only from CLEAN modules (constant
attrsets, or marked-pure modules applied with unchanged `specialArgs`), so its inputs to the merge are
identical to the previous eval and the value/provenance are byte-identical.

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

**A moved minted identity is refused, not re-composed.** A warm `.config` read throws
`gen-memo.identitiesHeld: minted identity moved … at '<coordinate>'` when the edit moved an instance's
`id_hash` (the option-set closure; cold emits the same moved identity, so there is no correct
fallback). The walk that finds instances (`identityMapOf`) decides membership from the DECLARATION: an
instance is a position whose declaration declares an `id_hash` option, and only that `id_hash` is
forced, so an undefined or throwing leaf nobody reads stays unread warm, as cold. **A minted instance
must sit at a position whose declared type carries identity; an identity in an untyped slot is not
tracked by the warm plane** — an `id_hash` value at a `raw`/`anything` leaf, as an element of
`attrsOf raw`, as a member of an `either`, below a terminal leaf, or in the freeform layer. **A typed
position the walk cannot place is not tracked either**, and that is a boundary of its own, not a member
of the untyped list: below a type that carries an element but states no position for it, nothing says
whether the type adds a path level, so the walk stops rather than guess. Only a gen type's `recarry`
states that position. Two kinds of record state none: a record that crossed stating its own merge
relation and no rebuild (a refinement over a nixpkgs wrapper or container), and **every raw nixpkgs
record carrying an element** (`listOf`, `nonEmptyListOf`, `attrsOf`/`lazyAttrsOf`/`attrsWith`,
`attrListOf`, `nullOr`, `uniq`, `unique`, `addCheck` over one of those, `functionTo`), because its functor
payload is what it offers to merge on, and the walk does not read a payload to learn what a type
carries. A moved identity there re-composes warm, equal to cold, rather than being refused: the refusal
given up would have fired only where warm already equals cold. A raw record carrying a module set
(nixpkgs' `submodule`, and `addCheck`/`coercedTo` over one) states it in `getSubModules` and is walked
at its own position when its declaration places that set at its position: some option record its
`getSubOptions` hands back is stamped with a `loc` equal to the position followed by its own path.
`getSubModules` says which set a type is built from, not where its instances sit, so a container
forwarding its element's set (`listOf`, `attrsOf`, `attrListOf`, `functionTo`, and `coercedTo` over
one, stock or with `nestedTypes` stripped) is served warm, equal to cold, and so is a hand-written
`getSubOptions` whose records state no `loc`. A `getSubOptions` that is neither a function nor a
functor states no declaration. nixpkgs' `deferredModuleWith` whose static modules declare `id_hash`
places them at its position, yet holds a module there, which no declaration field says: the warm read
refuses it by name (`the warm identity walk reads the option as an instance …`, at the door and the
option) where cold serves. A nesting seam (a tree type) is not walked either, as a leaf or as a
container's element. The byte oracle still compares those values; the refusal does not see them. A gen wrapper
that adds no path level (`nullOr`) holds its instance at its own position. Pinned by
`test-identity-outside-the-declaration-stratum-is-not-a-minted-identity`,
`test-identity-wrapper-without-a-path-level-holds-its-instance-in-place`,
`test-72izy-warm-config-read-forces-no-undeclared-identity` and `test-the-walk-reads-no-raw-payload`.

**The decision trace.** Every result carries `.warmDecision` (always-on data; `mode = "cold"` on a
plain compose):

```nix
{
  mode     = "warm" | "cold";                     # ADMISSION: cold = the fallback fired (reason stated)
  inert    = <bool>;                              # warm admitted, but no non-edited module is clean ⇒ reuses nothing
  reason   = <string|null>;                       # why cold (no warmFrom / check differs from warmFrom's / disabledModules refusal — defence only; unreachable through evalModuleTree while module removal is refused)
  strict   = <bool>;                              # the effective strictness this result was evaluated under; the next warm admission reads it
  reused   = [ <loc-string> … ];                  # the spliced declared leaves (dot-joined)
  remerged = { <loc-string> = <reason>; };        # "edited-def" | "dirty-def <file>" | "dirty-decl <file>" | "freeform-dirty <file>"
  modules  = { clean = [ file… ]; dirty = [ … ]; edited = [ … ]; };   # the classification
}
```

**Laziness contract.** `mode` / `inert` / `modules` are cheap (classification only). `reused` /
`remerged` are `O(declared-locs)` spine-forcing when read (they enumerate the loc partition — never leaf
values). This is adios's "what was reused vs re-evaluated," delivered as data.

**`mode` is admission, `inert` is the cheap reuse verdict.** `mode = "warm"` says the warm path was
taken; it does not say anything was reused. A base made only of function modules is admitted warm and
reuses nothing, because every function module is dirty (above). `inert = true` says exactly that
without walking the loc partition: warm was admitted and `modules.clean` is empty, so every declared
leaf is declared by a dirty or edited module and re-merges. The implication runs one way —
`inert = false` does not promise reuse (a clean base whose every leaf the edit touches reuses nothing
too); only `reused` answers that, at its spine cost. On a cold result `inert` is `false`: `mode`
already says nothing was spliced.

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
  `either`, `raw`, `anything`, plus `mkOption` / `mkOptionType` / `deriveType`.
- from gen-types (verify-only leaves): `str`, `int`, `bool`, `enum`, `path`, `union`, `refined`, …
  (the merge-bearing gen-merge versions of `listOf`/`attrsOf` win in the union).

**`anything`'s fold.** Lists concatenate (reverse definition order). Attrsets recurse per key, and a
conflict names the full path (`` `o.svc.k' ``). Anything else takes `mergeLeaf`, the engine's
agree-or-refuse leaf fold, which is also `raw`'s. **An attrset carrying `__mint` is carried whole**
when every definition carries it: it takes `mergeLeaf` too, so one definition passes through as it is,
several pass if all are `==` to the first, and a conflict is refused at the option itself
(`` `o' ``). `__mint` is the mark a substrate constructor writes (a gen-types checker or refined type,
a gen-schema kind, a gen-algebra intensional value). A rebuild would keep a digest but move every
closure into a fresh Value cell, so a value whose identity is DECIDED by `==` over its record would
stop equalling itself on upstream Nix and Determinate. Carried whole, a transported construction is
the same value on all three evaluators. Definitions mixing marked and plain attrsets are rebuilt.

The carry fold's stated costs, all of them `mergeLeaf`'s:

- **Twins are refused.** Two independent constructions of one identity (one digest, distinct
  closures) are `==`-unequal, so defining both at one `anything` slot refuses the whole value, where
  the rebuild returned one whose digest read cleanly. One value defined twice still folds to it.
- **Two definitions of one sealed value split as `raw` does.** A sealed gen-types type carries
  throwing fields, so `==` reaches a throw on upstream Nix and Determinate and short-circuits on Lix;
  `anything` and `raw` give the same answer on every evaluator.
- **A cyclic value overflows.** A hand-written `__mint` on a freshly built cyclic value, defined
  twice, sends `==` round the cycle and overflows the stack uncatchably: the cyclic-value exception
  in [Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate), extended to whole
  attrsets.
- **Unmarked values are still rebuilt.** A value carrying no `__mint` takes the per-key rebuild, so
  its compared parts do not survive transport: a gen-merge composite (`attrsOf int`) carried through
  `anything` gives `typeEq` `false` on upstream Nix and Determinate (Lix `true`), and so does `==`
  on `{ f = g; }`. This residue is enumerated, not decided: gen-merge's composites carry no
  `__mint` yet.

**The `types` argument is the gen-types library**, bound by its roster key, and not a pluggable leaf
vocabulary. The core builds every exported type through gen-types' check-witness protocol
(`witnessRecord`, held to `witnessedCheck`) and reads every fold's witness by it (`rewritesCheck`),
so a `types` without the protocol is refused by name at construction:

```
gen-merge: declares a `types' with no `rewritesCheck', `witnessRecord', `witnessedCheck' — the `types'
formal is the gen-types library, whose check-witness protocol every type this library exports is built
and read through (a gen-types older than that protocol lacks them)
```

A nixpkgs `lib.types` value is still accepted wherever a type is, as a foreign value at an option
(below). It is never the vocabulary: the foreign-vocabulary mode `types` once documented is
withdrawn, and a consumer that needs one gets a parameter of its own, not this slot. The namespace carries the three protocol names beside the leaves.

## The protocol boundary — `lib/interface.nix`

**A type says what it is in gen's own words. The nixpkgs `optionType` protocol is spoken in exactly
one unit, and a type acquires it by being EXPORTED through that unit.**

Cardelli 1997 calls the object at a fragment collection's boundary its **interface** — "a linkset is
a collection of named judgments plus an interface", and that interface is "the external interface of
the entire linkset". Definition 5-1 names the two halves this unit holds: the **import environment**
and the **export environment**. So do its functions.

|                |                                                                                             |
| -------------- | ------------------------------------------------------------------------------------------- |
| `exportType`   | a gen type expressed in the foreign protocol — "the type exported by the fragment"          |
| `importType`   | a foreign record read back as a gen type, or a named refusal — "the type of the `f` import" |
| `exportFields` | the fourteen names the foreign protocol reads, as this unit's private data                  |

The two vocabularies, kept apart on purpose:

| gen-native            | what it is                                                            | the foreign field(s) it derives                     |
| --------------------- | --------------------------------------------------------------------- | --------------------------------------------------- |
| `name`                | the type's name                                                       | `name`, `description`, `descriptionClass`           |
| `verify` / `admits`   | value predicate (`v -> null \| err`) / domain predicate (`v -> bool`) | `check`                                             |
| `mergeDefs`           | definition fold, `loc -> defs -> value`                               | `merge`                                             |
| `whenEmpty`           | what it is worth when nobody defined it                               | `emptyValue`                                        |
| `carries` / `recarry` | what it wraps, by ROLE, and how to rebuild over another               | `nestedTypes`, `getSubModules`                      |
| `unroledNested`       | an imported record's `nestedTypes` keys that name no role, verbatim   | `nestedTypes`                                       |
| `substructure`        | `{ declares; modules; rebuild; }`                                     | `getSubOptions`, `getSubModules`, `substSubModules` |
| `typeMergeRel`        | the **row-free** type-merge relation (one carve-out, see below)       | `typeMerge`, `functor`                              |
| `deprecated`          | the deprecation message, if any                                       | `deprecationMessage`                                |

`exportType` publishes a **partition of the fourteen** as data (`exportClasses`), so it can be read
rather than argued: **11 DERIVED** (a real translation from a differently-named gen datum;
`descriptionClass` is derived from `phraseClass`, the name and what the type carries), **1
FOREIGN CONSTANT** (`_type` — no counterpart exists on this side, which is the point), **2
NAME-CARRIED** (`name`, `description` — carried from the name, translating nothing, which is why
those two are allowed to be the same word on both sides and the eleven are not).

### What "ceremony" would look like

The boundary was licensed conditionally: build it, and if it turns out to be ceremony, collapse it
back into gen-merge. Four predicates make that condition readable — any one holding fires it — and
each produces a value in `ci/tests/interface.nix` rather than an opinion:

|         |                                              |                                                                                                                                     |
| ------- | -------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| **C-1** | the unit only forwards                       | count the classes; a FORWARDED class appearing, or DERIVED falling to or below FOREIGN CONSTANT                                     |
| **C-2** | a field set with no translation              | a derived field satisfied by reading a gen field of the **same name**                                                               |
| **C-3** | the boundary is crossed one direction only   | `importType` absent, or present and unreachable from the engine's type merge                                                        |
| **C-4** | the engine still speaks the foreign protocol | hand `mergeTypes` two gen-native types carrying no foreign field; it must return a merged type (`ci/tests/type-merge-relation.nix`) |

What does **not** fire it: that the unit is small; that few types cross today; that two of the
fourteen are constants. Ceremony is *translation that translates nothing*, never *a small
translation*.

### `defineType` — the crossing site, and there is one of it

`lib/types.nix` builds every type through `defineType`, which is `exportType` over the gen record.
The same value therefore carries both vocabularies, and that is **forced rather than convenient**:
the published `types` namespace is the drop-in a foreign module system mounts, and the type a
consumer writes there is handed to this library's own fold as readily as to a foreign one. What the
boundary buys is not that the two vocabularies live in different values — it is that only one unit
knows how to get from the first to the second, and that everything above states itself in the first
alone. `mkType` builds the gen record **without** its foreign expression: usable by this engine,
and it does not pay for the protocol (`ci/bench/interface-cost.sh` measures the difference in
`nrThunks`).

### `deriveType` — a type derived from a completed one

Published as `types.deriveType` and as top-level `deriveType`, one value under one name; name and
placement owner-ruled 2026-10-01.

```nix
deriveType {
  key = { … };                    # default null: plain data two derivations of one `id` must agree on
  fields = b: { __tag = "t"; };   # default `_: { }`: metadata, a function of the base it applies to
  name = "…"; description = "…";  # default: the base's
  mint = { minted = …; };         # default sealed
} "tagged" base                   # the `id` (required: the derivation's merge identity and functor
                                  # name), then the base; the options are closed, refused by name

```

**Why not `base // { … }`.** A completed type is a fixpoint: `defineType` ties the knot once, and
its relation, `typeMerge` and `functor.type` are closed over it, while `recarry`,
`substructure.rebuild` and `withArgs` are closed over its constructor. `//` changes the record and
leaves every one of those answering for the base — the copy merges with itself to its base, is
absorbed by its base when both are declared, rebuilds to its base and mints as its base — while
its check and fold stay right, so nothing a value reaches says so. `deriveType` applies the delta
**before** completion instead: the base's behaviour fields cross into a source record, the delta and
the datum `__derivation = { base; read; id; key; }` (`read` is the base as the import boundary
reads it) are added, and `defineType` completes it. Its relation
merges only a derivation of the same `id` and `key`, answering the bases' own join (through
`mergeTypes`) derived again; `recarry`, `substructure.rebuild` and `withArgs` derive their result
again. No protocol field is stated by hand, the phrase included: a derivation stating no
`description` is described by its base's phrase, rendered from `read` within the export's node
budget and costing one node, so a type whose cycle closes through the derivation
(`d = deriveType { … } "d" (nullOr (oneOf [ str (listOf d) ]))`) has a finite phrase, docs and refusals,
as the same shape without the derivation does. Which field of the base goes where is
`interface.deriveClasses`, and `ci/tests/derive-type.nix` fails by name on a field no class names.

**A `//` copy's rebuild is read off a witness.** A copy states its rebuild in one of two fields and
carries the other from its base: `substSubModules` in nixpkgs' words (gen-schema's `refined`), or
`substructure.rebuild` in gen's. `exportType` builds the rebuild once with gen-types' `witnessRecord`
and publishes it twice, as `substSubModules` and as `_substSubModulesWitness`, the construction of the
check witness below. The import boundary takes a stated `substSubModules` as the copy's rebuild
exactly when it no longer holds its witness, and the copy's `substructure` otherwise, so the layer
the author stated survives in either field (`decl-merge.test-redeclared-wrapper-over-nesting-keeps-its-layer`,
`decl-merge.test-copy-stating-its-rebuild-as-substructure-keeps-its-layer`). The rebuild is mounted
in both directions: by gen's redeclaration fold, and by nixpkgs' `fixupOptionType`, which calls the
outer type's `substSubModules` on **every** option whose type states a module set, declared once or
more. A stated `substSubModules` that answers no option type (`null`, a bare attrset) is refused by
name where gen's evaluation rebuilds it, and aborts in `lib.evalModules` as it does over a nixpkgs
type; the base's rebuild no longer serves it silently.

The derivation keeps its base's `name` by default, the value vocabulary its messages speak. Its
identity is `__derivation.id`, which every gen relation reads through `interface.keyOf` and which
`exportType` publishes as `functor.name`, so neither a gen relation nor a foreign `typeMerge`
absorbs it into its base. A foreign base (a nixpkgs type) crosses the import boundary first.

**Refusals, each by name:** a base that is not a completed option type (a constructor, a `mkType`
record, an option descriptor); `fields` setting anything but metadata — a type whose behaviour or
relation differs is a new type (`mkOptionType`); no string `id`; a `key` holding an option type,
which Nix `==` cannot compare totally (key a derivation by plain data).

**Identity.** A derivation never inherits its base's mint. With no `mint` it is sealed:
`typeEq` compares the reified value, and `__id` is the named refusal. A caller that passes a
`mint` owes a preimage covering the `id`, the `key` and the base's identity; one that omits the
`key` mints two different derivations as one.

**The name.** "Derive" is Bracha & Cook 1990 §2.1's word for this operation — inheritance as
"incremental derivation", `C = Δ(P) ⊕ P` with the delta parametric in the parent (hence `fields`
takes the base) — and it pairs with `defineType`. That `self` is then re-bound is Cook 1989's
account, which Bracha defers to; it is cited, not read, and the ground here is `mkTypeWith`'s own
knot and the cells. The hub's TERMINOLOGY already registers **Derive** for gen-schema's
`mkInstanceRegistry` `derive` hook, a post-validation enrichment of a registry's VALUES. This is a
second meaning, kept because the two sorts never meet: that one is a hook field on a registry, this
one a type constructor over a TYPE, and neither is reachable where the other is.

**Costs and residues.**

- One completion per lift: a merge, a `recarry` or a rebuild of a derivation re-completes it, so N
  derivation levels pay N completions and N relation frames, as gen-schema's `refined` does. The
  hub perf-bench constructs no derivation, so it says nothing about this cost.
- A foreign CONTAINER base (`lib.types.listOf …`) crosses the import boundary with no constructor to
  rebuild it over, and the vocabulary refuses it by name — the inherited round-trip residue. A
  foreign leaf derives.
- A derivation OF a consumer type whose relation keys on an inherited marker field is absorbed by
  that type: gen-schema's `refined` decides by `partner ? __schema`, which a derivation of a
  refined type inherits, so `mergeTypes R (deriveType { … } "id" R)` and the foreign `R.typeMerge` answer
  `R`. Separation holds over bases whose relation reads identity through `keyOf`; it closes for
  `refined` once `refined` is itself a `deriveType`.

### The import environment is PARTIAL, and its refusal survives the namespace assembly

`importType` answers `{ imported = …; }` or `{ refused = "<reason>"; }` — handed a record that carries
an element type or a module set while answering only part of the sub-protocol, it computes W4a's
refusal by name. **That refusal is propagated at every site that consumes it**, including the one
where it is least visible: `lib/default.nix` assembling the published `types` namespace out of the
injected leaf vocabulary. Swallowing it there published a protocol-incomplete record into
`lib.types`, where a mounting consumer dies inside the foreign engine on a missing attribute — the
uncatchable, unnamed abort this boundary exists to convert into a refusal. A computed refusal
thrown away is worse than one never computed.

The `types` parameter is this library's **uncontrolled input** — it means the gen-types library, and
a caller may hand it any record carrying the check-witness protocol — so "the shipped roster does not
trip it" is not a reason to swallow. Being total over that input is the whole reason the import environment refuses
rather than doing its best. Refusal is **per name**: the namespace is lazy, so a bad entry refuses
when forced and every other name still publishes.

What the assembly checks of the vocabulary, and no more: that it is an untagged attribute set (a
null, a list, or a tagged value such as a flake's outputs refuses by name), that it carries gen-types'
check-witness protocol and that the protocol agrees with the test gen-merge restates inline (both at
construction; the agreement door is stated with the witness, below), that each
type-shaped member imports as above, and that every name it shares with gen-merge's strategies is
declared in `lib/types-allowlist.nix`. Beyond the protocol, which names it carries is not judged: a
record whose overlap with the strategies is allowlisted publishes whatever subset of names it carries
— the protocol plus `{ inherit (lib.types) str int bool; }` publishes those three beside the
strategies (`ci/tests/linkset.nix`, a fixture of the assembly's totality, not a supported wiring).
A name it shares undeclared with the strategies refuses **per name** too: it answers with the
linkset's named refusal when demanded, and every other name still publishes, so the protocol plus
`{ inherit (lib.types) str nullOr; }` publishes `str` and `listOf` and refuses at `nullOr`. nixpkgs'
entire `lib.types`, which carries no protocol, is refused whole at construction. The allowlist is gen-merge's own declaration, so an entry is stale
only when it names nothing gen-merge exports; an entry naming a name the vocabulary lacks is
inapplicable, and whether the shipped gen-types still collides at each entry is a CI cell.

## The nixpkgs `optionType` protocol

Every type in the `types` namespace carries the full **14-field nixpkgs `mkOptionType` shape** —
`_type`, `name`, `description`, `descriptionClass`, `deprecationMessage`, `check`, `merge`,
`emptyValue`, `getSubOptions`, `getSubModules`, `substSubModules`, `typeMerge`, `nestedTypes`,
`functor` — derived at the boundary above, except where the record stated its own relation and that
pair is retained and republished, so the SAME type value serves both engines. This is what
lets gen-schema inject gen-merge-typed options into an instance submodule that a **nixpkgs**
`lib.evalModules` evaluates (the corpus path: `mkInstanceRegistry` inside flake-parts). Pinned by
`ci/tests/nixpkgs-protocol.nix`.

The scope of that sentence is the `types` namespace, and there is exactly one type-shaped value
outside it: an eval result's `.type`, which is a nesting seam and must NOT mount. It is covered
below.

The protocol has two halves. The **merge** half (`merge`, `emptyValue`, `typeMerge`) says how defs
combine; the **introspection** half (`getSubOptions`, `getSubModules`, `substSubModules`,
`nestedTypes`) says what a consumer can learn from a type *without any value* — how a documentation
generator, an LSP, or a registry-reflecting consumer reads a DECLARED surface.

`getSubOptions prefix` returns the option records one submodule level down. gen-merge states this as
its `substructure.declares`, and the boundary derives the foreign field from it — the rules are
nixpkgs', the vocabulary is gen's:

```nix
# submodule
declares = prefix: (evalModuleTree { inherit prefix specialArgs; } modules).options;
# attrsOf / lazyAttrsOf
declares = prefix: (subOf element).declares (prefix ++ [ "<name>" ]);
# listOf
declares = prefix: (subOf element).declares (prefix ++ [ "*" ]);
# nullOr — pass straight through, adding NO segment: a nullable introduces no path level
declares = (subOf element).declares;
```

`subOf` asks the protocol boundary what an element's substructure is, so an element speaking either
vocabulary answers the same question. gen-merge's `submodule` reads `.options` off the same nested
`evalModuleTree` its fold builds, with no defs supplied, so the introspection and merge halves cannot
disagree about what a submodule declares, and nothing an instance authored is forced. A **leaf** type
has no sub-options and returns `{ }` — the leaf answer the boundary supplies for a type that states
no substructure, which stays correct for every non-structural type.

Two types report `{ }` **correctly**, and should not be "fixed" into reporting something else.
`deferredModule`'s sub-options in nixpkgs are its `staticModules`; gen-merge ships no
`deferredModuleWith`, so that set is empty by construction. And an element that is not
protocol-complete — a gen-types **parametric** leaf (`enum`, `struct`, `union`) reaches the unified
namespace as a bare constructor and is never completed — declares no sub-options either, so a wrapper
reports `{ }` rather than aborting on a missing attribute.

#### The module-set half: `null` and `[ ]` are two different answers

`getSubModules` reports the module set a type carries, and it distinguishes **not having one** from
**having an empty one**:

| answer  | means                                                                                  |
| ------- | -------------------------------------------------------------------------------------- |
| `null`  | this type has no sub-module concept at all — a **leaf**'s answer                       |
| `[ ]`   | this type has a module set and there is nothing in it — `deferredModule`               |
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

### The sub-protocol is a REQUIRED FORMAL of a structural type

The three answers that say what a type **wraps** are one answer — `substructure`'s
`declares`/`modules`/`rebuild` in gen's words, `getSubOptions`/`getSubModules`/`substSubModules` in
the foreign protocol's — and a type that states none of them gets a **leaf's** answers
(`_prefix: { }`, `null`, `_m: null`). Those are right for a leaf and wrong for every type that wraps
another: a wrapping type left on them reports *"declares nothing"* indistinguishably from a type that
genuinely declares nothing, so a consumer reflecting a declared surface off it fails **closed and
silently**. One default cannot be right for both, so a type that **carries** something answers all
three itself or is **refused at construction**, by name, listing every field it did not supply.

The rule has **two arms, one per vocabulary**, and the refusal speaks the vocabulary its author wrote
in — a `mkOptionType` caller wrote `substSubModules`, not `rebuild`, and a message naming the field
they did not write would send them looking for the wrong thing:

```nix
gm.mkOptionType {
  name = "rackOf";
  elemType = t.str;
  getSubOptions = _prefix: { };
  getSubModules = null;
}
# ⇒ throws: gen-merge: the structural type `rackOf' carries an element type but does not supply
#           `substSubModules'; a structural type may not inherit a leaf's protocol answer
```

```nix
# the same rule at the gen-native constructor, in gen's own words
genMergeVocab.mkType {
  name = "crate";
  carries.element = t.str;
  recarry = c: c.element;
  substructure = { declares = _prefix: { }; modules = null; };
}
# ⇒ throws: gen-merge: the structural type `crate' carries a parameter but does not supply
#           `rebuild'; a type that carries something answers for it rather than inheriting a
#           leaf's answers
```

**A type that declares a ROLE owes a fourth formal, `recarry`,** required on the same terms. The
boundary reads it to rebuild the type over another payload wherever it **derives** the relation —
except where the record stated its own, which is answered by that instead and is never rebuilt this
way — so a carrying record without one that is not answered for otherwise would construct, export,
and then detonate with a bare missing-attribute error the moment a foreign engine applied the
functor — an interpreter abort naming neither the type nor the field.
The requirement is scoped to the **role**, not to carrying in general: `deferredModule` carries a
module set through its `substructure` without declaring a role, so it has no payload to be rebuilt
over and owes none.

The missing declaration is the design choice; making the field required makes it total.

**The domain is what the type carries** — a property of the constructor, read off the descriptor rather
than off any measurement. What a type carries has one source: the same reading (`statedRoles`) decides
this refusal's domain and fills the imported record's `carries`. A functor payload is what a type
offers to **merge** on, never what it carries: the container relations read a partner's payload, whole
and in its role's shape, and nothing else reads it — the identity walk included, which reads a raw
foreign record's element through `statedRoles` and finds no position for it there. A record that carries
something and states no merge relation (`functor.binOp`) is refused by name at import. Two ways a
descriptor says it carries something:

| the descriptor carries                                                                    | the test      | who is in                                   |
| ----------------------------------------------------------------------------------------- | ------------- | ------------------------------------------- |
| an element type — `elemType`, or nixpkgs' `nestedTypes.elemType` spelling                 | `statedRoles` | `listOf`, `attrsOf`/`lazyAttrsOf`, `nullOr` |
| a module set — `getSubModules`, the protocol's own field for one, supplied and non-`null` | `statedRoles` | `submodule`, `deferredModule`               |

The `nestedTypes.elemType` arm is **load-bearing rather than defensive**: `nullOr` carries its element
only there, so without it `nullOr` would escape its own rule. Disjunct **order** is load-bearing too —
`||` short-circuits, and a container's `getSubModules` IS its element's, so reading it to decide the
domain would force the element type at construction. An element-type carrier is settled first.

**Presence is what is missing, not value.** The domain test reads `getSubModules != null` — a supplied
list, empty or not, is a module set, and `null` is the leaf's *"no such concept"* — while the refusal
tests `t ? f`. So `getSubModules = null` is a **supplied answer**, which an `attrsOf` over a leaf
element legitimately gives, and only absence is refused.

Everything else is outside **by the domain**, not by a carve-out:

- a **leaf** carries neither;
- `either`/`oneOf` carry **members**, not an element. They introduce no path level, `{ }` is their
  answer on nixpkgs too, and their pair lives in the functor payload, which the domain check does not
  read;
- `deferredModule` is **inside** the domain by the module-set arm — its set is empty by construction
  and it answers all three itself, including the rebuild (above). Requiring it to *propagate* an
  element is a different demand and still refused: that would mean synthesising a parameter the
  constructor does not have.

`listOf`, `attrsOf`/`lazyAttrsOf` and `nullOr` then supply the triple from their element:
`getSubModules` is the element's, and `substSubModules` rebuilds **this** container over the
substituted element, keeping its own name so the `attrsOf`/`lazyAttrsOf` distinction survives a
substitution. Both are guarded exactly as `getSubOptions` already was on `nullOr`, for the same reason:
a gen-types **parametric** leaf reaches the unified namespace as a bare constructor, is never
protocol-completed, and carries neither field.

The oracle for the propagation is **shape-and-length, never `isNull`** — `LIST[0]` and `LIST[1]` are
the same answer under `isNull`, and that collapse is what made two earlier readings of this surface
wrong. Pinned by `test-containers-propagate-their-element-sub-protocol`
(`ci/tests/nixpkgs-protocol.nix`), whose controls include the four containers over a **leaf** element
still reporting `null`; the refusals by `structural-sub-protocol` (`ci/tests-error.nix`), where the
control is the same hand-built skeleton with the third field supplied.

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
- **The boundary re-ties a type's completion stamp.** A gen-types record carries a stamp tying its
  identity to the record its constructor completed, and a `//` copy keeps the stamp while changing
  what the identity stands for. This boundary rebuilds every record it imports and exports, so it
  re-ties the stamp to the record it completes; a record failing the stamp on entry is imported and
  served, but unminted, and gen-types' `typeEq` refuses it by name. The price: a description-only
  `//` (`t // { description = …; }`) is a copy too, and `typeEq` refuses it; as an option type it
  is still served.
- **A completed parametric leaf merges only the SAME type, or two same-named `enum`s.** Sameness is
  decided first, by gen-types' `typeEq`: its identity is minted over its construction, so two
  textually-identical constructions merge, and a type with a SEALED component (a `typedef`'s predicate,
  a refinement's `check`) merges where `typeEq` says one type — one binding declared twice, or two
  constructions of one registered term (gen-algebra `mkIntensional`). A digest match never merges on its
  own where either side seals a component: two separately written lambdas share a mark and are refused.
  Where `typeEq` answers `false` or refuses, the relation reads both constructions through gen-types' certifying `payloadOf` (the
  construction payload, read-only and never identity), and one law applies: two `enum`s under one name merge to
  the enum of their ordered union, nixpkgs' own `enum` functor `binOp` (`unique (a ++ b)`, left
  operand first). Every other differing pair refuses by name, saying whether no law exists for the two
  constructions (`struct`, two enum names) or a payload could not be read (a sealed or foreign
  partner) — gen-merge's own refusal on the declaration path, nixpkgs' `already declared` under a
  foreign mount — instead of a wrong type. A leaf with no mint at all (an `enum` over a path, a
  self-referential type) keeps refusing: its parameters live behind its own predicate. A **nullary** leaf has no
  parameters to compare: a gen × gen pair keeps its self-merge, and a gen leaf facing a raw foreign nullary
  leaf answers the partner's record (see "A foreign payload is read only where it is read WHOLE").

### `emptyValue` — when "nothing was defined" is not an error

With no surviving definition, nixpkgs lets the **type** supply a value before this is an error
(`modules.nix`: `else if type.emptyValue ? value then type.emptyValue.value`). A container nobody
added to is legitimately empty; a value nobody supplied is a mistake. `emptyValue` is what tells the
two apart, and gen-merge stamped `{ }` — *no* `value` attr — on every type, so both landed on the same
throw.

| type                                                      | `emptyValue`                                  |
| --------------------------------------------------------- | --------------------------------------------- |
| `attrsOf`, `lazyAttrsOf`                                  | `{ value = { }; }`                            |
| `submodule`, the tree type                                | `{ value = <its fold over no definitions>; }` |
| `listOf`                                                  | `{ value = [ ]; }`                            |
| `nullOr`                                                  | `{ value = null; }`                           |
| `raw`, `anything`, `deferredModule`, `either`, every leaf | *declares none* — still an error              |

The table matches nixpkgs entry for entry, and the second half is as load-bearing as the first: a type
that declares no empty value must keep throwing. A submodule's empty value is nixpkgs
`submoduleWith`'s `base.config`: its module set evaluated with no definitions, at no prefix, with
`_module.args.name = mkOptionDefault "‹name›"`. So its defaults read as declared and an undefined sub-option refuses by name.
The tree type's is its own fold over no definitions.

There are **two ways to arrive with nothing**, and both reach the same rule: an option that was never
defined at all, and an option whose every definition was discharged away — `mkIf false` as the sole
def. So `attrsOf` yields `{ }`, `listOf` yields `[ ]` and `nullOr` yields `null` in both situations,
while a `str` still reports that it was used but not defined. The same holds per ELEMENT: the strict
`attrsOf` and `listOf` drop an element whose every definition was discharged, as nixpkgs' do, and
`lazyAttrsOf` keeps it at the element's empty value. `listOf` indexes before it drops, so a
survivor keeps its source position. An option `default` is a definition (at
`mkOptionDefault` priority), so it always wins over the empty value.

### `check` — and the types whose default was wrong

`check` is nixpkgs' definition-level predicate, and gen-merge never states it directly: a leaf brings
a `verify` (`v -> null | err`, gen-types' contract) and a structural type brings an `admits`
(`v -> bool`, its own domain), and the boundary derives `check` from whichever it finds, in that
order. A leaf's own `check` is CURRIED and must never be applied as `v -> bool`, which is why
`verify` is preferred rather than merely tried first. A type stating neither gets `_: true`, the
nixpkgs `anything` posture.

That default is correct for a type whose merge really does accept any value. **`deferredModule`'s does
not.** Its merge wraps each def into an `imports` list, and the engine's `callM` can apply only a path,
a string naming an absolute path, a function, a `__functor` attrset (applied by its `__functionArgs`,
nixpkgs `lib.functionArgs`, when its `__functor` yields a function), or a plain attrset — so a
wrong-shaped definition used to be accepted and then detonate at whoever imported it, with no option
path and no definition file. It now tests those shapes, and its domain equals nixpkgs
`deferredModuleWith`'s `isAttrs x || isFunction x || path.check x`: `types.path.check` admits a string
beginning with `/`, context irrelevant, and `callM` imports such a string as the reference's
`loadModule` does. `submodule` admits the same domain, and `lint` collects it.

**Nor did the rest of the structural surface's.** `listOf` walks every definition with `imap0`,
`attrsOf`/`lazyAttrsOf` group their definitions by key, and a submodule reads its definitions as
nixpkgs `types.submodule` does — an attrset definition is config, and any other definition is a
module — so each states its domain too, matching nixpkgs on every shape except the submodule string-that-looks-
like-a-path, where the `deferredModule` narrowing above applies for the same reason
(`test-structural-check-shapes-match-nixpkgs`). Only `raw` and `anything` keep `_: true`, which is
what their merges genuinely do.

That was previously described here as a diagnostic gap rather than a soundness one, on the ground
that a wrong-shaped definition aborts on both engines either way. **Inside a union it is a soundness
gap**, and the correction is worth stating because the reasoning is general: a union's `check` is the
**disjunction** over its members, so a single member answering "yes" to everything makes the union
unable to refuse anything, and its merge then hands a definition to a member that cannot consume it.
See "`either` — a union's merge is total" below.

**Each structural fold refuses a definition outside its `admits`, by name and catchably**, before
the fold runs. The engine's `mergeDefs` reads `verify` and never `admits`, so a definition reaching
a gen structural type's merge without passing a union used to reach `imap0` or `//` and abort with
a raw builtin error (`expected a set but found a list`), or, for `deferredModule`, be accepted and
fail wherever it was imported. `listOf`, `attrsOf`, `lazyAttrsOf`, `attrs`, `deferredModule` and
`submodule` now wrap their folds in one binding, `refusingOutside` (`lib/types.nix`), passing the
same binding they state as `admits`, so their domain check cannot disagree with the `check` they
export. It tests the surviving definitions, where nixpkgs' `checkedAndMerged` tests `defsFinal`, and
refuses `` gen-merge: option `<loc>' has definitions `<type>' cannot consume (<files>) ``
(`ci/tests-error.nix` `structural-domain`). The tree type states no `admits` and keeps the module
reader's refusal.

**A foreign type's `check` is applied to every definition before its fold**, as nixpkgs'
`mergeDefinitions` does (`checkedAndMerged`). A type whose domain is stated in the foreign protocol —
`lib.types.str`, a `check` given to `mkOptionType`, a leaf vocabulary injected as `types`, or a gen
structural type sent out and brought back through `mkOptionType` — has its `check` tested at the
boundary (`importedFold`), wrapping whichever fold the type brought, so `lib.types.str` refuses `1` at
every position gen-merge folds and the refusal names the option, the type and the failing files
(`ci/tests/foreign-leaf-check.nix`). As in nixpkgs, only the definitions that survive `mkIf` and
priority are checked.

**A nixpkgs v2 type is merged by its own `merge.v2`**, as `mergeDefinitions` merges it: its
`headError` decides, not the record's `check`, and an answer that is not exactly
`{ headError, value, valueMeta }` aborts as it does there. An ad-hoc `type // { check = …; }` on a v2
type is **refused by name**, as nixpkgs refuses it; state the check with `addCheck`. On a
**submodule-bearing** v2 type (`submodule`, `attrsOf submodule`, …) nixpkgs does not refuse the override
but erases it without a word when it rebuilds the type at declaration (`substSubModules`); gen-merge
refuses it by name there too, a deliberate departure from a silent answer. An ad-hoc `check` on a
non-v2 submodule-bearing type (`deferredModule`, `attrTag`, `functionTo`, `uniq`) cannot be told from
the one its constructor shipped, and is applied.

**A foreign type used as the `freeformType` is merged by its raw `merge`**, as nixpkgs' freeform site
merges it (`freeformType.merge prefix defs`): no `check`, no coherence guard, no `headError` apply
there. The keys it owns are still checked by that merge. A record that crossed `mkOptionType` has lost
`merge`, so its checked fold carries the raw one on it as `mergeDefs.unchecked`.

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
`oneOf` is left-nested `either`, as nixpkgs folds it, and inherits the rule. A member that is
itself an `either` accepts when every definition passes its check and its own choice takes them,
as nixpkgs' `either` takes a member whose merge reports no head error, and a refusal names every
leaf member with the files it rejected.

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

### `typeMergeRel` — merging the TYPES, not the values

The question "do these two types merge?" is about two **declarations** rather than about defs: when
an option is declared with a type in more than one module, `redeclareDecl` asks the algebra about the
whole declared-type list, bracketed as nixpkgs brackets it, and refuses the declaration outright if the
answer is nothing. A refusal names the option path and *every* declaring file; the **non-type** fields keep their ordered bias (see
"Redeclaring an option" below).

**gen states this as `typeMergeRel`, and it is ROW-FREE — that is the whole difference.** (One
carve-out, against a raw foreign partner that states a relation of its own: see "A foreign payload is
read only where it is read WHOLE" below.) nixpkgs
asks `a.typeMerge b.functor`: the second operand is a functor **payload**, a row whose shape both
sides must agree on before the question can even be posed. The relation takes **the other type**. It
is PARTIAL and its refusal is NAMED — `{ merged = <type>; }` or `{ refused = <reason>; }` — so the
declaration site reports what did not merge instead of a bare null:

```nix
typeMergeRel = other: if <compatible> then { merged = <type>; } else { refused = "<reason>"; };
```

The engine dispatches **gen-native first, foreign second**. On a declaration plane that has two
meanings, one per operand. The LATER declaration's type decides (`mergeTypes later earlier`, nixpkgs'
`later.typeMerge earlier.functor`), and an EARLIER gen-native relation is asked first whether it
refuses the later type, a refusal no later relation overrules. The foreign arm stays and is not legacy:
gen-merge meets foreign functors by construction — a gen type mounted in a foreign module system can
face a same-named foreign type declared for the same option, and that partner has no relation and
never will. Removing the arm would make the boundary one-directional, which is the C-3 ceremony
predicate.

The boundary derives **both** `typeMerge` and `functor` from the one relation, except where the
record stated its own relation — that pair is retained under a gen name at import and republished
verbatim, the author's functor name governing. Outbound, it recovers
the partner from that partner's OWN functor (`f.type` is the partner's own constructor: a function of
the payload in the protocol's spelling, or, for an alternatives payload whose application answers a
function, as nixpkgs' `either`/`oneOf` publish it, the constructor applied positionally to its
members; so the reconstruction is well-typed whatever shape the payload has) and hands a TYPE to the
relation — no payload-shape agreement is needed on gen's side. Inbound, it publishes a functor a
foreign engine can recover this type from, in the foreign spellings:

```nix
# nullary — raw, anything, every gen-types leaf
{ name; type; payload = null; binOp = _a: _b: null; }      # same name ⇒ the deciding side's own record;
                                                           # a gen leaf facing a raw foreign nullary leaf
                                                           # answers the partner's
# one-element containers — listOf, nullOr                   (gen role: `element`)
{ payload = { elemType; }; type = p: rebuild p.elemType; }
# embedded in a richer foreign constructor (`interface.embeddings`): published under ITS name
{ name = "attrsWith"; payload = { elemType; lazy = false; placeholder = "name"; }; }  # attrsOf
{ name = "attrsWith"; payload = { elemType; lazy = true; placeholder = "name"; }; }   # lazyAttrsOf
{ name = "deferredModuleWith"; payload = { staticModules = [ ]; }; }                  # deferredModule
# `type` over a payload whose fixed parameters are not the type's own refuses by name
# submodule — the parameter is the MODULE LIST              (gen role: `moduleSet`)
{ payload = { modules; }; }
# either — the parameter is the member PAIR, positional     (gen role: `alternatives`)
{ payload.elemType = [ a b ]; }
```

So `attrsOf str` and `attrsOf int` are **not** mergeable, while two `attrsOf str` are, and two
submodule declarations of one option merge to a submodule declaring the union of both. A
parameterised type left on the nullary relation would answer "mergeable" for any same-named partner
and silently keep one declaration — the type-level form of a dropped definition.

**A foreign payload is read only where it is read WHOLE.** That payload is a row and may state
more than the one parameter this side has a place for: nixpkgs' `submoduleWith` carries
`class`/`specialArgs`/`shorthandOnlyDefinesConfig`/`description` beside `modules`, and its attribute
container carries laziness and a placeholder beside its element. Lifting only the key this side knows
would build a gen type out of a partner it did not understand and drop the rest with no diagnostic,
so a payload naming anything beyond the role's own key answers "nothing to merge on". A foreign
container whose payload IS just the element is read whole, and then the PARTNER's relation decides the
pair (`interface.joinCarriedInStatedRelation`, called from the container relation): the merged type is
the partner's record at every container level, so a mixed nixpkgs/gen redeclaration of `listOf`
or `nullOr` has nixpkgs' declared-type spine whichever declaration came first, under either
engine, and refuses where nixpkgs' `binOp` refuses. It is taken only where it keeps each operand's
stated name (`interface.joinRenames`), so a pair gen's own relation refuses (`ints.u8` beside `int`)
stays refused. The cost is a property of this arm: a mixed redeclaration pays about +685 thunks per
redeclared option (`nullOr (listOf int)`, linear, measured on Nix 2.34.8), a gen × gen pair pays about
+8, and the perf bench does not reach it. `either`/`oneOf` are covered by their own rule, because the
partner's relation is in its overridden `typeMerge` and not its functor: gen's `either` facing a raw
foreign partner that offers its member pair whole REBUILDS that partner from its published functor and
asks the rebuilt record's relation over gen's own functor (`interface.joinInRebuiltPartner`), the
application nixpkgs makes in the other order, so the merged type is nixpkgs' record, leaves included,
in both orders and under both engines (`either`, `oneOf`, a union inside a container). It is
order-independent by construction only where that relation answers a join the witness keeps;
elsewhere the pair falls back to gen's own relation and keeps its order behaviour (`ints.u8` stays
refused; a `path` member, whose leaf pair is order-dependent on its own, keeps that leaf's behaviour).
A foreign answer that aborts is taken as no answer (`tryEval`), so the relation stays total. The
partner's own `typeMerge` is never called. Price (Δ thunks per option, Nix 2.34.8): a gen × gen
`listOf` pays +1 on nixpkgs' engine and 0 on gen's, a gen × gen `either` +2 and 0, and a mixed `either`
about +300 against gen's engine's former (wrong-record) answer. A partner stated under the RICHER constructor a gen type embeds in
(nixpkgs `attrsWith` for `attrsOf`/`lazyAttrsOf`, `deferredModuleWith` for `deferredModule`) is joined
in the same binding over the embedding (`interface.embeddings`): gen's parameters are a point of that
payload, so the pair is decided by the partner's `binOp` under the same witness, a foreign
`staticModules` survives it, and a refused `attrsOf` pair names its element pair. A gen nesting type (`submodule`, the tree) facing a
same-named partner that offers it nothing is not refused for that: its parameters embed into the
partner's richer `submoduleWith` payload, so it hands the pair to the protocol's default relation over
the partner's PUBLISHED functor (`interface.joinInStatedRelation`, over `interface.moduleSetPayload`),
which reads both payloads whole. That is the relation nixpkgs' twin of the gen type applies when it
decides, so the pair merges to nixpkgs' `submoduleWith` in both declaration orders and under both
engines, and refuses where nixpkgs' `binOp` refuses. Two scopes: a partner stating a `typeMerge` of its
own stays order-dependent, as it is beside nixpkgs' twin; and a partner whose `functor.binOp` disagrees
with its own `typeMerge` gets that functor's relation in the order where gen decides. For the same reason an element that states no parameter at
all — a gen-types **parametric** leaf (`enum`, `struct`, `union`) reaches the unified namespace as a
bare constructor — makes its container not mergeable instead of aborting on a missing attribute.

**A nullary leaf pair is joined in the partner's published functor** (`interface.joinLeafInStatedRelation`,
called from the leaf relation behind `other ? typeMergeRel`, so a gen × gen pair builds nothing). A gen
leaf facing a RAW foreign leaf of the same key (equal `functor.name`, both payloads null, a `type` the
functor names) answers the protocol's default over that functor, which is the record the partner's twin
answers in the order where it decides: a mixed `int`/`bool`/`float`/`raw`/`anything` redeclaration, bare
or under `listOf`/`nullOr`, has nixpkgs' declared type in both orders and under both engines. It refuses
nothing it did not refuse: the join is taken only where it keeps each operand's stated name, and a
partner whose functor states a payload (nixpkgs `path`) or no `type` is answered by gen's own relation
as before. The partner's own `typeMerge` is never called. Two stated scopes. **A pair nixpkgs refuses at
two definitions is refused np-first too** (`raw` at two equal or two list definitions, `anything` at two
unequal lists; both engines), where gen's own record served it: that is nixpkgs' answer in the order
where it decides. **`attrs` is a stated divergence**: gen's `attrs` fold refuses definitions that set
one key to different values and serves a key they set to equal values (union with refusal of a
disagreement; the last-wins fold is rejected as silent and order-dependent), nixpkgs' `//` takes the
last, so a foreign `attrs` stays refused and nixpkgs' engine stays order-dependent for it. Leaves
whose functor disagrees on identity (`str`, `number`, `path`, `deferredModule`) are outside this rule.

**The relation is published as `genMerge.mergeTypes a b`** — the merged type or `null` — the one
binding the declaration stratum and the structural element folds both answer through. It asks a gen
type's `typeMergeRel` first and a foreign type's own `a.typeMerge b.functor` otherwise, behind the
type-walk fuel guard. A consumer holding two types it did not build
(gen-schema's `refined` asks it about its base) calls this rather than keeping a copy of the relation,
which would answer the question twice with two answers that could disagree. Pinned by
`test-merge-types-is-published-and-answers-a-foreign-pair-at-its-parameter`.

### Redeclaring an option

Two modules may declare the same option loc. The merge splits the record in two:

- **The `type` is the algebra's answer about the declaration list, or a refusal.** When two or more
  declarations carry a `type`, the merged type is the list folded as nixpkgs' `mergeOptionDecls`
  folds it: seeded from the LAST declaration, the accumulated type deciding against each earlier one,
  `[a, b, c] = (c ⊳ b) ⊳ a` (the relation above, later operand deciding). A refusal is named and
  carries the option path and *every* declaring file. A relation-worded reason names the deciding
  (later) type first: `submodule` declared beside `int` reads `` (`submodule' and `int') ``, and a
  tree type beside a `submodule` names the reading that differs, since both are named `submodule`. The outcome the routing removes is one declaration's field
  surviving beside the *other's* type on a record that then disagrees with itself.
- **The non-type fields are right-biased, and what they shadow stays reachable.** Later declarations
  win field by field: this fold is an *ordered* fold over the authored module order, so a later
  declaration is a later contribution rather than a stronger one, and a module layering `apply` onto
  an earlier typed leaf composes exactly as it reads. An ordered bias is a rule only while the loser
  is still reachable, so a merged record that actually shadowed a field carries what it shadowed:

```nix
(evalModuleTree { } [ a b ]).options.x
# ⇒ { _type = "option"; type = <str>; default = "from-B";
#     overridden = [ { file = "a.nix"; declaration = { type = <str>; default = "from-A"; }; } ]; }
```

Each entry's `file` names the module that most recently **contributed** to the record being
shadowed, which is not always the module that first declared the option: a module adding a field
shadows nothing and records no entry of its own, and when a later module restates that field the
entry names the module that wrote it.

**The type is decided once, at the last typed declaration.** `⊳` is not associative, so a left
module fold cannot build `(c ⊳ b) ⊳ a` step by step. Each redeclaration step reads the typed
declaring sites up to itself; only the step with no typed site after it may refuse. An earlier
step's type is the prefix's own answer, read lazily, so `overridden[].declaration.type` still means
"the accumulated earlier declaration" — and where that prefix does not merge on its own it is a named
throw if forced, since a later declaration may merge the whole list: with `B = attrsOf int`, `fo` a
`B` whose functor is renamed (so `[fo, B]` alone refuses) and `Fk` a `B` whose relation answers a
`B` that admits any partner, nixpkgs accepts `[fo, B, Fk]` as `attrsOf`, and so does gen-merge,
whose `overridden` types then read `attrsOf` and the throw. A later **untyped** declaration does not defer the
decision. The freeform plane reads its winner list through the same fold.

**A type-merge refusal surfaces on the read that reaches the option**, so the result is as lazy as
`declaredOptions` and nixpkgs. The declaration guard forces the key set and the `imports`
expansion of every level, deciding leaf or group per declaring module, and never merges a
redeclared leaf: a declared `type` is a descriptor field. So with `p` declared `str` in one module
and `int` in another, `config.p` and `options.p` refuse with the type-merge text, while
`options.q.type.name` of an unrelated `q` reads its answer. Which declarations are admitted does not
depend on how many modules declare an option: a `type` read from a `_module.args` argument is
admitted whether one module declares the option or several. **The cyclic case aborts uncatchably,
a declared exception to the rule that every refusal is catchable**: where that argument's own value
reads the option it types (`_module.args.ty = if config.p == … then str else int` beside
`options.p.type = ty`), the read dies with `infinite recursion encountered` at any declaration
count, as nixpkgs does. Refusing it by name would mean refusing every stratum-2 read in a declared
`type`, including the common `(pkgs.formats.json { }).type`, which the guard admits.

**An earlier gen-native relation's refusal is never overruled.** Each fold step first asks the
earlier operand's `typeMergeRel`, if it has one, about the type every later declaration jointly
became; a refusal there is the answer. So `[gt.int, Fint, str]` refuses as nixpkgs does. The veto
protects a gen relation against the type it is actually merged into. A foreign relation keeps the
authority nixpkgs gives it except over a join that drops a name an operand states, authored or
inherited, which refuses (below): `[gt.int, str, Fx]` with `Fx = str // { typeMerge = _: int; }`,
which nixpkgs accepts as `int`, refuses at `Fx`'s step, since `int` states neither `str` nor `Fx`.

**Against nixpkgs, on the type.** Over every declaration list of length 3 and 4 in a seven-family
census (8,338 words), gen-merge agreed with nixpkgs on every all-foreign list whose joins keep their
operands' names, on both the declaration and the freeform planes. It departs where a fold step's
gen-native relation refuses, and then by refusing: gen `attrs` against foreign `attrs` in the order
nixpkgs accepts, directly or under a gen container; an earlier gen relation vetoing a later foreign
relation that answers another type; and a refinement under a gen container against its bare element.
It also departs where a foreign join drops a name an operand states (the check-family witness,
below), and where a merge drops the check a wrapper added to a gen record (below the witness): by
refusing, or, for a pair that is one shared value, by keeping that value. Over a 65-type
pair census it merges no pair the relation without the witness refuses. They are listed under
[Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate). A refined type redeclared against
its bare base refuses in both orders, directly or under a gen container.

**A foreign join that drops an operand's check refuses.** nixpkgs' `addCheck` is
`elemType // { check = …; }`, so it keeps its base's `functor` and `typeMerge`: `port ∥ int`,
`u8 ∥ u16` and two `ints.between` calls all join to bare `int` there, and `[port, int]` accepts
70000\. gen-merge takes a foreign join (`later.typeMerge earlier.functor`, or an imported record's
stated relation) only where it keeps each operand's stated name at every depth the operand wraps a
type; otherwise the pair refuses, with a reason naming the join. A role the join gains is not a drop,
so a freeform submodule unioned with an option-only one, or two `attrTag`s, merge as on nixpkgs. A
join that is a gen record is compared with each operand as the import environment reads it, so a
type whose relation rebuilds it through `mkOptionType` (gen-schema's `refined`, gen-aspects'
`aspectsRoot`) merges when redeclared as itself. A
pair that is one shared value keeps it: `[port, port]` from one `types.port` answers `port`, and
rejects 70000. Refusing is the one answer sound whether a redeclaration is read as a join or as a
meet; which of those it means is left open. The cost is one fuel-bounded walk per foreign fold step,
and a second join only on the refusal path; gen-native pairs never reach it. Measured with
`NIX_SHOW_STATS`, one option declared in 200 modules: `listOf str` +2.7% thunks and +1.0% function
calls, a distinct `submodule` each +0.1%, `port` +0.07% and +0.18%. The measured members are under
[Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate).

**A type merge that drops a wrapper's check refuses, at every depth.** An `addCheck` keeps its base's
name and relation, so no name separates `addCheck int p` from `int`, and the relation answers the bare
base: `[int, addCheck int (x: x > 0)]` serves -1 on nixpkgs, in either order. For a gen record
gen-types' check-witness protocol makes the rewritten check observable (`rewritesCheck`), so
`mergeTypes` refuses wherever an operand's check was rewritten and the merge is not that operand
itself. The pair refuses with the wrapper first or second, under a gen parametric (`union [ int ]`),
under a container (`listOf (addCheck int p)` beside `listOf int`), and in a longer list, with a
reason naming which of the pair lost its check; under a container that reason follows the element
refusal. The test sits in `mergeTypes`, so the declaration and freeform planes, every container's
element relation and the published `genMerge.mergeTypes` all answer it. As above, refusing is sound
under both readings of a redeclaration. It is a default, and reversible: the rule that no check
vanishes silently forbids serving the value, but does not itself choose a refusal over another named
answer, so settling the reading as a join would relax this arm alone. **One wrapped value declared twice keeps its operand**: `w = addCheck int p`
declared as `[w, w]`, or as two `listOf w`, merges to `w` and rejects what `p` rejects. **Two
separately written wrappers refuse even over one predicate source**, because a check is a caller's
function and two cannot be compared (`mkOptionType`'s `sealedRel` answers the same): declare the
wrapped type once and reference it. A foreign record states no witness, so `addCheck` over a nixpkgs
type redeclared still serves as nixpkgs does (Known byte-mode boundaries, "Not covered"). The cost,
measured with `NIX_SHOW_STATS` on Nix: +3 thunks per evaluation, a constant, with calls and bytes
unchanged, for any number of options each declared once; `listOf int` declared in 200 modules, +0.40%
thunks, +0.90% function calls and +0.62% bytes, the element relation now asking the witness on every
step. The hub perf-bench row `moduleFanIn` declares each loc twice, so it guards the constant; the row
`sameLocFanIn` declares one loc in every module and gates the growth of the per-loc fold.

**Cost.** The declaring sites are grouped once per evaluation into a trie keyed by path step, so a
step finds an option's sites by a lookup of `depth` steps, whatever the module count `M`. The per-loc
facts a typed redeclaration step needs (the loc's typed sites and the index of the last of them) are bound
once per loc, and each step is told its position in the loc's declaration list, so the step costs the
same for any `n`: an option declared in `n` modules costs `O(n)` in thunks and calls. The type is decided
once, at the last typed declaration, by one `n`-element fold; each step is forced to WHNF as it is made, so
the fold's depth does not grow with `n` (one loc declared in 102,400 modules evaluates). Measured with
`NIX_SHOW_STATS` on Nix 2.34.8, one option declared `str` in all `n` modules, reading `config.p`: the
growth exponent over `n = 1600 → 6400` is 0.93 / 0.96 / 0.93 (thunks / calls / bytes), and 1.00 at
`n = 25,600 → 102,400`; nixpkgs reads 0.99 / 1.00 / 0.99 on the same shape. The hub perf-bench row
`sameLocFanIn` gates that linearity. The declaration guard forces each declaring module's key set and
never the merged record, so one option declared in `n` modules costs 2 thunks per module beyond `n`
options declared once each. The published `overridden` list is threaded as a chain and listed once, at
the last step, and the `provenance` of undeclared keys is grouped once and nested by a trie, so both
read linear in BYTES when forced: exponents 0.97 (`overridden`), 0.95 (one undeclared key in `n`
modules) and 0.96 (`n` distinct keys) over `n = 1600 → 3200`, on Nix 2.34.8, where the `++` chain and
the `//` accumulator they replace read 1.51, 1.69 and 1.47 (`ci/bench/redeclaration-cost.sh`). **What is not linear:** every provisional prefix type
(`overridden[].declaration.type`) is quadratic when forced, because `⊳` is not associative; that is
inherent to keeping the provenance. `n` distinct submodule-typed options, one
per module, read 1.49 in bytes (nixpkgs 1.61) with thunks and calls at 0.98.

**Against nixpkgs, on the other fields.** The engines part on the **other** fields — nixpkgs refuses a redeclaration
outright when both declarations carry any of `default`/`example`/`description`/`apply` (its
`bothHave` guard, which fires ahead of the functor), where gen-merge right-biases them under the
stated rule above. So the divergence runs one way: gen-merge accepts field-colliding redeclarations
that nixpkgs rejects. Note that nixpkgs prints the **same** `already declared` text on both of its
paths, so the message does not tell you which one refused — the `str`/`str` case merging is what
separates them.

`overridden` is oldest-first and appears **only** where a declaration really was shadowed — a module
that merely adds fields (the `apply`-layering shape) leaves the record exactly what a plain field
union produces. A third declaration appends to the chain rather than replacing it.

### The tree-as-a-type is an option type named `submodule`

`(evalModuleTree …).type` is the seam that lets a parent tree nest a child (submodule recursion,
freeform), and it is an option type: a real nixpkgs `lib.evalModules` mounts it bare, inside every
member-taking combinator, and in its docs. It reads every definition as a module, as its reference
`(lib.evalModules …).type` does (`submoduleWith`'s `shorthandOnlyDefinesConfig` defaults to false),
where `types.submodule` reads an attrset definition as config. Both nesting types read through the
one binding `defsAsModules`, nixpkgs' `allModules` flag for flag.

It is built as `submodule` is, by `strategies.defineType`, the one crossing site: a fold
(`mergeDefs`), a domain (`admits`, the module-value domain `isModuleValue`), a carried module set
(`carries.moduleSet`) with its rebuild (`recarry`), a relation (`typeMergeRel`) and the substructure
triple. Every protocol field is then derived by `exportType` as for any gen type.

| field                                               | answer                                                                                                                                                                                                                                                                                                                                                       |
| --------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `name`                                              | `submodule`, nixpkgs' name for a type whose definitions are modules: nixpkgs merges raw sub-option declarations into an option whose type is named `submodule` (`mergeModules'`), and its container phrases and refusals read so                                                                                                                             |
| `functor.payload`                                   | nixpkgs' `submoduleWith` payload, `{ modules; specialArgs; shorthandOnlyDefinesConfig; description; class; }`, published for both nesting types (`false` for the tree, `true` for `submodule`), so nixpkgs' `binOp` and raw-option merge read what they read off its own                                                                                     |
| `typeMerge`                                         | the relation: two trees union their module sets in authored order, as nixpkgs' `binOp` does, and merge `specialArgs`, refusing a key both state. A tree and a `submodule` refuse each other by name, naming the reading that differs, as nixpkgs refuses the pair. A foreign `submoduleWith` partner is joined in its own functor's relation, in both orders |
| `description`, `nestedTypes`, `getSubOptions`       | the freeform datum crosses: the tree's resolved freeform type (`unroledNested.freeformType`) gives nixpkgs' "open submodule of …", `nestedTypes.freeformType` and `_freeformOptions`                                                                                                                                                                         |
| `getSubOptions`, `getSubModules`, `substSubModules` | the tree's declarations under the foreign prefix, its module set, and its rebuild over another                                                                                                                                                                                                                                                               |
| `check`, `merge`, `emptyValue`                      | the module-value domain, the fold through the bridge (one root evaluation of the tree), and the tree over no definitions                                                                                                                                                                                                                                     |

**`submodule` and the tree name their modules as nixpkgs' `submoduleWith` does.** Each child with definitions gets
`_module.args.name` = the last step of its position (the attribute name under `attrsOf`, the
`[definition n-entry m]` step under `listOf`, the option's own name bare or under a union), resolved as
one definition at normal priority beside its modules' own. The child over no definitions, `emptyValue`
and `getSubOptions` read the placeholder `mkOptionDefault "‹name›"`. So a module's `mkForce` or
`mkDefault` on `_module.args.name` resolves by priority as nixpkgs resolves it, a plain definition
refuses as defined multiple times, and a caller's `specialArgs.name` (`withArgs` on `submodule`)
outranks it. `withArgs` therefore admits `name`, and refuses by name only the three arguments the engine
writes over, `config`, `options` and `prefix` (the refusal of `name` there stood
while `submodule` injected it over the caller's, and is superseded). A module reading `name` while its
declarations are folded (`imports`, an option key) refuses by name as it would for any module argument,
unless a caller supplied it. A module whose `_module.args` key set reads `name`
(`_module.args = if name == … then { … } else { }`) dies with infinite recursion, as in nixpkgs: whether
a module states `name` is decided by that key set, so it cannot wait on `name`.

**The published option records carry nixpkgs' declaration shape.** An evaluation's `.options` (and
`declaredOptions`) records carry `loc`, `declarations` (the declaring modules' files) and nixpkgs'
string form, `__toString = _: showOption loc`, so nixpkgs' `optionAttrSetToDocList` renders a mounted
tree's docs byte-equal to its own in `make-options-doc`'s view (`visible && !internal`). The evaluated
keys nixpkgs adds beside a declaration (`value`, `isDefined`, `definitions`,
`definitionsWithLocations`, `files`, `highestPrio`, `declarationPositions`, `options`, `valueMeta`)
are the option's value and definitions, which gen publishes on `config` and `provenance`; each is
refused by name, never absent. So a deep force of a published `.options` tree refuses, for every tree
(`test-a-deep-force-of-a-declaration-tree-meets-the-unanswered-keys`). The tree declares no
`_module` options, so its full doc list departs from nixpkgs' by the four `_module.*` entries nixpkgs
marks internal below the root.

**A union holds the tree as a member**, in gen's own eval and abroad. A gen union (`either`, `oneOf`,
`nullOr`) asks its members `admits` before `check`, so `either tree str` is union membership, and
gives what nixpkgs gives over the same construction. A definition outside the module domain is
refused by name before the nested eval runs (`` option … has definitions `submodule' cannot consume ``),
and an undeclared key under the union is refused by name as at a container element. Over the 180-mount
tree-union family a real `lib.evalModules` serves 138, each equal to nixpkgs' fold of the same
construction over its own `(evalModules …).type`, and refuses 42, each one nixpkgs refuses too: a
string definition reaching the tree's fold inside a container, or refused by nixpkgs' own check under
`nullOr`/`option` alone. A caller fold that closes over a union lexically, carrying no member, folds
it by its called form, and the tree refuses by name.

**Its fold is one value, and where no report is carried it refuses.** The tree is a child of the one
evaluation that holds it (below), so the fold READS it rather than evaluating it. `mergeDefs.threaded`
is the strict fold: every site that carries no undeclared report — a container element (`attrsOf`,
`listOf`, `nullOr` of the tree), a freeform plane — refuses a key the tree's own level does not declare
by name when that level is read, with its path, its file and the element's location. The trees nested
inside that level fold the same way, so each refuses its own level when it is read, and a level that
is not read decides nothing. `mergeDefs.threadedReported` is the same fold for the one caller that
carries a report, the declared leaf of an evaluation: it returns `{ value; undeclared; }` off one read
of the child, which inherits that evaluation's effective strictness. The finding is reported (above),
and, when either the carrier or the nested tree is strict, refused by the child at its own level when
that level is read. The CALLED forms (`mergeDefs` applied, `.reported`, and `whenEmpty.value`) refuse
by name: no second evaluation is made for a tree. To wrap a tree's fold, **replace `mergeDefs` whole**.
The same holds for a foreign type imported with a `check`, whose `mergeDefs` is a functor carrying its
unchecked fold as `.unchecked` for the freeformType site: a whole replacement governs at every site, a
refined `__functor` is ignored at the freeformType site
(`test-replaced-mergeDefs-governs-at-the-freeformType-site`).

`mergeTypes` consults a tree's relation as any type's. The warm identity walk reads a declared leaf
typed by a tree as it reads a `submodule` one. Pinned by
`test-reused-module-tree-leaf-reports-its-dropped-def`.

The mounts are pinned in `ci/tests-error.nix` (`tree-type.*`) and the parity cells in
`ci/tests/nixpkgs-protocol.nix` (the raw sub-option merge, the tree and `submodule` pair, the rendered
docs, the freeform datum and the string form).

### A foreign type that declares a nested tree, and the declared opt-out

A nested tree (`submodule`, `(evalModuleTree …).type`) is a node of the one evaluation rather than a
second evaluation called from inside a fold (see "Nested trees are children of the one evaluation"
below). Each nesting type
states its tree as data (`nests`: the module set, arguments, definition entry and the mode its
called form evaluates in), and each container states its element positions once (`split`), which
its own fold reads. `lazyAttrsOf` is the one exception: its fold is the split's twin, held equal
by a cell, because it is the `wideFreeform` hot path.

A foreign container outside the six gen-merge recognises (`attrsOf`, `lazyAttrsOf`, `listOf`,
`nullOr`, `either`, `oneOf`) passes the evaluation down to a nested tree only through its own
`substSubModules` rebuild (below). So gen-merge asks
whether such a type DECLARES a gen nesting type as an element, at any depth, through the carrying
spellings: its `nestedTypes` or a top-level `elemType` (`interface.declaresNesting`). A functor
payload says what a type MERGES on, not what it carries, so it declares nothing (ruled 2026-09-25).
That walk has a fuel of 32 (the
same `importedTypeWalkFuel` as the type-merge guard). A self-referential element, such as nixpkgs'
`types.json` shape, cannot be told from a deep one, so at exhaustion the walk **refuses by name**
(ruled 2026-09-27, S2 arm (i)). The message names the remedies that exist:

- wrap the element in a recognised container;
- in gen's own evaluation, use a container whose `substSubModules` rebuild states its element and
  whose `check` does not read the nested tree;
- state the answer yourself with the **declared opt-out**:

```nix
types.uniq valueType // { declaresNesting = false; }   # the container…
types.uniq (valueType // { declaresNesting = false; }) # …or the self-referential element
```

The walk reads the field on every type before it descends. A type carrying `false` answers `false`
with no walk and no fuel. **The price, taken by name:** a marked type that DOES forward to a gen
nesting type becomes a silent standalone evaluation through the exported `merge` (OQ11 (d)'s
stated price). Only `false` is accepted. `declaresNesting = true`, or any non-boolean, is refused by
name at `mkOptionType` and wherever the walk meets it, since a declared `true` is not a way to opt
in. Pinned by `ci/tests/nesting-declaration.nix` and `ci/tests-error.nix`
(`nesting-declaration.*`).

**Where the refusal fires, and re-homing.** A type is HOMED where it is bound to a position: at a
declared option (`evalModuleTree`), and when a record crosses whole through `mkOptionType`. One of
the six stock foreign containers whose element may nest is folded as gen-merge's own container, so
`nixpkgs.lib.types.attrsOf (submodule …)` threads like gen's. A stock container over no nesting
element keeps its own fold, unless its two statements of the element disagree (below). The six are recognised by their functor, the relation they merge by,
and rebuilt over the element their carrying spellings state, never over their payload's.

**An unrecognised container threads through its own rebuild** (ruled 2026-09-30, arm (T)). At a
declared option, a foreign type outside the six that declares a gen nesting element (`coercedTo`,
`uniq`, `unique`, `functionTo`, `attrListOf`, `attrsWith` with a non-default `placeholder`, a
hand-rolled `mkOptionType` whose rebuild forwards its argument, …) is rebuilt through its own
`substSubModules`, handed a marker that a gen element answers with itself. The container keeps its
own `merge` and `check` (`coercedTo` keeps its coercion), and the element under it folds as a node
of the one evaluation, so the value is nixpkgs'. Whether the rebuild threads is judged on the
ORIGINAL record against its rebuild, position by position and at any depth: every declared position
that may nest comes back as the marked element (or as a record that threads in turn), and every
other declared position is a sibling whose own `substSubModules`, called on the marker, answers
`null`, so it has no module set to lose. The marker's import throws the import refusal if anything
evaluates it as a module. Five things are refused by name instead:

- a rebuild that does not THREAD: it drops its argument (and would reach the tree as a standalone
  evaluation), or a sibling of the element would receive the marker in place of the module set
  nixpkgs leaves it (one that evaluates, relabels, stores, or drops the list from its rebuild);
- a position the declarations do not show that evaluates the marker as modules: it meets the
  marker's import, never folding an empty module;
- a nested-tree read at a position the container's merge does not expose, such as inside the
  function `functionTo` returns; a member that reads no tree (a string definition) still answers;
- the container's own refinement (`addCheck`), applied on the threaded fold with nixpkgs' verdict
  and naming the container, where it fails; one that reads the nested tree reads the tree's
  module-value `check`, so it is evaluated like any other;
- the same containers through `mkOptionType`, which keeps the import refusal.

A stock `unique` over the tree is decided stock and served, since its check is its element's. A
refinement on the element is carried as it is under the six. **The prices, stated:** `unique`'s
message is lost on rebuild, as nixpkgs' own rebuild loses it; the element handed into a rebuild answers `check` in
gen's words and `getSubModules` with `null`; the container's merge runs three times per option
against nixpkgs' once. A foreign closure, the container's own merge and check, runs inside gen's
evaluation over a gen-threaded element fold; no foreign engine evaluates the tree, and the channel
is entered only in gen's own evaluation.

**At the option root, a foreign record stating a module set is mounted as nixpkgs mounts it.**
nixpkgs' `fixupOptionType` rebuilds a declared
option's type over the declaration's module set, at the option's root only, and the rebuild reaches
what the root's own `substSubModules` forwards to. A foreign root that states a module set
(`getSubModules` is a list) is mounted the same way, judged before any read of the record's roles: as
its rebuild over that module set, where the result is an option type declaring no gen nesting
element, whose merge is the one served (`homedRootAt`). A root declaring a gen nesting element that
does not thread is mounted so too. So a hand-written `mkOptionType` whose own merge is not its
rebuild's, a `//` override of a stock submodule's `merge` or `substSubModules`, a payload-null copy
of a stock submodule (a definition completing its module set included), or a submodule given an
`elemType` it never folds, gives nixpkgs' value at the root and under a forwarding container. The
record's own `check` rides on the rebuild, gen's own or foreign, so the domain is the meet of the two
(`carriedCheck`, the re-home law): an `addCheck` over such a root refuses what it rejects, where
nixpkgs' rebuild erases it silently. A rebuild that is no option type (null, a bare attrset, absent,
or stating `merge` but no `check`) is refused by name (`rootRebuildRefusal`), where nixpkgs aborts, and
an ad-hoc `type // { check = ...; }` keeps its by-name refusal. A freeform type is no option's root
and is not mounted. The fix-up item's `_file` is `<unknown-file>`, as nixpkgs labels a module stating
no file, not the declaring file, and the module set is the merged type's, not a union per
declaration. Refused by name, pending the
release-parity ruling, where nixpkgs serves:

- a record declaring a gen nesting element that nixpkgs never rebuilds (no module set at the root,
  or below a union: `uniq (either (attrsOf sub) str)`, `either int copy`, any non-six container over
  a union holding a gen element) and whose marker rebuild does not thread;
- a fan-out container whose sibling of the threaded element substitutes a module set or becomes
  `null`; the opt-out serves it;
- a gen root container over such a record (`attrsOf copy`, `listOf copy` from gen-merge's types),
  whose element is homed at an inner site, never fixed up;
- a root whose fix-up result still declares a gen nesting element (a copy whose rebuild re-wraps
  itself).

**The prices, stated.** A hand-rolled position the declarations do not show whose evaluation of the
old empty marker module happened to equal nixpkgs' value is now refused by name. And a position the
declarations do not show whose merge STORES the handed list (`deferredModule`) is served with gen's
marker item in its value: inspecting the stored list (its length, its `_file` labels) differs from
nixpkgs silently, and evaluating it refuses by name. No predicate reaches it without reading a
payload: it is the half of arm (T)'s stated domain (a merge that does not inspect element values)
that has no predicate here.

Two more records are
refused by name (*defaulted, reversible*): one that states no element but whose functor payload
OFFERS a type declaring a gen nesting type (a hand-rolled `functor.payload.elemType`, or a stock
container with its `nestedTypes` removed), since its own fold would evaluate that tree standalone
and nothing in it says so; and a recognised container whose payload offers a different element
than it states, nesting or not, since it would carry one type and merge on another. Two elements
are the same when their `check` and `merge` are the same closures, as a stock container's are, so
two separate constructions of one shape differ; so two trees, a tree and a type folding by another
`merge`, and a tree stated with its `check` rewritten against the tree offered are each refused. Every one of these messages names the door (`mkOptionType`, or `evalModuleTree` with the
option), the type, what declared the element, and the ways out, the opt-out above among them.
**The prices, stated:** a stock container whose `merge` was overridden (`attrsOf t // { merge = …; }`)
cannot be told from the stock one and is re-homed silently, losing the override; and a foreign type
that forwards to a gen nesting type it does NOT declare evaluates that tree standalone through the
exported `merge`. A stock `either`/`oneOf`/`nullOr` re-homed over the gen module tree carries an
`addCheck` on that container: the tree's `check` is its module-value domain, so the stock check reads
it and the rewritten one is evaluated. `addCheck (either tree str) p` and the
`oneOf` twin refuse as nixpkgs does; over `nullOr` gen-merge is stricter than nixpkgs, which erases the
check at declaration. The `eitherTree`, `oneOfTree` and `nullOrTree` rows of
`test-the-residue-is-the-bare-tree-and-the-offered-tree` in `ci/tests/check-carriage.nix` pin all
three as refused, and **The price extended to a lost `check`** below states what is still lost.

**A check a wrapper states is carried.** nixpkgs refines a domain
on the descriptor's `check` (`addCheck t p`, `t // { check = …; }`, and `nonEmptyListOf`, which is
`addCheck` over `listOf`). **The `check` of a gen record is a callable record**, `{ __functor; … }`,
the kind nixpkgs already publishes for its own v2 checks: apply it as a function, and ask its kind
with `lib.isFunction` (functor-aware), never `builtins.isFunction`, which answers `false` for it
(`builtins.typeOf` is `"set"`, and `builtins.functionArgs` aborts on it). Over a gen record, the
rewritten `check` is detected by construction: the witness is the `check` record itself. `exportType`
publishes that one record twice, as `check` and as `_checkWitness`, and a record whose `check` is no
longer the witness was rewritten; `==` meets one set of bindings there and allocates nothing, so the
test is paid on every fold at no cost per fold. **The protocol is gen-types'** (gen-types' README is its first record and this is the
second):
`exportType` builds the one record with gen-types' `witnessRecord` and publishes it under both fields
itself, and the test is gen-types' `rewritesCheck`, so `_checkWitness` and the functor's `_fn` are
gen-types protocol fields, and gen-merge defines neither the record nor the test. It spells the pair
rather than take `witnessedCheck`'s, because that two-field result would cost every exported type a
set to read or copy, a slope per aspect; `witnessedCheck`'s
output is the layout the spelling is held to, by the door below, not by construction. Four per-fold sites restate the test inline, for
cost, because a call there is an environment on every fold and the fold's allocation ratchets have
no headroom for it: `interface.importedFold`, `modules.nix` `ownFold` and `threadedAs`, and
`types.nix` `isValid`, which asks it negated. What holds those copies to gen-types' test is a
construction-time **agreement door** (`lib/default.nix` `witnessDisagreement`): it asks both inline
spellings, and gen-types' own `rewritesCheck`, about the pair `witnessedCheck` builds and that pair
with its `check` replaced, and about the pair `exportType` spells from `witnessRecord` and that pair
rewritten. It refuses by name a gen-types whose test answers other than a boolean, or reads either
pair otherwise than the inline test does, whether the field was renamed or now holds something
else; a pair carrying any field beyond `check` and `_checkWitness`, which `exportType` publishes by
name; and a `witnessRecord` whose record is not shaped as the one `witnessedCheck` publishes
(`ci/tests-error.nix` `check-witness-protocol.*`). Its claim is scoped to those records: a
`rewritesCheck` that departs only on a record of some other shape passes it. Every fold meets only
records of these shapes or witness-less ones; the door never asks about a witness-less record. The
inline spellings read one `false` by their `?` guards, and that gen-types' own test does too is held
by gen-types' suite, not by this door. A `check` published as a bare lambda again is refused on every evaluator: on Nix and
Determinate by the inline test, since `f == f` is false there, and on Lix, where it is true and the
two spellings agree on `witnessedCheck`'s pair, because the pair `exportType` spells from
`witnessRecord` is then not that pair. Its fold then applies that
check to every definition (`checkedFold`, the same verdict as nixpkgs' `checkDefsForError`), at the
option, at an element, in the threaded fold, at a union's member choice and at the `mkOptionType`
door. gen reads it as a refinement: the gen domain (`verify`/`admits`) still applies, so a widening
`check` is refused by the base. A stock container that is re-homed keeps its own `check` on the
rebuild, since a functor rebuilds the container and its element and not a refinement over them.
A check over a union or nullable holding the bare tree reads the tree's `check`, its module-value
domain, so it is evaluated like any other: a failing one refuses and a passing one serves. A record re-bound by selection (`t // { inherit (t) check; }`), rebuilt by
`inherit`, or passed through `mapAttrs` keeps the same `check` record and reads as its own on Nix,
Determinate and Lix. Pinned by `ci/tests/check-carriage.nix` and
`ci/tests-error.nix` (`check-carriage.*`).
**The price extended to a lost `check`**: a check over
the bare tree itself is not carried, and is lost silently: the declared leaf folds the tree through its
threaded fold, which reads no rewritten `check`, and nixpkgs erases it too
(`test-the-residue-is-the-bare-tree`). The gen-types composites (`ts.refined (addCheck ts.int p) …`) read the
witness through the same protocol and carry or refuse such a member; what stays silent there is a
bare gen-types checker with its `check` rewritten, which has no witness (gen-types' residue R1).
**And a parametric leaf redeclared with a wrapped twin** refuses: an option declared once with a
gen-types parametric leaf and once with the same leaf under `addCheck` (`union [ int ]` beside
`addCheck (union [ int ]) (x: x > 0)`), in either order, merges by the two records' shared digest
(`completeParametric`'s relation), which drops the added check. The relation cannot read the
witness: a `//` copies the relation, so it is bound to its base and cannot tell its own wrapped
record declared twice, which must merge, from a wrapped partner, which must not. `mergeTypes` sees
both operands, so it refuses the drop and keeps one wrapped value declared twice, check and all
("Redeclaring an option").

Each nesting and container fold also carries a `threaded` sibling, reading its
nested trees through the evaluation's accessor, and a gen type's exported `merge` folds through it
with a bridge that evaluates each tree once, standalone, as before. Pinned by
`ci/tests/nesting-threaded.nix` and `ci/tests-error.nix` (`nesting-threaded.*`).

### Nested trees are children of the one evaluation

`evalModuleTree` is ONE gen-scope evaluation, with no second engine evaluating each nested tree on
its own. Its knot is a node of the kind `module-tree`, which declares one non-terminal attribute
(Vogt, Swierstra & Kuiper 1989 §3), `nested`: each nested tree the value holds is a child of that
node, minted at its POSITION (the option's path and the position below it), and a child's own nested
trees are its children. A child's `result` is its tree's evaluation, read from its host's position
record at its own coordinates (`getHostAt "positions"`: its definitions, `loc`, report mode and
member), the host's equation for that child (Söderberg & Hedin 2013 §2.3, §4.1). Its own record
carries its seed, the addresses of those definitions, which the evaluation does not resolve (owner
ruling 2026-09-28, arm (B)). The fold reads a child through the node's own record
(`getNta`), never by identifier. Values are unchanged; the evaluation count is 1
(`ci/tests-process.nix`, `one-eval-*`).

- **Which positions are children.** A nesting type is one; at the walk's root a container is walked
  through its `split`, exactly where its key set already reads its definitions (`attrsOf`, `listOf`,
  `nullOr`) and over-approximately where it does not (`lazyAttrsOf`, a freeform plane). A union is walked member by
  member at its own position; a container member counts only where every definition has its shape.
  A container of trees under `lazyAttrsOf` — bare, or as a union member — is S1 class (a): its
  position is a **container node**, a child whose own `container` group
  keys the inner trees over that position's definitions only, so no sibling is forced to key them,
  and whose `result` is `{ value; _nested; }`, the inner container's fold, not a tree's evaluation.
  At the walk's own root (an option's position, or a container node's) under a container that adds
  no step (`uniq`, `unique`, `coercedTo`), the position is walked as the root is, and the shape
  serves nixpkgs' value: that container's fold is its element's over the same definitions, so keying
  forces nothing a read does not. Below a step under any other over-approximating container — a
  split container whose fold sets no mark (gen-aspects' `aspectsRoot`, or a freeform plane typed by
  one) — the shape is refused by name. nixpkgs serves it there, so the refusal is a stated shortfall
  against serving nixpkgs' value, not a divergence from it.
  At an EXACT container's element, every container is keyed where it is READ. An attribute-keyed one
  (`lazyAttrsOf`, or an `attrsOf` whose element would not itself key so) keys over-approximately, by
  its definitions' attribute names, through its fold's door. Every other one is a container node: a
  `listOf`, a union holding a container member, a nixpkgs container gen threads rather than re-homes
  (`uniq`, `unique`, `coercedTo`, `attrsWith` with a placeholder), another split container
  (gen-aspects' `aspectsRoot`), and an `attrsOf` over an element that keys over-approximately. So
  `attrsOf^k S` at an exact element alternates with k: over-approximated where k is odd, a node where
  k is even.
  A sibling's definition outside a container's domain, or a sibling whose element throws, never
  breaks another key's read, as in nixpkgs.
- **Candidates.** An over-approximated child the fold never selected (a union position under a lazy
  container whose `choose` picks a non-nesting member) is enumerated, and reading its `result` refuses
  by name before any of its member's modules is applied.
- **Growth over empty seeds** refuses past `importedTypeWalkFuel` (32) by name: a nesting type that
  holds itself, on an option left undefined, would otherwise grow undefined trees without end.
  **The price:** an undefined chain of 32 or more directly typed nesting levels is refused even where
  it is finite, since recursion and depth cannot be told apart (OQ15 (c), *defaulted, reversible*).
- **Enumeration** (`allNodeIds`) evaluates every child's definitions to find its own children, and at
  gen-scope `d62b595` it grows exponentially with nesting depth. Read values through the fold.

Pinned by `ci/tests/nesting-placement.nix` and `ci/tests-error.nix` (`nesting-placement.*`).

## nixpkgs types on the engine

nixpkgs option types run on the **same byte-mode engine** as FOREIGN VALUES at its options, unmodified
and with zero adapter code:

```nix
genMerge.evalModuleTree { } [
    { options.name = lib.mkOption { type = lib.types.str; default = "d"; }; }
    { name = lib.mkForce "x"; }
  ]
```

nixpkgs option types already speak the `(loc, defs)` merge contract `mergeDefs` dispatches on — a
nixpkgs type carries a `.merge` (called `type.merge loc defs`) and no gen-types `.verify` (so the
post-merge verify is skipped) — and nixpkgs property tags (`_type = "override"/"merge"/"if"`) are
byte-compatible with gen-merge's priority pass, so `mkDefault`/`mkForce`/`mkIf`/`mkMerge` from nixpkgs
discharge identically. (Pinned by `ci/tests/compat-nixpkgs-types.nix`.)

**Not through `types`.** This was once "compat mode", a second engine built with `types = nixpkgs.lib.types`. That mode is withdrawn: `types` is the gen-types library, and nixpkgs'
`lib.types` handed to it is refused by name at construction ([The `types`
namespace](#the-types-namespace)). The engine never read its vocabulary to evaluate a module, so
every module that ran on that engine runs on this one unchanged.

**When to use it** — a migration on-ramp: bring a custom nixpkgs `mkOptionType` (or an odd leaf type)
along while porting a config onto the pure-gen module system, instead of rewriting it up front. An
escape hatch, **not** the fast path.

**Cost profile** (cited — [gen hub `BENCHMARKS.md`](https://github.com/sini/gen/blob/main/BENCHMARKS.md#compat-mode)):

- **leaf-type shims are free** — a nixpkgs leaf's `.merge` is trivial, so the engine keeps the full
  speedup: hybrid **0.62×** of nixpkgs cpu, vs pure gen-merge's **0.63×**, at `scalar` n=16000.
- **structural-type shims give the win back** — nixpkgs `submodule.merge` runs `lib.evalModules` per
  instance, dragging the nixpkgs engine into every subtree: hybrid **0.96×**, vs pure **0.44×**, at
  `registry` (`attrsOf submodule`) n=2000.

So keep den-hoag's hot registry/aspect paths on gen-merge's structural strategies; reserve nixpkgs
types for the leaf/custom-type edges of a port.

**One-way boundary** — types flow nixpkgs → engine, not the reverse. A nixpkgs type plugs INTO
gen-merge because it carries `.merge`; a gen-types checker does **not** run inside nixpkgs'
`lib.evalModules`, because it is verify-only (no `.merge`).

**Purity** — nixpkgs enters here as a VALUE at an option; `lib/` never gains a nixpkgs dependency
(enforced by `ci/tests/purity.nix`) — the same value-injection philosophy as
[gen-flake](https://github.com/sini/gen-flake).

## Byte-mode scope (and the deferred structural seam)

This is **byte-mode**: it reproduces nixpkgs' order-sensitive merge exactly — the cut-over
conformance oracle and the NixOS terminal contract. It does **not** implement the confluent
semilattice merge, structural equivalence (`≈ₛ`), or pre-eval identity dedup — those are a separate,
deferred mode. The per-option combine is a **swappable kernel**: byte-mode passes the
nixpkgs-faithful kernel; the structural mode later swaps a confluent-join kernel without changing the
engine skeleton (see `2026-07-02-structural-identity-dedup-spike.md`).

## Known byte-mode boundaries (deliberate)

- **An explicit `key` spelled like an anonymous module's never meets it.** Module imports are graph
  edges and a module is a node, identified by nixpkgs' key rule: an explicit `key` (a path module's
  own, read after application, else its path) in one namespace, an anonymous module (`<importer>:anon-<n>`) in another. nixpkgs keeps the
  two in one string namespace, so a module with `key = ":anon-2"` merges there with the second
  anonymous top-level module (`[ { l = [ "a" ]; } { key = ":anon-2"; l = [ "b" ]; } ]` after a
  declaring module reads `[ "a" ]` in nixpkgs); here they are two nodes and read `[ "b" "a" ]`
  (`ci/tests/module-graph.nix`, `test-a1-…`). Everywhere else the module set and its order are
  nixpkgs': a diamond or a repeated key is one node, the closure is breadth-first, and the first
  occurrence reached wins, taking its own imports.

- **A keyed module may publish its key comparison, `__keyEq = { subject; decide; }`**, a key nixpkgs
  does not have. Where a later occurrence shares the key of the one kept, and either publishes it, the
  pair is decided rather than the later one dropped: `decide kept.subject later.subject` true is one
  module; false, a non-boolean, or only one of the two publishing it is refused by name, the same in
  both import orders wherever both occurrences publish one symmetric `decide`, as gen-schema's do;
  gen-merge applies the kept occurrence's `decide`. A throw inside `decide` propagates. Where neither
  publishes it, nixpkgs' rule holds and the later occurrence is dropped. Two occurrences of one
  spelled path are the one file and keep nixpkgs' rule; two different path files sharing an in-file
  key, or a path import sharing its key with a content module, are decided like any other pair. A module publishing `__keyEq` without a `key` is refused by name. gen-schema keys a
  kind with parents by its mark and publishes its sealed comparison here (`ci/tests/key-eq.nix`).

- **An import cycle terminates.** A keyed or path cycle (`a` imports `b` imports `a`, or a module
  importing itself) closes over its finite set of node ids and each module contributes once
  (`test-c1-…` to `test-c4-…`). nixpkgs overflows the stack on the same modules, uncatchably, so the
  engine is more defined than the reference here. Data minting fresh keys without bound (a function
  module returning `key = "k${toString (n + 1)}"` and importing its successor) is non-well-founded
  and still diverges. So does a self-referential import chain of anonymous, unkeyed modules: an
  anonymous module has no identity to dedupe on, so the chain overflows the stack uncatchably, as
  nixpkgs does on the same modules.

- **A check-only `mkOptionType` refuses where nixpkgs' default merge is silent.** Two definitions
  that are attrsets sharing a key whose values are not `==`, or that are functions (functors
  included), are refused by
  name (`ci/tests-error.nix` `mkoptiontype-default-merge`); nixpkgs keeps the FIRST file's value at
  the key (`{ a = 1; }` in the first file, `{ a = 2; }` in the second ⇒ `{ a = 1; }`: its
  definitions list runs in reverse file order and `//` is last-wins over that list), and for
  functions aborts uncatchably or unwraps a `{ value = …; }` result. Every other arm of the default is nixpkgs' value, with "equal"
  meaning the evaluator's `==` on each definer's own value, and a shared key's values are forced
  where nixpkgs forces none, at the read of that key. The attrset refusal fires where its key is
  read and names that key's path (`heddle.a`), with the values the files set there; the key set and
  every other key read as nixpkgs' do, so a key whose definitions read a sibling of the same option
  (`x.a = config.x.b` in two files, `x.b = 1` in a third) serves `1` as nixpkgs does. The fold is
  `unionAgreeing`, the `attrs` fold's own construction. The price, stated with the 2026-09-25
  ruling: a nixpkgs module relying on silent last-wins attrset merging under a check-only type is
  refused here. The price of deciding per key, measured with every value forced: about one thunk
  and two calls per key over deciding every shared key before returning the set; a read of the key
  set or of one sibling is cheaper, since it pays no other key's `==`.

- **At that shared key the three evaluators split in one stated case.** `==`'s identity
  short-circuit (the Nix manual, *Value identity optimization*) compares value *slots* on upstream
  Nix and Determinate and object identity on Lix. The fold compares each definer's own slot
  (`slotsDiffer`), so between functions "equal" is identity, which is sound: no evaluator
  accepts two different functions (`ci/tests-error.nix` `mkoptiontype-default-merge`, distinct
  closures). `==` also treats an int as equal to the same float, and two derivations with one
  `outPath` as equal, on every evaluator. The three agree wherever the definitions hold one value in
  one slot: a value bound once and written at each site, and a module argument supplied through
  `specialArgs` (`ci/tests/shared-key-identity.nix`, cells kept ×3). They split when the same
  function, or one value holding an attribute that throws when forced (a nixpkgs package set), is
  held in a *different* slot by each definition: a selection written at each site (`lib.id`,
  `h.pkgs`), a `with`-bound name, a separate `import`, a function result, or a module argument
  supplied only through `_module.args`. There Nix and Determinate refuse by name (a function) or
  throw the value's own error, and Lix keeps the value. Two kinds of residue, priced differently:

  - *User-made copies* cannot be made to agree: upstream Nix has no observer of closure identity, so
    a relation it can compute cannot tell "one closure in two slots" from "two closures of one
    lambda". Calling them equal drops a distinct function silently; calling every function unequal
    refuses values all three accept today. Pinned per evaluator by
    `test-a-function-reached-by-selection-answers-as-the-evaluator-s-own-identity`.
  - *The `_module.args` copy is chosen, not forced.* One shared cell per argument name per
    evaluation removes it on all three evaluators; it costs thunks on every nested submodule
    evaluation, which the hub perf-bench's kindMatch bounds do not admit today, so it is not paid.
    `test-a-function-passed-through-module-args-answers-as-the-evaluator-s-own-identity` pins it,
    and is meant to go red on Nix and Determinate when a landing pays that price.

  `mergeLeaf` and `leafFold` answer as nixpkgs' `mergeEqualOption` does on the same evaluator, this
  split included.

  The `attrs` fold is a second site of the same rule, through the same binding (`slotsDiffer`):
  definitions that set one key to equal values serve that key, and different values refuse it by
  name (`ci/tests-error.nix` `attrs-container`). "Equal" is the evaluator's `==` on each definer's
  own value, so the split above holds there too, and so do `==`'s two equations of values that are
  not identical: an int against the same float, and two derivations with one `outPath`, serve the
  value nixpkgs' `//` keeps and drop the other definer's (its numeric type; its attributes besides
  `outPath`), exactly as nixpkgs does. A function at a shared key against another function in a
  different slot refuses with its own text, since `==` cannot show two functions to agree; against a
  non-function it is a different value. The comparison is per key: a disagreement refuses where its
  key is read, so the key set and every other key still read as nixpkgs' do. The price, paid once per
  evaluation of the option, on the first read of that key: `==` walks two equal copies held in
  different slots in full, where nixpkgs' `//` forces neither; a value in one slot is decided
  unwalked. **An interpreter error inside two equal copies aborts uncatchably at that read, a
  declared exception to the rule that every refusal is catchable**: `{ a = { p = 1; q = ({ }).nope; }; }`
  written at two sites aborts with `attribute 'nope' missing` where nixpkgs serves `p`. `tryEval`
  catches only `throw` and `assert`, so no compare turns the error into a refusal, and the one
  construction that avoids forcing it, an equality that compares nested sets per sub-key, is a new
  relation in place of `==` that only moves the abort to the nested read a realization forces anyway.

  The same rule, through the same binding (`slotsDiffer`), decides the base module arguments two
  `(submodule …).withArgs` declarations of one option state: one bound value passed by both (one
  nixpkgs `lib`, one function, a `specialArgs` formal each declaring module hands on) merges on
  all three evaluators, decided at its WHNF; an argument only one declaration states is never
  compared and never forced. The user-copy residue is the same: where each declaration holds a
  *different* cell of one value that throws when walked (`{ lib = h.lib; }` at each site, or
  `lib // { }` at each site), Nix and Determinate throw the value's own error and Lix merges. It is
  stated, not converted into a named refusal: a `tryEval` there would turn the split into a
  quieter one (refused on two evaluators, merged on the third).

- **A module formal that `specialArgs`, `config`, `options` or `prefix` supplies is that attribute
  itself, not a copy**, in both strata: the value stratum's `callM` and the declaration stratum's
  `callD` alike. nixpkgs' `applyModuleArgs` copies every formal; `callM` applies a module
  to `extra // baseArgs` (and `callD` to `extra // declArgs`), so a `baseArgs` formal is `baseArgs`' own attribute (0 thunks and no
  allocation beyond the application's one `//`), and every module holds one slot. A module whose
  every formal is in `baseArgs` (`{ options, ... }`) is applied to `baseArgs` itself, which is that
  union key for key, so it pays neither `extra` nor the `//` (`callD` likewise over `declArgs`). Observable through any `==`: with `specialArgs = { inherit fa; box = [ fa ]; }` and `fa` a
  function, `[ fa ] == box` in a user module reads true on all three evaluators, where nixpkgs reads
  false on Nix and Determinate and true on Lix. nixpkgs is evaluator-split there, so no single
  answer matches it everywhere; this one is uniform. Precedence (`specialArgs` over `_module.args`),
  default formals, the missing-argument message and laziness are unchanged. The price is nil:
  the application's `//` swaps its operands, and the hub perf-bench reads the copying form's thunk
  and allocation bounds.

- **Two structurally equal CYCLIC values abort uncatchably, a declared exception to the rule that
  every refusal is catchable.** Nix `==` is not total, and it recurses without bound on a pair of
  pointer-distinct, structurally equal cyclic values — `{ a = r; }`,`{ a = r'; }` with `r` and `r'`
  separate bindings of `{ s = r; n = 1; }` — or on any pair whose lockstep `==` reaches a back edge
  before a difference. The class has four members, all exiting
  `stack overflow; max-call-depth exceeded` (Lix: `stack overflow (possible infinite recursion)`),
  which `tryEval` does not catch: the check-only
  `mkOptionType` default's shared-key compare (`mergeDescriptorDefault`, above),
  the `attrs` fold's shared-key compare (above), the no-fold leaf combine (`mergeLeaf`), and its
  exported twin (`leafFold`). 6a508e3 aborts on the same input at the first, third and fourth, so
  this is a boundary the folds inherit, not one they introduced. The two attrset folds decide per
  key (`unionAgreeing`), so they reach the abort only at the read of the cyclic key itself; the key
  set and every sibling serve.
  `mergeLeaf` and `leafFold` are byte-parity with nixpkgs: its own `mergeEqualOption` aborts
  uncatchably on the identical input. `mergeDescriptorDefault` and the `attrs` fold are the
  departures — nixpkgs' `//` never compares the shared key, so it silently keeps the last file's
  cyclic value where these folds abort. The exception is argued, not merely declared: no pure-Nix observation (`typeOf`, attribute
  names, selection, `==` on non-container leaves) tells a cyclic binding shared by both definitions
  apart from two freshly built, structurally identical cycles — both unfold to the same infinite
  tree, so a bounded pre-flight that refuses the latter also refuses the former, which nixpkgs
  accepts and this fold accepts today, and one that instead accepts on exhaustion is a silent drop
  past its bound. Every construction changes an answer this fold gives today without deciding the
  input that aborts, so the abort stands as the exception rather than behind a door.

- **A type's docs phrase elides past 128 composing nodes.** An exported type's `description` and
  `descriptionClass` are nixpkgs' phrase and class for the same construction, derived once at the
  export (`interface.phraseOfWithin`): a container composes its member's phrase, parenthesised by
  the member's class, as nixpkgs' `optionDescriptionPhrase` does. The phrase is rendered within a
  budget of `phraseBudget = 128` composing nodes (a container, a union or a freeform nest each cost
  one; a leaf, however wide, and a foreign member's stated phrase cost none), threaded through
  siblings, so it bounds the whole phrase tree and not only its depth. Past the budget the
  remaining members read `…`, where nixpkgs never elides: `listOf` nested 129 times departs, 128
  times is nixpkgs' phrase (`ci/tests/description-phrase.nix`). The most-composed phrase in
  nixpkgs' NixOS option tree composes 35 nodes, and no gen-typed declaration measured composes more
  than 3. Raising the ceiling is a one-constant change. A `deriveType` stating no `description`
  costs one node, however long its chain of such derivations: a derivation of a 128-node phrase
  elides where its base does not, and a derivation over a cyclic base, whose phrase always reaches
  the ceiling, renders one node less than its base.

- **A self-referential gen type has a finite phrase where nixpkgs' twin diverges.** For
  `v = nullOr (oneOf [ str (attrsOf v) (listOf v) ])` the budget is what ends the phrase: it is
  1 473 B, elided with `…`, nixpkgs' docs serve it, and every nixpkgs refusal over it (`type = v`,
  `either int v`, `listOf v`) is a named refusal `tryEval` catches; nixpkgs' own `valueType`
  diverges on the same reads, so here the export is more defined than the reference. A freeform
  nest of itself (`submodule [ { freeformType = self; } ]`) is bounded the same way. The price is
  per lap, not a byte figure: every lap of the cycle re-emits its leaves at no cost, so the phrase
  is bounded by 128 times the widest text one lap emits. A cycle through a 1 500-member enum gives
  a 1 850 177 B phrase, and a nixpkgs refusal over it still terminates and is still caught, at about
  444 MB RSS. No byte cap is placed on it: one would have to stay above the widest single leaf to
  keep parity, and it bounds no descent.

- **A cycle closed through a foreign record's `description` aborts uncatchably, a declared
  exception to the rule that every refusal is catchable.** A gen container reads a foreign member's
  phrase from the member's own `description`, as nixpkgs' containers do. When that foreign phrase is
  itself a cycle, the read dies with `infinite recursion encountered`. There are three instances:
  `listOf nv` over nixpkgs' self-referential `nv = nullOr (oneOf [ str (attrsOf nv) (listOf nv) ])`,
  whose divergence is inside nixpkgs' own `description` thunk, and `vm = nullOr (np.listOf vm)`, a
  gen cycle closed through a nixpkgs composer, which describes `vm` from `vm`'s own exported
  `description` (its `getSubModules`/`getSubOptions` refuse by name, the next bullet); and a `deriveType` whose `fields` states its base's `description`
  (`fields = b: { inherit (b) description; }`) over a base that holds the derivation, a caller's
  stated phrase built from the phrase its own member renders. Omitting `description` serves the
  same text within the budget. Before the phrase was derived all three served the constructor's name (`"listOf"`,
  `"nullOr"`) as their description; now the description, the docs over it and (for `listOf nv`)
  nixpkgs' refusal over it abort, as nixpkgs' twin `np.listOf nv` does in every arm.
  `ci/tests-process-cells.nix` pins the three deaths, each with a live control. The exception is
  argued, not merely declared: parity requires reading a foreign member's stated phrase; nothing
  observable separates a foreign record's stated `description` from a derived one without forcing
  it; and the structural alternative, re-rendering a stock-named foreign composer from its
  `nestedTypes` without reading its `description`, departs from nixpkgs on every stock composer
  with a stated override (49 of the 16 798 top-level NixOS options hold one in their phrase tree,
  `time.timeZone`'s "null or string without spaces" among them). Every construction changes an
  answer the export gives correctly today without deciding the input that aborts.

- **A cyclic type's spine and its redeclaration refuse by name past the type-walk fuel.** A cycle
  every back-edge of which sits under a constructor consuming the value is CONTRACTIVE, and its
  value observations (check, merge, refusal) serve. Two observations of the TYPE itself consume
  nothing, and nixpkgs' twin diverges on both:

  - `getSubModules`/`getSubOptions` of a forwarding container (`listOf`, `attrsOf`, `lazyAttrsOf`,
    `nullOr`) follow its element chain for at most `importedTypeWalkFuel` (32) steps. A stock
    nixpkgs record forwarding both reads to one element (`listOf`, `nullOr`, `attrsWith`, `uniq`,
    `functionTo`, `coercedTo`'s `finalType`) is a step of the same walk, taken to bound the chain
    and never to answer for the record: once the chain is shown to end, the record answers for
    itself, so one whose sub-protocol was overridden answers its override, as nixpkgs' own container
    over it does. So `r = nullOr (listOf r)`, and the same cycle through any of those nixpkgs
    records, is SERVED by `evalModuleTree` (`[ null [ null ] ]`), and nixpkgs' evaluation and docs
    over it are named refusals `tryEval` catches where nixpkgs' twin aborts.
  - A type merge (a redeclaration, `exportType`'s `typeMerge` and `binOp`) asks the boundary's
    decidability walk of both operands once, at its entry, and refuses a pair that does not bottom
    out within the fuel; its descent asks again of no sub-tree. So any cyclic type declared twice,
    the union-closed json shape included, refuses by name, in gen's engine and through nixpkgs'.
    The walk stops at a gen nesting type, whose relation unions module sets and descends into no
    type, so a submodule's modules are never forced by it.
  - THE PRICE: a finite chain of 34 or more forwarding containers below the container asked refuses
    its spine where it was answered, a finite type nested 32 containers deep refuses its
    redeclaration, and a cycle through a stock nixpkgs container whose override stops forwarding
    refuses its spine where the override was answered. So nixpkgs' `evalModules`, which reads
    `getSubModules` when it declares an option, refuses a value through such a gen type where it
    accepted it; gen's `evalModuleTree` still serves the value, the all-nixpkgs twin still accepts
    it, and nixpkgs' own fix-up drops the override on its option path anyway. All three are named
    refusals; the deepest real family measured in nixpkgs' vocabulary is 2. A redeclaration pays
    one bounded walk per operand, linear in its depth (about 12 thunks per operand level); a single
    declaration pays no thunk, and one attribute per forwarding container (`ci/tests/cyclic-types.nix`). THE
    REMEDY is in the refusal: close a cycle through a union (`either`, `oneOf`) or a submodule, which
    answer for themselves, or nest a finite chain less deeply. THE ESCAPE HATCH: a gen record whose
    `substructure` states no `forward` answers for itself, which ends the spine walk there. The
    redeclaration walk states none, as the foreign arm's identical walk states none.
  - nixpkgs' docs over a cycle through a submodule (`r = listOf (submodule { options.x = mkOption { type = nullOr r; }; })`) still diverge, in nixpkgs as here: every `getSubOptions`
    gen answers there is finite, and the walk that does not end is nixpkgs'
    `optionAttrSetToDocList` recursing through nested options, whose own remedy is
    `visible = "shallow"`.

- **A type that is its own derivation, and an unguarded cycle, abort uncatchably, a declared
  exception to the rule that every refusal is catchable.**

  - `d = deriveType { … } "d" d` states no constructor between `d` and itself: it is the equation
    `d = d`, and denotes no type. `deriveType` reads its base when it is built, so Nix black-holes
    the thunk (`infinite recursion encountered`) before any gen code observes a value, as nixpkgs'
    `d = d // { … }` dies. Neither serving nor refusing is available: a lazy `deriveType` would die
    the same way at its first read, since every field of `d` is read off `d`.
  - A NON-CONTRACTIVE cycle, one whose back-edge passes no constructor that consumes the value
    (`r = either int r`, `either r int`, `nullOr r`, `deriveType { … } "d" (either int d)`), has no unique
    fixpoint: the least is `int`, the greatest admits everything. Its out-of-domain `check`, the
    refusals that read it, and for `either r int` even the in-domain check, die in the call-depth
    channel (`stack overflow; max-call-depth exceeded`) on all three evaluators, as nixpkgs' twins
    do. A construction exists that would refuse it by name, a lazily-forced contractiveness walk per
    union node, and it is not taken, by priority and cost (*defaulted, reversible*): nixpkgs aborts identically and serves no value to keep parity with; the walk's cost on
    `check`'s hot path is unmeasured; it would refuse a flat `oneOf` of 34 or more members that
    serves today unless union width is charged apart; and it would leave a cycle alternating foreign
    and gen unions unbounded.
  - `ci/tests-process-cells.nix` pins both deaths (`cyclic-derive-self`, `cyclic-unguarded`) on
    their channels, with a live control (`cyclic-guarded-control`).

- **A foreign knot closed through a gen door aborts uncatchably at construction, a declared
  exception to the rule that every refusal is catchable.** `r = mkOptionType (np.either np.int (np.listOf r))` and `d = deriveType { … } "d" (np.either np.int (np.listOf d))` die with `infinite recursion encountered` on every reader, where nixpkgs' twin (`np.mkOptionType` over the record,
  `base // { … }`) constructs and serves its check. The import decides at construction whether a
  stock foreign container crosses as gen's own container (it may nest) or as itself (it cannot),
  and the two records differ in their key set: `split` and `recarry` against `phraseClass` and
  `retainedRelation`. The two inputs that decide it differ only in an element (`np.attrsOf np.int`, `np.attrsOf sub`), at any depth, so the decision forces the elements, and in a knot the
  elements reach the value being built. A container outside the six is the same case through the
  import refusal's walk (`uniq`). The class is every such knot, through either door and through
  `either`, `listOf`, `attrsOf`, `nullOr` and `uniq` alike, `declaresNesting = false` on the
  record at the door included, since the re-homing decision does not read the marker; one whose
  door sits inside the cycle (`r = np.either np.int (np.listOf (mkOptionType r))`) constructs and
  dies at its first fold instead. **The way out:** close the knot on the foreign side and carry it
  through the door once, `mkOptionType (let r = np.either np.int (np.listOf r); in r)`, which
  serves nixpkgs' value. Through `deriveType` the same knot serves too, but only because the walk
  answers "may nest" at its fuel's exhaustion and so re-homes a cyclic container; an acyclic
  foreign container there is the vocabulary's named refusal. A cycle through a container outside
  the six is then the walk's named refusal at its fuel, with its three remedies.
  `ci/tests-process-cells.nix` pins both deaths and the way out. The exception is
  argued, not merely declared: a record whose key set does not wait on the walk is a fixed shape,
  and both fixed shapes change answers given today. Crossing every stock container as itself
  stops re-homing one that nests and refuses `deriveType` over it; crossing every one as gen's
  container drops an override on one that nests nothing and admits `deriveType` over a foreign
  container, which the vocabulary refuses.

- `raw` uses `mergeEqualOption` (multiple equal-valued defs collapse); nixpkgs `raw` is
  `mergeOneOption` (throws on >1 def even if equal). Not exercised by the surface — add a strict
  `raw` only if a consumer hits it.

- **A leaf `freeformType` folds the undeclared plane as one leaf value, so key-level properties
  are returned as data, not discharged.** A type with no fold of its own (a gen leaf, a bare
  `mkType`, a foreign record stating neither `merge` nor `check`) folds the plane by `mergeLeaf`,
  the fold the option site gives it: one file passes through, equal files agree, anything else is
  refused by name. `q = mkIf false "a"` under `freeformType = types.str` therefore reads
  `{ _type = "if"; condition = false; content = "a"; }`, the value nixpkgs gives on the same type and
  the value a foreign leaf gives at this site (`ci/tests/undeclared.nix` cell 22). Whether the
  plane should discharge or refuse such properties is an open design question.

- **A module's `_module.check` is refused by presence; nixpkgs honours it.** nixpkgs declares four
  `_module` options. gen-merge reads `args` and `freeformType` itself and takes `check` and
  `specialArgs` at `evalModuleTree`'s door, so a module defining either is refused by name, any
  value, `mkIf false` included:
  `` gen-merge: `_module.check' is not read from a module: pass it as `evalModuleTree { check = …; }'; defined in <file> ``.
  The refusal fires before the realizer, so it is what an undeclared sibling meets first. Whether to
  honour the option as nixpkgs does is an open design question.
  `_module.specialArgs` is refused the same way (`… is set by the caller, never by a module …`):
  nixpkgs drops a module's definition silently, and a silent drop is not a value. A non-attrset
  `_module` is refused (`` `_module' must be an attribute set, and this one is <type>; defined in <file> ``),
  as nixpkgs refuses it. Every other `_module.<x>` is an ordinary config path, as in nixpkgs: refused
  as an option that does not exist under `check`, listed on `.undeclared`, absorbed by a
  `freeformType`, merged by a declared `options._module.<x>`. Declaring `options._module` as a
  single option whose type carries no sub-options is refused by name, as nixpkgs refuses it (it would
  be a parent of the engine's own keys). A `submodule`-typed `options._module` takes every
  `_module.<x>` the engine does not own, as nixpkgs' does once it merges its own `_module` options
  into the submodule (`ci/tests/module-key.nix`). An engine-owned `_module.<k>` re-declared, as an
  `options._module.<k>` or inside such a leaf, is refused where nixpkgs refuses it with its own
  declaration taking part: a type that does not merge with the engine's own, or a field the engine's
  own declaration states (`` gen-merge: the option `_module.<k>' in `<file>' is already declared by the engine's own `_module' options ``); a nixpkgs `submodule` leaf is judged by nixpkgs itself, in
  its words, with the engine's declarations folded first. An owned key declared as a group of
  options is refused as the parent of options its type cannot carry. Two modules' fields right-bias,
  as every redeclaration does. An accepted `apply` maps the value where the engine reads the key,
  and on `args` the set it maps holds a nested child's `name`, so the `name` its modules receive is
  the applied one; an accepted `readOnly` refuses a second definition (nixpkgs' own module defines
  `args`, and a re-declaration's `default` counts). The departures from nixpkgs, each with its
  ground:

  - *Eager at `args` and `specialArgs`.* The refusal fires on every config read, where nixpkgs'
    fires only when the key is read: the engine's redeclaration refusal is eager everywhere, and the
    unread type nixpkgs passes is one that never runs.
  - *`readOnly` at `args`.* nixpkgs dies with a stack overflow; this engine refuses by name.
  - *The door key.* An `apply` or `readOnly` on `check` is refused by name
    (`` … is read only from `evalModuleTree { check = …; }' ``), because the engine does not run it;
    nixpkgs honours it. It waits on the door's own design.
  - *The ordered fold.* Two `apply`s, at the group or inside the leaf, keep the later, as every
    doubled field of a redeclaration does here, `specialArgs` included; nixpkgs refuses the pair.
  - *`config._module.args` inside a module.* It holds the modules' arguments (and a nested child's
    `name`) only. nixpkgs' also holds `extendModules` and `moduleType`; this engine has no
    `extendModules`.
  - *`config._module.check` in a child of an unchecked tree's `.type`.* The view reads the
    strictness that governs the child's refusal of an undeclared key, which is nixpkgs' value under a
    strict parent. Under a caller `check = false` that child runs lax, because this engine's `.type`
    carries its evaluation's `check` and nixpkgs' does not, so the view reads `false` where nixpkgs
    reads `true` (and refuses the key).
  - *Both refuse, by different causes.* Three inputs nixpkgs refuses as a parent or as already
    declared are refused here as types that do not merge or as a single option. A re-declared `specialArgs` type the caller's
    set does not satisfy refuses on the read in both, as `not of type`, naming `<gen-merge>` as the
    definition where nixpkgs names `lib/modules.nix`.
  - *A redeclaration never read.* An ordinary option redeclared with clashing types refuses here and
    exits 0 in nixpkgs when it is not read; that is the engine's standing rule.
    `lint` refuses the three module-input refusals the engine fires before merging
    (`specialArgs`, `check`, a non-attrset `_module`) and reports nothing for an unknown `_module.<x>`,
    where the two engines agree.

- **A redeclared option's type refuses where a gen-native relation refuses, even where nixpkgs
  accepts.** The declared-type list folds as nixpkgs brackets it, and on every all-foreign list whose
  joins keep their operands' names the two engines agree, on the declaration and freeform planes
  (see "Redeclaring an option"). The
  departures are all over-refusals, each at a fold step whose earlier operand is a gen type whose
  relation refuses the later one. Under a **foreign** outer container the element relation runs in
  foreign code and accepts what nixpkgs accepts. The list fold's cost is linear in the number of modules
  that declare one option with a type, in thunks and calls ("Redeclaring an option", **Cost**). Measured members:

  - `gt.attrs` against `lib.types.attrs`, in the order nixpkgs accepts (the foreign `attrs` fold is
    `//`; gen's `attrs` refuses a disagreement, so it refuses a partner that states no fold of its own);
  - the same pair under a gen container;
  - an earlier gen relation vetoing a later foreign relation that answers another type
    (`[gt.str, Fint]` with `Fint = int // { typeMerge = _: str; }`, and a refined type before `Fx`);
  - a refinement under a gen container against its bare element (`[listOf R, listOf int, listOf int]`,
    where nixpkgs accepts `listOf` and drops the refinement).

- **A foreign join that drops a name an operand states refuses, even where nixpkgs accepts** ("A
  foreign join that drops an operand's check refuses"). These departures are also over-refusals,
  except one that answers the operand. Measured members:

  - a check family whose join renames it: `port ∥ int` in both orders, `u8 ∥ u16`,
    `unsigned ∥ positive`, `numbers.between` pairs and `passwdEntry str ∥ str`, directly or under a
    nixpkgs or gen container;
  - two separately built `ints.between 0 1`, since two calls build two values;
  - a foreign relation, authored or inherited, that answers a type keeping neither operand's name
    (`[int, str, Fx]`, which nixpkgs accepts as `int`);
  - one shared value declared twice, `[port, port]`, which answers `port` where nixpkgs answers `int`;
  - one shared record imported through `mkOptionType` and declared twice, which refuses where the bare
    twin keeps its operand: the imported record meets the engine's own import of its partner, and
    Nix `==` does not survive that path.

- **A type merge that drops a wrapper's check refuses, for a gen record, even where nixpkgs serves**
  ("A type merge that drops a wrapper's check refuses, at every depth"). Measured members, each
  served by nixpkgs: `addCheck int p` beside `int` in either order, beside `union [ int ]`, under
  `listOf` and in a three-declaration list; two separately written `addCheck int p`, which is the
  one legitimate input refused (the remedy is one shared value). One shared wrapped value declared
  twice merges and keeps its check, where nixpkgs serves what the check rejects.

  Not covered, because no name separates the check from its base and a foreign record states no
  check witness: an `addCheck` over a nixpkgs type that keeps its base's name (`addCheck lib.types.int f`, `nonEmptyListOf`). Nor a drop under a
  key `nestedTypes` states that names no role this boundary carries (`freeformType`,
  `coercedType`/`finalType`, an `attrTag`'s tags): it is not in gen's vocabulary, so a join is not
  judged over it.

- **A `nestedTypes` key that names no gen role crosses verbatim, and gen-merge is blind inside it.**
  An imported record keeps every key its roles did not consume (`freeformType`,
  `coercedType`/`finalType`, an `attrTag`'s tags, an author's own key) as `unroledNested`, and
  `exportType` re-publishes it beside the role's spelling, so the type reads as nixpkgs' own does
  (`test-a-nestedTypes-key-naming-no-role-crosses-verbatim`). A key the role's spelling would itself
  publish cannot be kept beside it, so that record is refused by name at import rather than losing
  one of the two: the element stated at the top-level `elemType` while `nestedTypes.elemType` holds
  an option record (`test-an-unroled-key-the-role-would-publish-is-refused`). No role is assigned to such a key, so
  nothing on this side reads it: a join does not judge over it (the bullet above), and the identity
  walk never descends through it — below such a record the walk sees only what the record's module
  set states (`getSubModules`/`getSubOptions`; an `attrTag`'s tags and a `coercedTo`'s `finalType`
  state theirs there). An identity reachable only through such a key is compared by the byte oracle
  and not tracked by the warm refusal. The same blindness holds inside a redeclared nixpkgs
  submodule's `freeformType`: the two halves' freeform types join below the walk's sight, so the
  witness does not see a check that join drops (`freeformType = attrsOf port` redeclared against
  `attrsOf int` serves `70000`, as nixpkgs does; `submodule-laziness`, row `freeformCheckDrop`).

- **A nixpkgs submodule's `nestedTypes` is never forced, and what that recognition cannot see is
  served as a module set.** nixpkgs' `submoduleWith` states `nestedTypes` as an output of
  evaluating the type's own module set with no definitions, a read nixpkgs never takes; taking it
  refused "option does not exist" on a redeclared submodule whose halves complete each other. A
  record whose functor payload states `modules` and which states a non-null `getSubModules` is
  recognised for laziness only (the one exception to reading what a record carries off its
  carrying spelling): its role is the module set, read off `getSubModules`, and its `nestedTypes`
  crosses as an unforced thunk (`ci/tests/submodule-laziness.nix`, a poisoned `nestedTypes` on
  every route). The residue, pinned (`test-the-residue-is-served-as-a-module-set`): such a record
  that also states a static role in `nestedTypes` (a nixpkgs submodule given an `elemType` by `//`)
  is served as a module set with that role unread; a record whose `nestedTypes` is evaluation-derived
  but whose payload states no `modules` (a hand-copied submodule) or which states no
  `getSubModules` is not recognised: one stating a module set is mounted at an option root as
  nixpkgs' `fixupOptionType` mounts it (arm (T), the root fix-up), before its `nestedTypes` is
  read, and one stating none keeps the refusal, pending the release-parity ruling. At an option root
  a recognised record is mounted as its rebuild too, so one whose rebuild lies about its roles is
  served what nixpkgs serves. A container whose payload states
  `modules` beside a static element and states no `getSubModules` keeps both its refusals.
  "Served" holds for an honest record only: a recognised record answers the decidability pre-check
  without a walk, so its own `typeMerge` runs unguarded, and a hand-built one whose `typeMerge`
  recurses through itself overflows the stack uncatchably where the type-walk fuel refused it by name.
  The nesting walk is blind inside a recognised record's `freeformType` as well: a gen nesting type
  there is neither threaded nor refused but evaluated standalone through the bridge, as a declared
  sub-option's is, so under a stock `uniq` OQ11 (d)'s named refusal becomes a silent standalone
  evaluation whose value equals nixpkgs'
  (`test-a-freeform-gen-nesting-type-serves-through-the-bridge`).

- **A sub-option declared beneath an option whose type is a submodule is refused by name, where
  nixpkgs merges it** (the `nix.settings` shape: `options.thing` of type `submodule { … }` in one
  module, `options.thing.sub` in another). nixpkgs folds the sub-option into the submodule; here
  the declaration merge refuses it as a leaf/group collision, naming the option
  (`ci/tests-error.nix` `test-leaf-group-collision-refusal-names-the-option`).

- **An identity inside an instance is not walked.** The identity walk stops at an instance (a
  position whose declaration declares `id_hash`) and reads only that instance's `id_hash`, never its
  other options. A second minted identity held in one of them (an instance's own `listOf` of
  instances, say) is compared by the byte oracle and not tracked by the warm refusal: an edit moving
  it re-composes warm, equal to cold, whatever container holds it. Only the outermost instance on a
  path is a tracked identity (`test-the-walk-reads-no-raw-payload`, row `innerInstance`).

- **A `mkOptionType` stating no relation merges with one construction and refuses two of one name.**
  Its check is a caller's function, so the name cannot say two of them are one type; the relation
  compares the reified records under Nix `==` over `closuresFirst`'s subject, which terminates on
  two constructions (`ci/tests/samename-relation.nix`). Three departures,
  stated:

  - *One value declared twice merges and keeps its check* (`[g, g]`), where nixpkgs refuses the
    second declaration. A value equals itself under Nix `==`, so it is one construction.
  - *A `//` derivation is another value.* `g // { … }` declared beside `g`, or twice, is refused,
    loudly, even where the derivation changes nothing the check reads.
  - *A selection reaches the one record.* `h.g` written at each declaration merges on all three
    evaluators (`test-one-construction-merges.reachedTwice`): the subject's closures are the
    record's own attributes. The evaluator split of the shared-key bullet above belongs to a
    FUNCTION reached by selection at each site, which is where the companions' compared
    components meet it (gen-schema, gen-aspects READMEs).

  `closuresFirst`'s enumerated exceptions (a graft; a record in open caller content) and its value
  move (a listed field that throws propagates) are stated at its declaration in `lib/interface.nix`.
  A `records` member that is not an attrset (`type = "str"`, a lambda) contributes `{ }` and the
  value decides (`test-a-non-record-in-records-answers`).

- **A `check = false` tree merged where no report is carried refuses, per level, a key nixpkgs would
  drop.** At an element site, a freeform plane or the public `mergeDefs`, the reference (`evalModules`
  with `_module.check = false`) returns a value with the key gone; gen-merge refuses it by name, since
  every read here yields a value or a named refusal and a silent drop is neither. Where nixpkgs
  checks, both refuse at the same level on the same read. The finding can come from the tree type's
  **own** module set, so such a type refuses at every non-reporting use, a fully discharged
  `lazyAttrsOf` element included (its empty value is the strict fold over no definitions).

The module reader is nixpkgs' `unifyModuleSyntax`: a module is structured iff it carries `config` or
`options`, a structured module admits exactly nixpkgs' `attrsToRemove` and refuses any other key by
name (naming every surplus key and the file, whatever `check` says), and a shorthand module strips
nixpkgs' `shorthandAttrsToRemove` and reads every other key as config (`require` joins `imports`;
`meta` on a structured module is folded into config). Both lists also carry gen-merge's engine keys
`__pureModule`, `__reservedKeys` and `__keyEq`, and the shorthand list carries `_module`, which a shorthand module reads as config.
A top-level `_module` beside `config`/`options` is refused by name as an unsupported attribute, as
nixpkgs refuses it. Its departures:

- `_class` is stripped in both forms and never checked. gen-merge has no `class` parameter, which is
  nixpkgs with `class = null`.
- `disabledModules` is **refused by presence**, in both module forms and before the surplus check:
  gen-merge does not implement module removal, so the modules it names would stay enabled. The empty
  list is refused too, which over-refuses relative to nixpkgs (it accepts `[ ]`); refusing on
  presence never forces the list. *Defaulted, reversible.* Implementing module removal is deferred
  work, re-armed by a consumer that needs it. Its reach is every door below, so a declaration-only
  read — `.options`, `declaredOptions`, `substructure.declares` — refuses the empty list too, which
  nixpkgs accepts on those reads as on any other.
- **The refusals above fire on each door's first read of a module**, as nixpkgs' `unifyModuleSyntax`
  does. That read is the declaration stratum's, which every `evalModuleTree` read forces before any
  config, and which `declaredOptions` and `substructure.declares` read directly, at any nesting; `lint`
  refuses at its own first read. So a declaration-only read refuses exactly as a config read does: on
  the typo `{ options.b = mkOption …; option.c = mkOption …; }` both `.options` and `declaredOptions`
  refuse by name, where they once answered `[ "b" ]` silently. A warm trace over an edited module the
  reader refuses is refused with it: `warmDecision.mode` on a surplus-key edit is refused where it
  once read `"warm"`, and on a `disabledModules` edit where it once read `"cold"`.
- **A value that is not a module is refused by name**, where nixpkgs aborts. A module is a path, a
  string naming an absolute path (imported, as nixpkgs does), a function or an attrset; anything else
  — an `imports` element, a top-level module, or a nesting type's definition read as a module, such
  as `{ imports = [ "x" ]; }` on a tree that declares an option `imports` — is refused with
  `gen-merge: a module must be a path, a function or an attribute set, and this one is <type>`.
  nixpkgs fails the `import` uncatchably. `lint` refuses the same value with the same message, where it
  once reported no findings. A strict superset: no module nixpkgs accepts changes meaning.
- **A module function whose result is not an attribute set is refused by name, catchably** — parity,
  not a departure: it is `unifyModuleSyntax`'s own third arm, which nixpkgs words
  `module <file> (<key>) does not look like a module.` A module function is applied once, to the
  module arguments, and its result must be the module; a curried `a: b: { … }`, a returned path and
  any other non-attrset result are refused with
  `` gen-merge: module `<file>' is a function whose result is <type>, not an attribute set ``. It fires
  at the declaration stratum's read, so `.config`, `.options`, `declaredOptions`, an `imports`
  element, a `submodule` or `deferredModule` definition and a warm trace all refuse. The config read
  once aborted uncatchably (`expected a set but found a function`), and the declaration-only reads
  once answered silently. `lint` never applies a function module, so this arm does not reach it.
- **`__reservedKeys` reserves names in a module's import closure**, a key nixpkgs does not have. A
  module carrying
  `__reservedKeys = { names = { <name> = <refusal text>; … }; exempt = [ <attribute path> … ]; }`
  makes every module it imports refuse a top-level `<name>` with that name's text, followed by
  `` (module `<file>') ``. The closure is every route the collector follows: nested `imports`,
  `require`, function and functor modules (read after application), paths, and a whole-module
  `mkIf`/`mkMerge` (read after push-down). The marked module's own top level is NOT checked, and
  neither is an explicit `config.<name>`, which is the instance route. A module carrying every `exempt`
  path is not checked. The content is plain data a library supplies (gen-schema and gen-aspects mark
  a kind entry's definitions with the names they reserve, so a construction formal written in a
  module the entry imports is refused by name rather than read as instance config); gen-merge names
  no kind and no formal. The refusal fires at the declaration stratum's read, like the arms above.
  Three properties are stated, not hidden:
  - The scope is an inherited attribute along the import edge, as `_file` is, so it belongs to a
    module's **first occurrence** in import order. A path or keyed module reached first outside any
    scope is deduplicated before a scoped module re-imports it, and it is not checked.
  - A nested `__reservedKeys` replaces the inherited reservation for its own closure, so an empty
    nested one voids it. Like a hand-written exempt shape, that is a forgery, not an honest route.
  - A malformed marker (not an attribute set, `names` not an attribute set of strings, `exempt` not a
    list of string lists) is refused by name on the first module it scopes:
    `` gen-merge: module `<file>' is imported under a malformed `__reservedKeys': <what is wrong>. … ``.
    A marker on a module that imports nothing scopes nothing and is not read.
    `lint` keeps its own collector and does not thread the scope: it is a portability report, not this
    refusal.

These boundaries are mechanically checkable — see [Portable-subset lint](#portable-subset-lint).

## Portable-subset lint

`genMerge.lint modules → [ findings ]` (empty list ⇒ portable) statically flags the modules that
step outside the byte-mode surface, so the "runs on gen-merge and `lib.evalModules` byte-identically"
claim is verifiable, not asserted. The flagged kinds:

| kind                    | what it catches                                                                        | why it diverges                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| ----------------------- | -------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `order-pass`            | a config def carrying an `_type = "order"` marker (`mkOrder` / `mkBefore` / `mkAfter`) | ⚠ **STALE — the divergence this row names is CLOSED.** It was true while the order pass was absent (the marker was carried as an ordinary value and mis-ordered); the pass now ships and the two engines agree on order-marked defs. The finding still fires, so a module using `mkBefore`/`mkAfter` is reported non-portable when it is not. Retiring the finding moves shipped lint cells and is therefore held for its own change, not folded into the landing that made it stale                                                                                                                                                                                                                                              |
| `options-introspection` | a module **function** whose formals include `options`                                  | byte-mode `.options` is a minimal descriptor map (the merged decl tree), not the nixpkgs-shaped `options` structure                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `type-merge`            | the same option loc declared **with a `type`** in more than one module                 | on the type the engines agree on every all-foreign declaration list whose joins keep their operands' names (both fold it as nixpkgs brackets it, the later type deciding), and gen-merge departs by refusing where a fold step's gen-native relation refuses, a foreign join drops a name an operand states or a merge drops a gen record's added check, or by keeping one shared value declared twice (Known byte-mode boundaries); nixpkgs *additionally* refuses outright when both declarations carry any of `default`/`example`/`description`/`apply` (`bothHave`, ahead of the functor), where gen-merge right-biases those fields. The flag over-approximates on purpose — only the field-colliding pairs actually diverge |
| `function-to`           | an option type named `functionTo`                                                      | intentionally omitted from the type surface (wrap guard functions as data)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `unverifiable`          | an option type nested deeper than the type-walk fuel                                   | can't decide `functionTo` at that depth — reported rather than silently accepted (a portability lint must not false-negative)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |

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
on attrset modules, `import`ed path leaves (a path or a string naming an absolute path), and the
modules reached through `imports`. A
submodule's `getSubModules` is a separate nested eval — lint those by passing them to `lint`
directly. A recognised nixpkgs submodule's `freeformType` is not scanned, by either route: reading
it is the forcing the engine never takes, so here "never forces what the engine
wouldn't" wins over "must not false-negative" and a `functionTo` there is not flagged
(`test-the-lint-does-not-scan-a-submodule-freeformType`).

Run it over a module list (or wire it into CI as an accept-gate — `ci/tests/lint.nix` asserts it
accepts the whole equivalence corpus and rejects one fixture per construct):

```nix
genMerge.lint [
    { options.tags = genMerge.mkOption { type = genMerge.types.listOf genMerge.types.str; default = [ ]; }; }
    { tags = genMerge.mkForce [ "a" ]; }                       # portable — a plain override
  ]
# ⇒ [ ]   (portable)

genMerge.lint [
    { options.tags = genMerge.mkOption { type = genMerge.types.listOf genMerge.types.str; default = [ ]; }; }
    { tags = lib.mkAfter [ "z" ]; }                            # flagged — an order marker (see the ⚠ above)
  ]
# ⇒ [ { kind = "order-pass"; loc = [ "tags" ]; file = "<gen-merge>"; detail = "…"; } ]
```

## Purity

The library (`lib/`) is `nixpkgs.lib`-free — it is the *replacement* for `lib.evalModules`, so it
never calls it (enforced by `ci/tests/purity.nix`). nixpkgs enters only in `ci/` (the nix-unit
harness + the equivalence oracle's reference side).

A second, sharper purity holds inside the library: **the foreign `optionType` protocol is uttered in
exactly one unit.** Not "never imported" — never *spoken*. `ci/tests/interface.nix` reads it two ways,
because neither alone is enough: a token scan over the comment-stripped library source (which cannot
speak about `name`/`description`/`check`/`merge`/`_type`, since those are ordinary words this library
uses for its own things), and a name-blind arm asking who **mints** each of the fourteen — the gen
record carries none of them but `name`, and the export carries every one. Both arms carry a live
control in the same run, because a scan that cannot find anything reports exactly what a clean scan
reports.

## Testing

`nix develop ./ci --command ci` runs the nix-unit suites behind the read-roots guard, which refuses
when anything under a declared read root is unknown to git (any extension or name, `_`-prefixed
included; `git add` it or move it). The bare `nix flake check ./ci` and `nix-unit --flake ./ci#tests`
are unguarded: they read a git-filtered copy of the tree, so an untracked cell is silently absent
and the run stays green. The suites: `merge` (the 7-item primitive + priority subset),
`deferred` / `checking` (non-forcing + leaf verification), `oracle` (byte-identity vs
`lib.evalModules`, with mutation-teeth assertions), `compat` (nixpkgs `lib.types` on the engine),
`core-kernel` (the fixed-input short-circuit), `provenance` (the `.provenance` record shapes + forcing
contract), `bands` (`priorityBand`/`bandedLeaves` over real provenance: k1–k6, every unset reason), `lint` (the portable-subset checker — accepts the whole `oracle` corpus, rejects one fixture
per unsupported construct), `interface` (the protocol boundary: T3, the C-1/C-2/C-3 ceremony
predicates, and a mounted-in-real-`lib.evalModules` arm with its mutants), `type-merge-relation`
(C-4 — the engine's dispatch basis), `linkset` (the declared-disjointness export merge), and `purity`.

Two instruments sit outside the suites, because what they read is not an in-language assertion:

```bash
./ci/bench/either-totality.sh    # an EXIT CODE: an abort that escapes `tryEval` and kills a runner
./ci/bench/interface-cost.sh     # `nrThunks`: what the foreign protocol costs per type instance
./ci/bench/reserved-scope-cost.sh  # `nrThunks`: what `__reservedKeys` costs per scoped entry, against its bound
```

Running the suites directly through the nix-unit CLI (`nix-unit --flake ./ci#tests`, or the devshell
`ci` command) needs a raised stack — `ulimit -s unlimited` — at the default 8 MB: nix-unit's own
traversal of the deep module-system evals overflows it (the pre-commit hook and the devshell command
raise it automatically; `nix flake check ./ci` is a plain eval and does not need it).

## Theoretical foundations

- **byte-mode = the conformance oracle + terminal contract** (structural-dedup spike §3).
- **priority = one override rule**, the grepped subset (design spec §7), plus the nixpkgs **order
  pass** as compat vocabulary — precedence itself is gen's graph-position-and-provenance question, not
  the integer lattice's.
- **deferredModule = a lazy constructor**, inspectable before forcing (Lorenzen 2025 §2.3).
- **the `(loc, defs)` hook = the escape the engine rides** (nixpkgs `mkOptionType.merge`).
