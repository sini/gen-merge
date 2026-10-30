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
   desugars to a lowest-priority definition (no separate codepath), and a `readOnly` option counts it
   as a setting, as nixpkgs does: a default beside one definition is refused by name.
2. **freeformType** — `lazyAttrsOf` / `attrsOf` routing of undeclared keys.
3. **per-key `name` + `_module.args`** binding under keyed collections.
4. **self-referential `config` fixpoint** — one local `fix` per call; `config._module.args.X = config` lets siblings cross-reference.
5. **`imports` as graph edges** — each tree's modules are nodes keyed by nixpkgs' key rule; a diamond or
   a repeated key is one node (`ci/tests/module-graph.nix`). A merge collects them by a breadth-first
   level walk that keys only keyed and path modules. The identity-keyed `genericClosure` is the graph's,
   built only when the graph is read, and checked node by node against the merge's list first. A module
   may name others in `disabledModules`, and the collection drops every occurrence of a named module
   with its imports, as nixpkgs' `collectModules` does ([Module removal](#module-removal-disabledmodules)).
6. **the `(loc, defs)` custom-merge escape hatch** — `mkOptionType { merge = loc: defs: …; }`. A
   descriptor stating `name` and no fold takes nixpkgs' constructor default (see
   [`mergeDefaultOption`](#mergedefaultoption--the-shape-directed-law-exported-beside-mergeleaf)).
   A gen leaf states the same fold options first, `types.typedef { merge = loc: defs: …; } "tally" isInt`:
   each definition is verified before the fold and blamed on its file, `merge loc` must be a function,
   and the result is verified again, refused by name naming the type's `merge` (`ci/tests/typedef-merge.nix`).
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

### The definition record

nixpkgs' `mkDefinition { file; value; }` (exported here too) builds `{ _type = "definition"; file; value; }`, and the record **is** a definition in its own file. nixpkgs reads it right after
discharge, so it is legal under `mkIf` and `mkMerge`, and below it only one override level
(`mkForce` / `mkDefault`) is read before the order pass sorts. gen-merge reads it at the same seat:
discharge maps a definition to definitions (`dischargeIn file value`), the record is a terminal arm
carrying its own file, and every fold that pairs a file calls it, so `options.x.files` and a refusal
name the record's file rather than the enclosing module's. Two readings differ from nixpkgs:

- `definitionsWithLocations` serves `{ file; value; }`, without the record's `_type` key, which nixpkgs
  keeps.
- A record as a whole `submodule` value, or a whole submodule element of `attrsOf` / `lazyAttrsOf` /
  `listOf` / `nullOr`, serves the checked value where nixpkgs aborts uncatchably. A value the
  submodule's check rejects is refused.

### A partial fold — `mergeDefsPartial`, `partialAttrsOf` and `partialSubmodule`

`mergeDefsPartial loc type defs` runs the spine over SOME of a position's definitions, for a consumer that
folds the rest later. Its result is a definition again, so folding it with the remaining definitions is the
fold over all of them: `filterOverrides` is a fold of the (priority, values) monoid, and a partial result
stays in it only while it keeps its priority.

| winners               | result                                                              |
| --------------------- | ------------------------------------------------------------------- |
| at a non-default `p`  | `{ _type = "override"; priority = p; content = <merged>; }`         |
| at the default (100)  | the merged value, as `mergeDefs` gives it                           |
| none (all discharged) | the identity, `{ _type = "if"; condition = false; content = { }; }` |

`partialAttrsOf element` is `lazyAttrsOf element` whose every key folds through `mergeDefsPartial` (and
its threaded twin on the evaluation's path), so a nested priority survives at every depth. Both sit at the
top level beside `mergeDefs`, not in `types`, whose members the vocabulary censuses enumerate. Its consumer
is gen-aspects' guard carrier, whose typed half folds at load and meets its fired content later.
Tests: `ci/tests/partial-fold.nix`.

`partialSubmodule mods` is `submodule mods` whose every DECLARED option folds partially: in gen's own
evaluation an option's value is its winners as the table above gives them, and a default-only option is its
declared default at `mkOptionDefault` (`{ _type = "override"; priority = 1500; content = <default>; }`), as
nixpkgs' fold holds it. Its child is evaluated on a partial knot in `childTree`, with or without a seed. It
is its own type: the constructor tag enters the mint, so `typeEq` separates it from `submodule mods`, and a
redeclaration mixing the two refuses by name. Its consumer is gen-aspects' guard carrier's typed child, whose
declared `includes` then keeps its priority to the fired content. Tests: `ci/tests/partial-submodule.nix`.

Its bounds, each pinned there:

- **An option with neither a definition nor a declared default moves nothing.** Its value is the identity, so
  a later fold that supplies no definition serves no key, where `submodule` and nixpkgs serve the type's empty
  value (`[ ]` for a list). Every option that has a definition or a declared default folds as the whole fold.
- **Mounted in nixpkgs `evalModules`, it serves the full fold at the mounted option's own type only.** A
  `partialSubmodule` nested below it, at depth 1 or more (inside a `submodule`, or inside another
  `partialSubmodule`), is a child of the mounted evaluation and stays partial, so the nixpkgs consumer reads
  its definitions (`{ _type = "override"; … }`). Partial is meaningful where a gen fold consumes the value.
- **A nested tree keeps its priorities only when it is itself declared `partialSubmodule`.** A `submodule`
  declared inside a `partialSubmodule` folds fully, so its own options' priorities are spent: a later
  `mkDefault` beside it loses to its declared default, carried as data at the default priority.

### A whole value judged — `verifyValue`

`verifyValue type value` answers whether `value` is a `type` as gen's fold would serve it, in gen-types'
`verify` shape: `null` where the fold of the one definition `value` at `type`, read to the type's depth,
serves it, and otherwise a string naming the failing position, relative to the value, and why. A composite's
`check` cannot be that answer: it is nixpkgs' shallow per-definition predicate (`(attrsOf int).check { b = "x"; }`
is `true`), and it stays equal to nixpkgs'.

```
verifyValue (attrsOf (listOf (submodule { options.port = mkOption { type = int; }; })))
  { a = [ { port = 1; } { port = "x"; } ]; }
# => "`a.\"[definition 1-entry 2]\".port': expected type 'int' but value \"x\" is of type 'string'"
```

At every position the definitions pass the fold's discharge, priority and order passes, and the head step is
the fold's own choice predicate, the one `either` chooses its member by: each definition's `isValid`, then the
set's head judgement (a union's `headJudge`, a refinement's `verify` on the merged value, a foreign record's
`merge.v2` `headError`). Below it the judgement descends through a container's `split` and a nesting type's
tree, evaluated once, whose declared options and freeform definitions are judged in turn. That descent runs
parallel to the fold's; `ci/tests/verify-value.nix` holds the two to one answer, `null` exactly where the fold
serves, cell by cell.

Its bounds:

- A foreign (nixpkgs) record's refusal below its head is not a position nixpkgs publishes: its `headError` is
  shallow and its v1 `check` is per definition. The judgement reads the foreign fold to its depth there, and
  nixpkgs' own throw propagates, never `null` (`ci/tests-error.nix`, `verify-value`).
- A payload the type's depth forces throws its own error (`attrsOf raw` at `{ a = throw …; }`), as the fold
  does; one it does not force (`lazyAttrsOf raw`, `raw`) is never read.
- `deferredModule` is judged at its domain only: a deferred module is not evaluated until something imports it.

Cost, `NIX_SHOW_STATS` `nrThunks` per key of `attrsOf (listOf E)`, two elements a key, n = 100 to 200: 852
against the fold's 828 with `E` a submodule (each element's tree is a root evaluation, where the fold's is a
child of its own), and 64 against 64 with `E = int`.

### `mergeDefaultOption` — the shape-directed law (exported beside `mergeLeaf`)

`genMerge.mergeDefaultOption loc defs` is the nixpkgs `lib.mergeDefaultOption` analogue: the law
nixpkgs applies where no *per-key* type was authored. It combines by the definitions' **runtime
shape** — one def ⇒ its value · all functions ⇒ applied **pointwise**, results merged by the same law
(this is not composition; a function is what nixpkgs' `lib.isFunction` accepts, so a `setFunctionArgs`
wrapper counts) · all lists ⇒ concatenated · all attrsets ⇒ `//`-folded, **shallow,
last-wins** · all bools ⇒ OR-folded · all strings ⇒ concatenated · all ints **and all equal** ⇒ that
value · anything else ⇒ a named refusal. **Only differing ints and type-heterogeneous definition lists
refuse**; differing bools and strings combine.

★ **It does NOT replace `mergeLeaf`.** `mergeLeaf` remains the engine's
no-`.merge` default with its agree-or-refuse posture. Two routes inside this library reach the law, both
below: `mkOptionType`'s default, and an option that states no `type`, at four shapes. The second moves
the value of an untyped option defined more than once, and it is `types.unspecified`'s fold too; no
typed option's merge semantics move. It claims one law at one arm, never
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

**An option stating no `type` takes that default at four shapes, and the leaf fold elsewhere.**
nixpkgs gives such an option `types.unspecified` (`fixupOptionType`), a `mkOptionType` stating `name`
alone, so it folds by the constructor default. Here an untyped option defined more than once
(`mergeUntyped`, lib/modules.nix) takes the default above when every definition is a list, every one a
string, every one a bool, or every one an attrset and not every one a functor: `"s"`,`"s"` ⇒ `"ss"`,
`[ 1 ]`,`[ 1 ]` ⇒ `[ 1 1 ]`, disjoint attrsets ⇒ their union, with the shared-key refusal above. Every
other shape keeps `mergeLeaf`. That makes it a third fold, not the check-only descriptor's: equal
nulls, floats and paths, and `1` beside `1.0`, are **served** by an untyped option and **refused** by a
check-only descriptor. The check-only descriptor's narrowing was ruled (2026-09-25);
nixpkgs' refusal of those shapes is the refuse half of nixpkgs parity, which is not ruled, so the untyped option
keeps the leaf fold's agreement there. Functions and functors stay compared, never applied. A single
definition is its own value under both folds and stays on the leaf fold. Cells:
`ci/tests/parity-surface.nix` `test-untyped-*` and `ci/tests-error.nix` `untyped-default-merge`.

**Such an option's record states `types.unspecified`**, as nixpkgs' `fixupOptionType` gives it, so
`options.<o>.type.name` reads `unspecified` and nixpkgs' docs walker renders `unspecified value`.
`types.unspecified` folds by this same fold (one definition is its own value), so an explicit
`type = types.unspecified` and a declaration stating none are one type with one fold, as they are in
nixpkgs (`ci/tests/module-option-records.nix`).

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

`evalModuleTree { specialArgs ? {}; check ? true; prefix ? []; coreShortCircuit ? false; warmFrom ? null; editedModules ? []; class ? null } modules → { config; options; _module; type; provenance; undeclared; deprecations; _type; class; extendModules; graph }`. `config`, `options` and `_module` are read through the evaluation's one refusal, as nixpkgs' `checked` reads its three: an undeclared definition under `_module.check`, or a refusing `_module.check` or `_module.freeformType`, refuses each of them. `_module` is the module-visible record (`args`, `check`, `freeformType`, `specialArgs`). `class` is nixpkgs' nominal module class: every module reads it as its `_class` argument, and a requested class refuses a loaded module stating another (a removed module and one that loses its key to another included, as nixpkgs loads both). `extendModules` re-evaluates with modules appended (also a module argument), `graph` is nixpkgs' import tree (`disabled` marks a removed node), and `_type` is `"configuration"`. `.config` is the merged output; `.options` is the merged descriptor map (introspection,
no nixpkgs eval); `.type` carries a `.merge` so a tree nests inside a parent tree (submodule
recursion) — and it is an option type named `submodule`, which a real nixpkgs `lib.evalModules`
mounts (see below);
`.provenance` is a lazy per-loc record of WHERE each value came from (see below);
`.undeclared` lists the definitions the eval did not merge into `.config` (see below);
`.deprecations` lists the declared options whose TYPE carries a `deprecationMessage` (see below).

Every function module receives `config`, `options`, and `prefix` (the module's option path, equal to
the `loc` at the enclosing `submodule.merge` call — `[]` at the root, `["sub"]` inside an option
named `sub`) in addition to any `specialArgs` and `_module.args` entries. A `specialArgs` key among
the three is the value every module reading it receives, as in nixpkgs' `evalModules`, where the
caller's set is the right operand of the base arguments; a `_module.args` entry of that name stays
readable as `config._module.args.<name>` but does not bind the formal. Inside a module, `config._module` carries
`args`, `check`, `freeformType` and `specialArgs`, as nixpkgs' does. `specialArgs` reads through a
re-declared `type` or `apply`, while the arguments a module receives stay the caller's set. A nested
tree's modules also receive
`name`, the last step of their position: `types.submodule` and the tree-as-a-type state it as
nixpkgs' `submoduleWith` does, an overridable `_module.args.name` definition. Every evaluation also
serves nixpkgs' `internalModule` arguments, `extendModules` and `moduleType` (the evaluation's own
type, whose empty value is its on-demand `type` child), through `config._module.args` and as formals,
and `_class` as a formal. A module's own definition of one is a second definition beside the engine's:
`mkForce` wins, `mkDefault` yields, and a plain one is refused by name, where nixpkgs, printing a
plain `moduleType` beside its own, dies with a stack overflow.
A module's WHOLE `_module.args` set under a property is ranked against the engine's definitions as nixpkgs'
override pass ranks it: `mkForce { … }` serves the forced set alone, so `extendModules`, `moduleType` and the
position's `name` are then undefined and a read of one is refused by name where nixpkgs aborts, and
`mkDefault { … }` loses to them. A condition over a set at normal priority stays per key, so deciding the keys
forces no condition, and `mkIf false { … }` keeps its keys where nixpkgs drops them.
A nested tree's `moduleType` publishes the
module list nixpkgs' `submoduleWith` builds the child over: the `‹name›` placeholder, the type's own
modules located by their declaring file, the position's `{ _module.args.name = last loc; }`, then the
definitions, and its `extendModules` re-evaluates that list with the new modules appended
(`ci/tests/published-module-set.nix`). So its empty value is named by the position, however many type
hops down it is read, and the type placed at a second position is refused there as two definitions of `name`, as in nixpkgs
(`ci/tests/request-surface.nix`). **That is the whole of the injected argument set, and it is the argument-side compat
boundary:** nixpkgs injects `lib` at every
`evalModules` level, the `lib` its module system is instantiated with. gen-merge injects the `lib` it is
built with (`lib/default.nix`'s `lib` parameter) at every level, and none if built with none, as the flake's
`lib` output is. On that engine a module reading `lib` is refused by name
(`` module argument `lib' is not defined ``) until the caller threads it through `specialArgs` (or, outside
option declarations, `_module.args`). `_class` and `_prefix` are injected as nixpkgs injects them.

### A type that refuses a caller's base module argument — `refusingSubmodule`

`refusingSubmodule stated keys mods` is `submodule mods` that STATES base module arguments it refuses from a
caller: a type of gen's own, with no nixpkgs twin, whose evaluation supplies those arguments itself (a
gen-schema instance reads its own `config` to bind its kind argument and identity). Its `withArgs`
refuses a stated key by name when the caller's set carries it, and gen's submodule union refuses a
stated key that either declaration's arguments carry, in either order; the merged type refuses what
either side stated. Presence decides, never the value. Any other key is served, as on a plain
`submodule`. The stated set is the record's `refusedArgs` attribute beside `specialArgs`, sorted and
unique, never in `functor.payload`, so the payload stays nixpkgs' `submoduleWith`'s; every rebuild
(`recarry`, `substructure.rebuild`, the union, the exported `typeMerge` and `substSubModules`, a
`deriveType`) carries it, and it enters the type's mint, so two types differing only in it mint apart. A
redeclaration through nixpkgs' own `submoduleWith` is nixpkgs' record and carries no set: gen's relation
refuses there a stated key that partner's `specialArgs` supply, and the record that join returns keeps
the stated keys through every later join it decides and every rebuild of it, answering a later partner
that supplies one with no merge (a join a later nixpkgs record decides never asks it). `keys` must be
a list of strings drawn from the engine's `baseArgNames` (`lib/modules.nix`: `_class`, `_prefix`,
`config`, `lib`, `name`, `options`, `prefix`, `specialArgs`, held to the arguments a module receives by
`test-baseArgNames-is-every-key-the-engine-supplies`); any other key is refused at
construction, since no evaluation of the type supplies it. A type serving as a nixpkgs twin never
states a key: there nixpkgs serves the caller's value.

The first operand, `stated`, is `null` for a type minted over its module list, or the CONSTRUCTION
the module set is built from, for a library that builds `mods` itself from arguments:
`{ ctor; members; args = tags: { … }; sealed; }`, with `ctor` qualified in the stating library's
namespace (an unqualified one, or one in `gen-merge.`, is refused, since the mint keeps the spelling as
stated), `members` the minted inputs (entering by their marks), `args` the inert ones, and `sealed` the
caller content. It is minted in place of the module list's seal, so two constructions over equal
arguments are one type and two over different arguments are two. The statement must cover every input
`mods` depends on, or two different module sets mint one type. `withArgs` keeps it; a rebuild keeps it
and seals the module set it is rebuilt over beside it; a union of two declarations and a `recarry` seal
the module list again. Any other first operand is refused by name, so a call that hands the key list
first is refused where it is written.

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

**Served on a refused evaluation.** `.provenance` is served where `config` refuses: it records what the
engine read and from where, which is a different question from whether it checks.

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
winning def's value to WHNF (the order marker test), so reading `winners` fires a declared
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

**Served on a refused evaluation.** `.deprecations` is served where `config` refuses: it records what the
engine read and from where, which is a different question from whether it checks.

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
# ⇒ [ { path = [ "inner" ]; type = "depA"; message = "…"; declarations = [ "<unknown-file>" ]; } ]
```

`ty.getSubOptions` reaches the same declarations as a tree if that shape suits better. Note what the
re-derived records say about provenance: `declarations` reads `[ "<unknown-file>" ]`, because sub-modules
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
root and an edited root, since it has no single origin. Warm is also REFUSED (cold fallback,
`reason = "disabledModules names a module to remove (warm refused)"`) when the evaluation's
`disabledModules` name any module, in the base or the edit: a removal moves which base nodes exist,
which the footprint cannot see. An edited entry stating an empty or non-matching list keeps its own
refusal (`"disabledModules on an edited module (warm refused)"`) for the same reason. Warm is also REFUSED (cold
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
`disabledModules` refusals above, the regime key above, which keeps a prior of a different effective strictness
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

**The decision trace.** Every result carries `.warmDecision` (always-on data, plus the one function field
`next`; `mode = "cold"` on a plain compose):

```nix
{
  mode     = "warm" | "cold";                     # ADMISSION: cold = the fallback fired (reason stated)
  inert    = <bool>;                              # warm admitted, but no non-edited module is clean ⇒ reuses nothing
  reason   = <string|null>;                       # why cold (no warmFrom / check differs from warmFrom's / disabledModules names a module / disabledModules on an edited module / an edited module reaches a base node)
  strict   = <bool>;                              # the effective strictness this result was evaluated under; the next warm admission reads it
  reused   = [ <loc-string> … ];                  # the spliced declared leaves (dot-joined)
  remerged = { <loc-string> = <reason>; };        # "edited-def" | "dirty-def <file>" | "dirty-decl <file>" | "freeform-dirty <file>"
  modules  = { clean = [ file… ]; dirty = [ … ]; edited = [ … ]; };   # the classification
  uncheckedConfig = <attrs>;                      # read through this evaluation's refusal (Result surface, below)
  next     = <function: options → modules → evaluation>;  # the warm continuation (Result surface, below)
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
pin it. The three internal memo fields `freeformConfig` / `freeformProv` / `warmDecision.next` on the
result let a CHAINED warm (warmFrom = a warm result) reuse the freeform layer directly.

**Result surface.** The public result is `config` / `options` / `_module` / `provenance` / `undeclared` /
`deprecations` (+ `type`);
`warmDecision` (the decision trace), `freeformConfig` / `freeformProv` (the freeform memo layers) and
`warmDecision.next` (the warm continuation a `warmFrom` evaluation runs through) are internal fields —
additive, threaded between chained evals, not part of the byte-identity contract. `optionDefs`,
`freeformConfig` and `warmDecision.uncheckedConfig` carry definition values, so they are read through
the evaluation's refusal, as `config` is: its identity verdict, then its unmatched-definition check.
`warmDecision.next o modules` is `evalModuleTree (o // { warmFrom = r; }) modules` over this result
`r`, under the same door and its refusals, holding `r`'s record unread through `r`'s refusal: a warm
evaluation runs through it, so a prior's refusal is never the next evaluation's.

## The `types` namespace

`genMerge.types` = gen-types leaf **checkers** ⊎ gen-merge structural **strategies** — the `lib.types`
drop-in the re-host points at (`lib.types.X` → `genMerge.types.X`):

- from gen-merge (merge-bearing): `submodule`, `listOf`, `attrsOf`, `lazyAttrsOf`, `deferredModule`,
  `either`, `raw`, `anything`, `unspecified`, `optionType`, plus `mkOption` / `mkOptionType` /
  `deriveType`. `unspecified` and `optionType` are published here only, not at the top level.

**`unspecified`** admits anything and folds as an option stating no `type` folds (see
[`mergeDefaultOption`](#mergedefaultoption--the-shape-directed-law-exported-beside-mergeleaf)).
**`optionType`**'s values are types, gen's own records or foreign ones. One definition is its own
value; several merge through the declaration type-merge, the later module deciding against each
earlier one, as nixpkgs' `types.optionType.merge` hands them to its own, and the merged type is rebuilt
over each definition's module set located at its file, so a sub-option's `declarations` name the file
that defined it, as nixpkgs' `fixupOptionType` locates them; a pair that does not merge is
refused by name with the type-merge text (where nixpkgs says `already declared`), and a definition
that is not a type is refused as outside the type. `_module.freeformType` is `nullOr optionType`, and
its definitions fold through the same binding (`mergeTypeDefs`, lib/modules.nix).

- from gen-types (verify-only leaves): `str`, `int`, `bool`, `enum`, `path`, `union`, `refined`, …
  (the merge-bearing gen-merge versions of `listOf`/`attrsOf` win in the union).

The union carries gen-types' identity helpers too. Every one of them is a function (`stampOk`,
`rewritesCheck`, `witnessedCheck`, …) except **`typeWitness`**, gen-types' witness declaration, a
record of field names: it is the one value member of `types` that is not a type, and a fold through
it as a declared option type is refused by name.

**`anything`'s fold.** Lists concatenate (reverse definition order). Attrsets recurse per key, and a
conflict names the full path (`` `o.svc.k' ``). A key's definitions take the engine's priority spine
before the recursion, as nixpkgs' `(attrsOf anything).merge` does: a property marker at a nested key
(`mkIf`, `mkMerge`, `mkForce`, `mkOrder`) is discharged there, and a key whose every definition
discharges to nothing is dropped. The key set is therefore strict, as nixpkgs' is: it forces each
definition at the node to WHNF. Anything else takes `mergeLeaf`, the engine's
agree-or-refuse leaf fold, which is also `raw`'s. **An attrset carrying `__mint` is carried whole**
when every definition carries it: it takes `mergeLeaf` too, so one definition passes through as it is,
several pass if all are `==` to the first, and a conflict is refused at the option itself
(`` `o' ``). `__mint` is the mark a substrate constructor writes (a gen-types checker or refined type,
a gen-merge composite or derivation, a gen-schema kind, a gen-algebra intensional value). A rebuild would keep a digest but move every
closure into a fresh Value cell, so a value whose identity is DECIDED by `==` over its record would
stop equalling itself on upstream Nix and Determinate. Carried whole, a transported construction is
the same value on all three evaluators. Definitions mixing marked and plain attrsets are rebuilt.

The carry fold's stated costs, all of them `mergeLeaf`'s:

- **Twins are refused.** Two independent constructions of one identity (one digest, distinct
  closures) are `==`-unequal, so defining both at one `anything` slot refuses the whole value, where
  the rebuild returned one whose digest read cleanly. One value defined twice still folds to it. This
  reaches gen-merge's own composites: two constructions of `listOf int` defined in one `anything`
  slot are refused by name.
- **Two definitions of one sealed value split as `raw` does.** A sealed gen-types type carries
  throwing fields, so `==` reaches a throw on upstream Nix and Determinate and short-circuits on Lix;
  `anything` and `raw` give the same answer on every evaluator.
- **A cyclic value overflows.** A hand-written `__mint` on a freshly built cyclic value, defined
  twice, sends `==` round the cycle and overflows the stack uncatchably: the cyclic-value exception
  in [Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate), extended to whole
  attrsets.
- **Unmarked values are still rebuilt.** A value carrying no `__mint` takes the per-key rebuild, so
  its compared parts do not survive transport: a record with no mark (a nixpkgs composite, a custom
  `mkOptionType`) carried through `anything` can give `typeEq` `false` on upstream Nix and
  Determinate, and so does `==` on `{ f = g; }`. gen-merge's own composites carry `__mint` and are
  carried whole, so `listOf int` is itself after transport on all three evaluators.

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

| gen-native            | what it is                                                            | the foreign field(s) it derives                                    |
| --------------------- | --------------------------------------------------------------------- | ------------------------------------------------------------------ |
| `name`                | the type's name                                                       | `name`, `description`, `descriptionClass`                          |
| `verify` / `admits`   | value predicate (`v -> null \| err`) / domain predicate (`v -> bool`) | `check`                                                            |
| `mergeDefs`           | definition fold, `loc -> defs -> value`                               | `merge`                                                            |
| `whenEmpty`           | what it is worth when nobody defined it                               | `emptyValue`                                                       |
| `carries` / `recarry` | what it wraps, by ROLE, and how to rebuild over another               | `nestedTypes`, `getSubModules`                                     |
| `unroledNested`       | an imported record's `nestedTypes` keys that name no role, verbatim   | `nestedTypes`                                                      |
| `substructure`        | `{ declares; modules; rebuild; freeformType; }`                       | `getSubOptions`, `getSubModules`, `substSubModules`, `description` |
| `typeMergeRel`        | the **row-free** type-merge relation (one carve-out, see below)       | `typeMerge`, `functor`                                             |
| `deprecated`          | the deprecation message, if any                                       | `deprecationMessage`                                               |

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
A descriptor handed to the published `types.defineType` that states the foreign `check` beside gen's
words has that `check` read where every foreign word is read, in the import half, and conjoined with
what it states in gen's words, so the crossing drops no predicate it was handed.
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
  mint = { minted = …; };         # default: minted per component
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
reads it) are added, and `defineType` completes it. A witnessed rewrite of the base's `check` (a `check` copy, `addCheck`) is the base's stated
check and crosses with its behaviour, so the derivation refuses what the base refuses. Its relation
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
which Nix `==` cannot compare totally (key a derivation by plain data); a base carrying a parameter
under its author's own relation (a foreign container or module set), naming `defineType`, which
serves it (argued under costs and residues).

**Identity.** A derivation never inherits its base's mint. With no `mint` it is minted per
component through gen-types' identity half: the `id` and the `key` inert, the base by its mark (or
sealed, where it carries none or a wrapper rewrote its `check`), so `deriveType (listOf t) { … }` is
one type wherever it is built over one `t` (unless the base is a witnessed `check` rewrite, whose
derivations are compared by value, so two separate constructions are not `typeEq`), and gen-types' `idOf` refuses by name only where the
base hands up a sealed component. A caller that passes a `mint` keeps that meaning and owes a preimage covering
the `id`, the `key` and the base's identity; one that omits the `key` mints two different
derivations as one.

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
- **A base carrying a parameter under its author's own relation is refused by name, and the refusal
  names `defineType`, which serves it.** A foreign container or module set the import keeps as itself
  (`lib.types.listOf lib.types.int`, `lib.types.submodule …`) states its author's relation and no
  `recarry`, so the import hands up no rebuild for it. A derivation is its base's join and rebuild derived again, so it needs both from this
  library: a join that keeps every check either declaration states (a redeclared option accepts a
  definition only if every declared check does), and a rebuild over another payload. The author's
  relation is the foreign protocol's later-operand join, which keeps one operand's check. Threaded
  carriage does not supply the missing join. It serves the base itself through `defineType`, and this
  library's evaluation meets two such declarations at the option, reading each one's check there. A
  derivation needs the meet as a TYPE, because its relation answers a type. One built over the carried
  base, joining through `mergeTypes`, served a value one copy's `verify` rejects when declared twice,
  where the raw base refuses it. So the refusal stands until a join of two foreign records carries every
  check and `verify` either states, and serving it then moves no refused cell to silent. It is an open defect, not a stated limit. A foreign leaf derives,
  and so does a stock container over a gen nesting element, which the import re-homes as gen's own. A
  `verify` a copy of such a container states rides on that re-home, as the copy's `check` does, so the
  derivation evaluates the definition before judging it (`derive-type-container-verify-copy`).
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
`{ inherit (lib.types) str nullOr; }` publishes `str` and `listOf` and refuses at `nullOr`. A declared
name refuses by name as well when the vocabulary's value there is live: the link keeps no record of
what it shadows, so it admits a shadow only over a tombstone, a value that refuses when reached,
and the shipped gen-types keeps one at each allowlisted name. nixpkgs'
entire `lib.types`, which carries no protocol, is refused whole at construction. The allowlist is gen-merge's own declaration, so an entry is stale
only when it names nothing gen-merge exports; an entry naming a name the vocabulary lacks is
inapplicable, and whether the shipped gen-types still collides at each entry is a CI cell. The
allowlist's own hygiene (a stale, groundless or byte-copied entry) is a CI cell too and not a load
check, since the allowlist and the strategies it is judged against are both gen-merge's constants:
`linkset.test-the-shipped-allowlist-is-hygienic`.

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
vocabulary answers the same question. gen-merge's `submodule` reads `.options` off a standalone
evaluation of the modules its fold reads, with no defs supplied, as nixpkgs' `extendModules { prefix }`
does, so the introspection and merge halves cannot disagree about what a submodule declares, nothing
an instance authored is forced, and the records it returns can evaluate their own nested trees. Like nixpkgs'
`getSubOptions`, that evaluation lists nixpkgs' own `noCheckForDocsModule` (`config._module.check = mkForce false`)
after the type's modules, so a module reading `_module.check` there reads `false` and the evaluation's `moduleType`
lists the module last (`ci/tests/docs-evaluation.nix`). A **leaf** type
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
  re-ties the stamp to the record it completes, and wherever it ties one it declares it: the record
  carries the vocabulary's witness declaration (`__witness = types.typeWitness`, where the vocabulary
  publishes one), which gen-algebra's `conservativeEq`, gen-types' `typeEq`, reads at decision time.
  gen-merge's own composites tie and declare the same way. A record failing the stamp on entry is
  imported and served, but unminted, and `typeEq` refuses it by name. The published `mkOptionType`
  first returns a gen-merge completion's copy departing at its `verify` or `check` as it is, as
  `types.defineType` does (below): it keeps its mark and stale stamp, so `idOf` and `typeEq` refuse
  it by name as they refuse the raw copy. A gen nesting record (`submodule`, `partialSubmodule`)
  whose check is rewritten (`addCheck`, `// { check }`) needs no `verify`: it crosses as itself too,
  its threaded fold intact, so it is served below a gen union as the raw record is. The price: a description-only
  `//` (`t // { description = …; }`) is a copy too, and `typeEq` refuses it; as an option type it
  is still served. **Re-completion keeps the witnesses a record arrives with**: the
  published `types.defineType` and `mkOptionType` never re-tie the check witness over a `check` they
  did not derive, and `types.defineType` keeps the stale stamp of a copy whose distinguishing content
  changed, so a re-completed `addCheck T p` is enforced alone and beside `T` and its identity is
  refused by name, as the raw copy's is. The FOLD keeps one too: a container's fold holds the record
  it was completed with (`mergeDefs.completed`), so does a submodule's (tied once, by the door that
  completes its constructor's record) and a library constant's (`attrs`, `deferredModule`,
  `optionType`, `anything`, `unspecified`: the constant itself, completed once), and no door re-ties
  a fold it did not complete, so a
  `//` copy that takes another container's fold (`split`, `mergeDefs`, `merge`) keeps its own `check`
  over a fold whose witness is not its own, and that check is owed: a definition it rejects is refused
  by name, naming the copy's type. A copy departing only at fields a door does not read (a
  `description` or a caller field at `defineType`; the import door also reads the protocol fields it
  translates) keeps its completion's identity there. Neither door's copy test (the import door's
  `copy`, `types.defineType`'s `stale`) asks a field that is an output of the record's own evaluation
  (`interface.ownEvaluation`: `descriptionClass`, `nestedTypes`, `unroledNested`, on a record whose
  module set decides its `nestedTypes`), because forcing one evaluates the module set, and inside a
  registry knot that is an uncatchable infinite recursion on Nix and Determinate. The price: a copy
  departing only there is the same type to `typeEq` at both doors, its forged value carried, its
  `idOf` still refused (the record is sealed). **`types.defineType` returns a copy departing
  within its carrier as it is**, and so does the published `mkOptionType`: a `//` copy of a gen-merge
  completion that states `verify`, departs from its completion at `check` or `verify`, and elsewhere
  only at fields the door does not compare (`interface.doorUnread`: `typeMerge`, a name-carried or
  identity field, a module set's own outputs) keeps its row,
  functor, relation, fold, mint and stale stamp, and the door re-derives only the two foreign fields its
  departure invalidates: `check`, its declared domain, and `typeMerge`, its completion's foreign relation
  met with the copy (`interface.carriedCopy`). For a copy departing at `verify` alone that domain is a
  one-definition projection of the `verify`, published as the copy's own check witness: a foreign engine
  asks it of each definition, and gen's readers see the pair unrewritten and judge the `verify` on the
  merged value, through either door as raw. A copy that also states an ad-hoc `check` publishes it as a
  witnessed rewrite, judged per definition. Only a gen-merge
  completion is carried (it states `typeMergeRel` and `_checkWitness`): a raw gen-types record holds no
  row, functor, relation or fold to keep, and its `check` is not a predicate, so it is imported, and a
  verify copy of one leaves the door unminted and refused by name. A copy departing only at name-carried
  fields is imported too, and the import boundary re-ties it, so it keeps its completion's identity. The
  door decides the carriage without forcing a field whose value reads the members (the name, the
  description, the identity cells, a module set's own outputs), so a self-referential checked container
  (`let s = mkOptionType (gt.checkedListOf s)`) has a value, and so does the same through
  `types.defineType`. A container copy
  stating `verify` (`listOf`, `struct`) is carried the same way. So a verify copy of `enum "e" [a b]`
  keeps the `enum` row, and beside a widening `enum` it serves the union's member as the raw copy does.
  In gen's engine the door's verdict is the raw copy's over every leaf, wrapper, partner and order the
  door matrix enumerates (19,140 cells), except a copy of a caller-check `mkOptionType`, which states no
  `verify` and is re-completed. Outside that population, a copy changing `merge`, or only `typeMerge`,
  is still re-completed and loses its row. Inside a nixpkgs container the raw copy's `verify` is read
  too (see "A `//` copy's `verify` is read inside a foreign container", and "… inside a nixpkgs
  submodule" for its open defects there), except under
  `nullOr`, `either` and `uniq` over a copy whose `verify` admits what its base's `check` rejects,
  where the door serves and the raw copy is refused by the container's own `check`, its base's.
  Gen's engine drops at no door. Under nixpkgs' `evalModules`, nixpkgs merges two declarations by
  asking the later one's `typeMerge` and handing it only the earlier one's functor.
  A door copy's functor therefore names the copy as the declaration (`functor.__declared`) beside
  its completion's `type`, which stays the completion, and where the later relation is gen's (an
  exported `typeMerge`, derived or retained) it meets the join with that declaration, closing a
  module-set declaration's `verify` on the merged value as the door closes its own join. Where the
  later relation is nixpkgs' own, a copy declared FIRST is dropped where the raw copy is: that is
  nixpkgs' later-operand rule, which it applies to its own `addCheck` copies too. So is a copy that
  leaves the door stale-stamped rather than carried (an `addCheck` over a gen container copied with
  `// { verify }`): it states no declaration. Some copies of a gen `either` declared first are dropped
  too. **A record gen did not complete comes back closed under
  its own rebuilds**: every completion states a type-merge relation, so a foreign-protocol record
  stating none (a nixpkgs `int`, `addCheck np.int p`, an `np.submodule M`, an `addCheck` or
  `// { verify }` copy of either) is not completed, and the engine imports it where it is declared,
  enforcing its own `check`. Its `typeMerge`, and a module set's `substSubModules`, answer with its
  checks carried, so it keeps them where nixpkgs rebuilds it (a redeclaration, a stock submodule's
  fixup, a freeform plane), and an ad-hoc `// { check }` override is carried as a check there. A
  constant constructor's own record (`np.int`) has nothing to carry and crosses as itself. Its
  `verify` is read on the merged value and stated where a fold asks membership: in a v2 merge's
  `headError`, after its base's, as nixpkgs' `addCheck` states its check, so `np.either` / `np.oneOf`
  moves on to a member that admits the definitions; a non-v2 record is lifted into the v2 protocol,
  its own check read on every definition and naming the ones it rejects, as nixpkgs'
  `checkDefsForError` does. A gen record a caller checked since its completion (nixpkgs' `addCheck`
  over a completion or over a door's return, or a `// { check }` copy) is closed over that check by
  the door that completes it again, before the completion, so a later declaration's join and a module
  set's fixup keep it; a copy departing only elsewhere (a `// { description }`) is completed as it is.
  A `//` copy of a completed gen record (a container, `submodule`, `deferredModule`, `attrs`,
  `optionType`, `anything`, `unspecified` or `raw`) that rewrites its `admits` states a domain its
  fold never closed over, so it is the check rewrite it states: the door closes it over its check and
  its new `admits` together, as `addCheck` conjoins them, and a value the new `admits` drops is
  refused by name in gen's evaluation and in nixpkgs', while a value it keeps is served as the plain
  record serves it. `anything` and `unspecified` fold totally and state no `admits`, so a copy stating
  one departs from its completion. `raw` has no fold of its own (the engine's leaf fold folds it, and
  closes over no domain), so a foldless record stating `admits` and no `verify` is read the same way;
  on a foldless import (`mkOptionType gt.raw`, whose `admits` is its `check`'s view) the conjunction
  is idempotent. A copy removing `admits` states no domain and is completed as it is.
  A `// { verify }` copy the caller checked is closed the same way, whether the door completes it again
  or returns it as itself, and a checked record nixpkgs' join carries at a root states its check on
  the `merge.v2` `headError` nixpkgs reads, so `types.defineType` over a checked gen `nullOr` of a
  keyed nixpkgs submodule keeps its check declared twice. One such record can still drop a check under
  nixpkgs' evaluation: a `// { verify }` copy the caller checked, declared once, keeps the caller's
  check and can drop the copy's own `verify`. **The limit:** a raw outer `K // { verify }` mounted in nixpkgs'
  `lib.evalModules` without a door is nixpkgs' drop, not gen's: nixpkgs never reads the field, and no
  gen code receives the overlay. The one place that leaves a gen record inside nixpkgs weaker than
  nixpkgs' own twin is `np.either` declared once, where the `addCheck` twin refuses rejected values
  that the raw copy serves; declare it through a door (`types.defineType`), or use `addCheck`.
- **A completed parametric leaf merges only the SAME type, or two `enum`s.** Sameness is
  decided first, by gen-types' `typeEq`: its identity is minted over its construction, so two
  textually-identical constructions merge, and a type with a SEALED component (a `typedef`'s predicate,
  a refinement's `check`) merges where `typeEq` says one type — one binding declared twice, or two
  constructions of one registered term (gen-algebra `mkIntensional`). A digest match never merges on its
  own where either side seals a component: two separately written lambdas share a mark and are refused.
  Where `typeEq` answers `false` or refuses, the relation reads both constructions through gen-types' certifying `payloadOf` (the
  construction payload, read-only and never identity), and one law applies: two `enum`s under any two names
  merge to the enum of their ordered union under the left operand's name, nixpkgs' own `enum` functor `binOp`
  (`unique (a ++ b)`, left operand first), as nixpkgs' `enum`, which has no name, unions any two. A gen
  `enum` is completed under nixpkgs' `enum` row at its own members, so a nixpkgs `enum` partner is joined
  in its own relation, and that join is taken only where it keeps every member. Every other differing pair
  refuses by name, saying whether no law exists for the two
  constructions (`struct`) or a payload could not be read (a sealed or foreign
  partner) — gen-merge's own refusal on the declaration path, nixpkgs' `already declared` under a
  foreign mount — instead of a wrong type. A leaf with no mint at all (an `enum` over a path, a
  self-referential type) keeps refusing: its parameters live behind its own predicate. A **nullary** leaf has no
  parameters to compare: a gen × gen pair keeps its self-merge, and a gen leaf facing a raw foreign nullary
  leaf answers the partner's record (see "A foreign payload is read only where it is read WHOLE").
- **A composite is identified per component; its redeclaration keeps its own relation**.
  `listOf`, `attrsOf`, `lazyAttrsOf`, `nullOr`, `either` (so `oneOf`), `submodule` and a `deriveType`
  derivation carry the identity fields built by gen-types' exported identity half (`mkIdentity`): a
  mark over the constructor, spelled `gen-merge.<name>`, and one tag per component (the element, the
  alternatives in order; a submodule's module set sealed and its `withArgs` arguments inert), with the
  sealed components in `__sealed` beside it. So `listOf int` built twice is one type, and is itself
  after transport through `anything`; gen-types' own `checkedListOf int` and `checkedOption int` are other types,
  because they fold differently. The mint is lazy: a declaration never compared mints nothing, and a
  kind's mark demands its option types' mints. Identity and a redeclaration's value are two
  questions: one submodule binding declared twice is one type (`typeEq` `true`), and its
  redeclaration is still decided by the type's own relation, so its module set is evaluated twice, as
  nixpkgs `lib.evalModules` does (a doubled list option reads `[ 1 1 ]` in both; with a `default` on
  the doubled option nixpkgs refuses `already declared` and
  gen-merge keeps its right-biased non-type fields, the shadowed declaration still reachable (below)).
  Two module sets still union and two `listOf` over joinable elements still join. Two
  submodules over different module sets share a mark and differ at the sealed module set, so `typeEq`
  of the pair refuses by name. A `//` copy of a composite fails the completion stamp, as a leaf's
  does.

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
(`v -> bool`, its own domain), and the boundary derives `check` from what it finds: their conjunction
where a record states both, and otherwise whichever it states. A leaf's own `check` is CURRIED and must
never be applied as `v -> bool`, which is why `verify` is read in place of it; that reason never bore on
an `admits` stated beside the `verify`, so a record's per-definition domain is every predicate it
states. A type stating neither gets `_: true`, the nixpkgs `anything` posture.

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
the fold runs. The engine's `mergeDefs` reads `admits` only where the fold carries no witness of a
guard of it (below), and a fold is called from more places than that, so a definition reaching
a gen structural type's merge without passing a union used to reach `imap0` or `//` and abort with
a raw builtin error (`expected a set but found a list`), or, for `deferredModule`, be accepted and
fail wherever it was imported. `listOf`, `attrsOf`, `lazyAttrsOf`, `attrs`, `deferredModule` and
`submodule` now wrap their folds in one binding, `refusingOutside` (`lib/types.nix`), passing the
same binding they state as `admits`, so their domain check cannot disagree with the `check` they
export. It tests the surviving definitions, where nixpkgs' `checkedAndMerged` tests `defsFinal`, and
refuses `` gen-merge: option `<loc>' has definitions `<type>' cannot consume (<files>) ``
(`ci/tests-error.nix` `structural-domain`). The tree type states no `admits` and keeps the module
reader's refusal.

**A record's `admits` is refused outside wherever the fold the engine runs carries no witness of a
guard of it.** A record stating `admits` and no `verify` (a caller's, through any door or none, or a
`//` copy taking a fold of its own) is refused with the text above, before its fold's value is read,
unless the fold it runs carries such a witness. Two folds do:

- a fold completed under the record's own `_checkWitness` (`mergeDefs.completed`, the record the fold
  was completed with) whose completion holds the record's own `admits` and fold record, which a
  container's and a submodule's fold carry, tied where the door completes them, a library
  constant's carries, stating the constant, and an import's checked fold carries, tied by the door
  that completes the import (the import leaves the slot open, and the door fills only an open slot);
- the fold of a record whose `check` a wrapper rewrote, which the import checks per definition.

A `//` copy that swaps the fold takes a fold without the witness, so its `admits` is read
(`ci/tests-error.nix` `caller-admits`). Because `mergeDefs.completed` is the record its fold was
completed with, a door's return and its fold's completion hold one `admits` slot, so the doors'
admits-rewrite test above is false on every return and fires only where a `//` copy restated
`admits`: `types.defineType` and `mkOptionType` refuse that copy, and the engine reads `admits`
wherever the fold carries no witness. Both slots are compared because a constant's fold is a record:
a `//` copy that restates `admits`, or rewrites only the fold's function
(`t.attrs // { mergeDefs = t.attrs.mergeDefs // { __functor = …; }; }`), keeps `completed` while
its fold no longer closes over what it states, so its `admits` is read. The witness costs a call
through the fold record (one value per fold of a constant), and on `attrs`, `deferredModule` and
`optionType` the slot comparison costs more per option than the second `admits` read it replaces.
One copy is still served against its `admits`:
a container's `//` copy that keeps its fold and restates `admits` without passing either door (raw,
or through `types.mkType`), which is served as its fold serves. A copy that borrows another import's
checked fold (`mkOptionType { check = …; } // { inherit (other) mergeDefs; }`) carries that import's
completion, or none once the fold is rebuilt without it, so its `admits` is read.

A nesting record's fold is its own only while it is the fold the record was completed with. A `//`
copy of a `submodule`, or of an evaluation's own `type`, that rewrites `mergeDefs.threaded` or
replaces the fold whole is refused by the record's own `check` per definition, at the top and as a
container's element (`` gen-merge: a definition for option `x' is not of type `submodule', in `a.nix' ``),
and a door does not tie such a copy's fold to it (`ci/tests-error.nix` `caller-admits`). Inside the
record's domain the copy's own fold still runs.

**A foreign type's `check` is applied to every definition before its fold**, as nixpkgs'
`mergeDefinitions` does (`checkedAndMerged`). A type whose domain is stated in the foreign protocol —
`lib.types.str`, a `check` given to `mkOptionType`, a leaf vocabulary injected as `types`, or a gen
structural type sent out and brought back through `mkOptionType` — has its `check` tested at the
boundary (`importedFold`), wrapping whichever fold the type brought, so `lib.types.str` refuses `1` at
every position gen-merge folds and the refusal names the option, the type and the failing files
(`ci/tests/foreign-leaf-check.nix`). As in nixpkgs, only the definitions that survive `mkIf` and
priority are checked. A gen record carrying no check witness that states a `check` beside its own
`mergeDefs` (a caller's record, raw or through `types.mkType`) is a foreign descriptor too: its
`check` is tested before that fold, the threaded one of a nesting container included, and never
swaps it for a `merge` the record also states; a union asks it when choosing a member, so
`either <it> int` serves what the check rejects by `int`, as nixpkgs' `either` does
(`ci/tests-error.nix` `foreign-check-beside-fold`).

**A nixpkgs v2 type is merged by its own `merge.v2`**, as `mergeDefinitions` merges it: its
`headError` decides, not the record's `check`, and an answer that is not exactly
`{ headError, value, valueMeta }` aborts as it does there. An ad-hoc `type // { check = …; }` on a v2
type is **refused by name**, as nixpkgs refuses it; state the check with `addCheck`. That holds over
a gen `either`, and over a stock `either` or `oneOf` holding a gen nesting element that is re-homed as
gen's own union: an `either` of a submodule states no module set. Declared twice or more, the
override is met as the redeclaration meet meets any two types, so its check is enforced on the met
type. Imported through a door, the override is judged at each join nixpkgs asks the door for: a join
that is the override again (its functor rebuilds it) is refused by name, declared once beside another
type or declared twice, and a join that is a coherent type is served, the override's check owed on the
values its own merge admits. On a **submodule-bearing** v2 type (`submodule`, `attrsOf submodule`, …) nixpkgs does not refuse the override
but erases it without a word when it rebuilds the type at declaration (`substSubModules`); gen-merge
enforces it as the check it is, as it enforces an `addCheck` there: a value it admits is served, and a
value it rejects is refused by name, a deliberate departure from a silent answer. An ad-hoc `check` on a
non-v2 submodule-bearing type (`deferredModule`, `attrTag`, `functionTo`, `uniq`) cannot be told from
the one its constructor shipped, and is applied.

**An exported gen type that publishes a head judgement answers nixpkgs' `merge.v2` too**, as
nixpkgs' own `either`, `nullOr` and `addCheck` do: `merge` is `{ __functor; v2; }`, the functor
calling the fold directly, and `check` carries `isV2MergeCoherent = true`, without which nixpkgs'
`checkV2MergeCoherence` refuses the mount. Today that is `either` (so `oneOf`) and `nullOr`, and a
derivation or refinement of either. Every other export publishes the bare fold, as nixpkgs' leaves
do: its `headError` would be the pointwise check alone, which nixpkgs' v1 reading already computes,
and a v2 `merge` would make nixpkgs refuse the ad-hoc `type // { check = …; }` it accepts on a v1
type; so `gen.int // { check = …; }` mounts under `lib.evalModules` as nixpkgs'
`int // { check = …; }` does.
The `headError` is the published `check` over each definition (nixpkgs' `Definition values:` form,
naming files), then the type's head judgement. So a nixpkgs union holding a gen type takes its next
member where gen's own fold would refuse the definitions whole: `lib.types.either (either int str) x`
over `1` and `"s"` gives `x`'s value under `lib.evalModules`, as the all-nixpkgs composition does
(`ci/tests/nixpkgs-protocol.nix`). Under v2 nixpkgs applies only the `headError`, so
its pointwise half is what keeps a gen leaf checked there.

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
`oneOf` is left-nested `either`, as nixpkgs folds it, and inherits the rule. A member accepts when
every definition passes its check and its **head judgement** takes them whole, as nixpkgs' `either`
takes a member whose merge reports no head error. The judgement is published beside the fold, as
`mergeDefs.headJudge` (`null` when the type takes the definitions whole, else why not): an
`either`'s is its own choice, a `nullOr`'s is its split (null beside a value is refused, a set with
no null is its element's to judge), and a derivation or a refinement of either carries it with the
fold. A foreign member is judged by its own `merge.v2` `headError`; every other member judges no
further than its check. A refusal walks every member whose judgement refused and
names each leaf member with the files it rejected, the later members included.

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
carve-out, against a partner that states a relation of its own, raw or returned by the `mkOptionType`
door: see "A foreign payload is
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
`later.typeMerge earlier.functor`), and an EARLIER relation is asked first whether it refuses the
later type, a refusal that ends the step unless it is the decider's answer alone ("Redeclaring an
option"). The foreign arm stays and is not legacy:
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
                                                           # a gen leaf facing a raw foreign nullary leaf,
                                                           # or a nixpkgs leaf through a door, answers
                                                           # the partner's
# one-element containers — listOf, nullOr                   (gen role: `element`)
{ payload = { elemType; }; type = p: rebuild p.elemType; }
# embedded in a richer foreign constructor (`interface.embeddings`): published under ITS name
{ name = "attrsWith"; payload = { elemType; lazy = false; placeholder = "name"; }; }  # attrsOf
{ name = "attrsWith"; payload = { elemType; lazy = true; placeholder = "name"; }; }   # lazyAttrsOf
{ name = "deferredModuleWith"; payload = { staticModules = [ ]; }; }                  # deferredModule
{ name = "str"; payload = null; }                                                     # str (gen-types `string`)
{ name = "path"; payload = { absolute = true; inStore = null; }; }                    # path
{ name = "path"; payload = { absolute = null; inStore = null; }; }                    # pathLike
{ name = "either"; payload = { elemType = [ int float ]; }; }                         # number (gen-merge's own leaves)
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
refused).
A foreign answer that aborts is taken as no answer (`tryEval`), so the relation stays total. The
partner's own `typeMerge` is never called. Price (Δ thunks per option, Nix 2.34.8): a gen × gen
`listOf` pays +1 on nixpkgs' engine and 0 on gen's, a gen × gen `either` +2 and 0, and a mixed `either`
about +300 against gen's engine's former (wrong-record) answer. A partner stated under the RICHER constructor a gen type embeds in
(nixpkgs `attrsWith` for `attrsOf`/`lazyAttrsOf`, `deferredModuleWith` for `deferredModule`) is joined
in the same binding over the embedding (`interface.embeddings`): gen's parameters are a point of that
payload, so the pair is decided by the partner's `binOp` under the same witness, a foreign
`staticModules` survives it, and a refused `attrsOf` pair names its element pair. A container or
`deferredModule` returned by the `mkOptionType` door (either door) states its relation beside gen's role. Where gen
cannot read that relation whole and the door return's own relation answers the pair with no ad-hoc override at any
depth, it is joined at these element and embedding pairs in that relation; otherwise it stays gen's partner, and its
own closure decides the pair where it is the deciding declaration. A union's member pair
does not read it so, and refuses that door return where nixpkgs serves. Three LEAVES embed
too: gen-merge publishes gen-types' `string` as nixpkgs' `str` (no payload; the witness reads the two
names as one record's, the table's `joinsAs`), and `path`/`pathLike` as `pathWith` at `absolute = true`
and at no constraint. A mixed `str`/`path`/`pathLike` redeclaration therefore has nixpkgs' record in both orders
under either engine, and a partner keyed under the embedding whose relation declines the join is
REFUSED, never answered by gen's own record: gen `path` beside `pathInStore`, `externalPath` or a
constrained `pathWith` is refused as nixpkgs' twin refuses it, so the partner's check is never dropped
unsaid. Each row claims gen's check is the partner's at the embedded parameters. Their `name` is
unchanged (`string`, `path`, `pathLike`). Price (hub perf bench, Nix 2.34.8): a per-process constant of
+6 thunks on each load row (+4 on `aspects`) from the three rows' exported functors, no marginal moved,
and a gen × gen `str` redeclaration pays less than before (`sameLocFanIn` thunks p/r 1.508 → 1.480),
because a gen partner is answered before the embedding is read. A fourth leaf row's parameters are
TYPES: gen-types' `number` is published as nixpkgs' `either` over gen-merge's own `int` and `float`
(the row's `members`, stated at the completion as the completed leaves the `types` export publishes),
and a partner keyed `either` is joined in its union relation, rebuilt from its functor
(`interface.joinInRebuiltPartner`), so a mixed `number` redeclaration, bare, under a container or
inside `either number str`, has nixpkgs' record in both orders under either engine, and a nixpkgs
`addCheck` beside it keeps its check in gen's engine. The export's functor accepts a payload whose
members ARE gen's `int` and `float` by their minted identity under the completion stamp
(`interface.membersAgree`): a second instance of this library agrees, nixpkgs' members, a raw `//`
copy of gen `int` and the members swapped do not. A supplied vocabulary lacking `int` or `float`, or
minting none for it, forms no row, and its `number` publishes under its own name. Price (Δ thunks/calls
per redeclared option, Nix/Lix/Determinate alike): mixed on nixpkgs' engine 667/543 against the
nixpkgs twin's 227/159, of which the meet's share (+285) is the correctness floor; mixed on
gen's engine 783/724 against the twin's 1173/1151; a gen × gen `number` unchanged. A gen nesting type (`submodule`, the tree) facing a
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
called from the leaf relation for every partner that is not gen's own, a gen record with no retained
relation, so a gen × gen pair builds nothing). A gen leaf facing a RAW foreign leaf, or a nixpkgs leaf
through a door, of the same key (equal `functor.name`, both payloads null, a `type` the
functor names) answers the protocol's default over that functor, which is the record the partner's twin
answers in the order where it decides: a mixed `int`/`bool`/`float`/`raw`/`anything` redeclaration, bare
or under `listOf`/`nullOr`, has nixpkgs' declared type in both orders and under both engines. It refuses
nothing it did not refuse: the join is taken only where it keeps each operand's stated name, and a
partner whose functor states no `type` is answered by gen's own relation as before. The leaf relation
never calls the partner's own `typeMerge`. **A same-keyed partner whose functor states a payload has the
twin's answer in each order** (`interface.statesPayload`): where gen decides it is refused, as nixpkgs'
default relation, which the twin states, asserts two leaves agree on a payload; where the partner is
declared later, its own relation decides, as nixpkgs lets it, because that refusal states `vetoes = false` (below). Gen's own record would serve the pair with the partner's check dropped. Measured over
the twin leaves bare and under `listOf`/`nullOr`/`attrsOf`, both engines; a partner stating no
`payload` key at all, and a union (`either`/`oneOf`) over the leaf, are outside it. Two stated scopes. **A pair nixpkgs refuses at
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
`config.q` and `options.q.type.name` of an unrelated `q` read their answers. Which declarations are admitted does not
depend on how many modules declare an option: a `type` read from a `_module.args` argument is
admitted whether one module declares the option or several. **The cyclic case aborts uncatchably,
a declared exception to the rule that every refusal is catchable**: where that argument's own value
reads the option it types (`_module.args.ty = if config.p == … then str else int` beside
`options.p.type = ty`), the read dies with `infinite recursion encountered` at any declaration
count, as nixpkgs does. Refusing it by name would mean refusing every stratum-2 read in a declared
`type`, including the common `(pkgs.formats.json { }).type`, which the guard admits.

**A declaration that reads an earlier-resolved declaration is served: nixpkgs' renamed-option
family.** `mkRenamedOptionModule`, `mkRenamedOptionModuleWith`, `mkAliasOptionModule` and their
`doRename` declare the alias leaf with its target's `type`, so the leaf reads `options` and the
guard's poisoned fold cannot resolve it. The guard then runs **staged passes**: each unresolved node
is re-tried with `options` bound to the previous pass's declarations, stamped as `declarationsOf`
stamps them, so a pass reads only what strictly earlier passes settled and a chain of renames
resolves one link per pass, in any module order. The previous pass's declarations carry the module
arguments their own modules define (`_module.args`), so an alias whose target's `type` reads an
argument (nixpkgs' `systemd.nix` under `with utils;`) resolves once a pass reads them; the pass that
tries a node binds no argument, so an option of its own whose declaration or presence reads one still
refuses by the argument's name. The unresolved nodes are tried once, at pass 300, and a pass is
built only when a later pass reads it: a node costs the passes its reads reach, so a read that needs
a pass resolving nothing visible (an argument becoming readable, an element of one argument read
from the one before it) is served however many such hops it takes below 300. No count of the
tree's leaves or arguments bounds those hops, and a cycle reads down every pass, so the depth is a
constant under the evaluator's call depth: a cycle refuses by name rather than overflowing the
stack, and a node whose hops outrun the passes refuses by the read the last pass could not make.
What no pass resolves refuses at the end, the
spine-first unresolved node: a rename cycle and an option whose **presence** reads `options` refuse
with the `options` poison's text, and a node whose read resolved reports its own error. The passes
decide admission only; every value still comes from the value side. Two prices are stated, both
uncatchable: a declaration reading a field its target does not carry (`options.a.example`) dies as
nixpkgs dies, where the poison once refused it by name; and a module that **catches** a stamped-view
refusal (`tryEval options.a.isDefined`) can pass as a leaf and take a group's shape on the value
side, where it reaches Nix's recursion abort. The second is the guard's standing price for a module
that catches its refusal, a cycle with nothing to detect it, reached now at any pass rather than
only at the first. Each pass
re-folds the whole module set, so a set holding renames pays about one extra declaration fold per
pass its reads reach, and a cycle pays all 300.

**An earlier relation's refusal ends the step unless the decider's answer alone.** Each fold step
first asks the earlier operand's `typeMergeRel`, if it has one, about the type every later declaration
jointly became; a refusal there is the answer. So `[gt.int, Fint, str]` refuses as nixpkgs does. The
exception is a refusal stated as the decider's answer alone (`vetoes = false`), which nixpkgs, asking
only the later declaration, would give where that relation decides:

- the leaf relation's refusal of a same-keyed partner stating a payload, and a container's over such
  an element pair;
- the leaf relation's refusal of a partner of another key that is **foreign**: a raw record, or one
  stating its author's relation through `mkOptionType` (it carries `retainedRelation`);
- a relation an author stated through `mkOptionType` refusing a foreign partner.

There the later relation decides and its join is met with every declaration's check, and the refusal
names the pair only where that relation gives no join; a partner relation's own `throw` is then
reported in gen's words. So a nixpkgs `int` alias whose `typeMerge` answers `int`, declared after gen's
`int`, serves what both declarations admit, and `[gt.str, Fint]` with `Fint = int // { typeMerge = _: str; }`
merges to nixpkgs' `str` met with `Fint`'s check, refusing `"a"` and `1`. Against a **gen-native** later type (one stating `typeMergeRel`
and no `retainedRelation`) those two relations' refusals still end the step. That is a hold, not a
law: the leaf relation, deciding, keys a partner stating a relation by its type name where nixpkgs keys
by functor name, and would serve where nixpkgs refuses. Every other gen relation's refusal of a later
type also ends the step. Where nixpkgs serves such a pair these refusals are open defects, listed
under [Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate). A foreign relation keeps the
authority nixpkgs gives it, also over a join that drops a name an operand states, authored or
inherited, which is met at the step (below): `[gt.int, str, Fx]` with `Fx = str // { typeMerge = _: int; }`
answers `int`, as nixpkgs does, and rejects what `str` rejects.

**Against nixpkgs, on the type.** Over every declaration list of length 3 and 4 in a seven-family
census (8,338 words), gen-merge agreed with nixpkgs on every all-foreign list whose joins keep their
operands' names, on both the declaration and the freeform planes. It departs where an earlier
relation's refusal ends a fold step, and then by refusing ("A redeclared option's type refuses where an
earlier relation's refusal ends the step", under Known byte-mode boundaries).
Gen `attrs` against foreign `attrs` merges in both orders, directly or under a gen container, to gen's
fold met with the partner's check. Where a merge drops a check (a foreign join that renames an
operand, or the check a wrapper added to a gen record) the join is met, so the value differs only where
a dropped check rejects it, and a pair that is one shared value keeps that value. They are listed under
[Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate). A refined type redeclared against
its bare base meets it in both orders, directly or under a gen container: a record that declares the
record it `wraps` answers beside a bare record of that record's key (`interface.wrapsKeyOf`), at gen's
relation dispatch, its veto and the exported `typeMerge` a foreign engine asks, so the merged type is
the refinement and serves what both declarations accept.

**A foreign join that drops an operand's check is met.** nixpkgs' `addCheck` is
`elemType // { check = …; }`, so it keeps its base's `functor` and `typeMerge`: `port ∥ int`,
`u8 ∥ u16` and two `ints.between` calls all join to bare `int` there, and `[port, int]` accepts
70000\. gen-merge takes a foreign join (`later.typeMerge earlier.functor`, or an imported record's
stated relation) as is where it keeps each operand's stated name at every depth the operand wraps a
type. A raw foreign join that renames past an operand is taken as the step's carrier and met with every
operand (`interface.importedMerge`), so `[port, int]` merges to `int` and rejects 70000. A record
imported through `mkOptionType` merges on `foreignRel`, which answers its stated relation's renaming
join as the carrier (`meets`), and the step meets that join the same way, at every role it carries and
at the top: a stated relation supplies the join, never a certificate that the join keeps each
operand's check. A join that is not a type the step can apply (one lacking the `check` or the `merge`
an operand states) is refused on both paths, with a reason saying so. A declaration's admission is its
`check` AND what its `merge` admits (nixpkgs' containers judge their elements in `merge`, and a fold may
refuse what its check accepts), so where a join is taken past the witness the step holds each
declaration's own fold: it runs beside the join's over the same definitions, its value is demanded
position by position as the served value is, and a v2 fold's `headError` refuses. An operand whose
relation gen-merge did not construct (an author's `typeMergeRel`, carrying no `exact` witness) is held the
same way where it carries no element or alternatives role, even when its join keeps every name, because
such a join certifies no fold: an author type named `int` whose `merge` refuses an odd value, declared
beside `int`, refuses 3 and serves 4 in both orders. Where the join is a type stating no gen
relation (no `typeMergeRel`), a gen container declared beside it as itself (not returned through a door)
is held by its own fold, so its element judgement is enforced though the join's merge never reads it. The fold held is the operand's own unchecked fold
(what it merges by without a definition check), never a refusal of how a declaration is spelled. A record met holding
stays held when it is merged again, in gen's engine and through its exported `typeMerge`. A pair that
holds pays each operand's fold: measured, about 19 thunks per redeclared option for `[port, int]`. A role the join gains is not a drop,
so a freeform submodule unioned with an option-only one, or two `attrTag`s, merge as on nixpkgs. A
join that is a gen record is compared with each operand as the import environment reads it, so a
type whose relation rebuilds it through `mkOptionType` (gen-schema's `refined`, gen-aspects'
`aspectsRoot`) merges when redeclared as itself. A
pair that is one shared value keeps it: `[port, port]` from one `types.port` answers `port`, and
rejects 70000. A redeclaration is the meet (owner-ruled 2026-10-06, below); every join taken here is
met at the step, which serves nothing an operand rejects. The cost is one fuel-bounded walk per foreign fold step,
and a second join only on the refusal path; gen-native pairs never reach it. Measured with
`NIX_SHOW_STATS`, one option declared in 200 modules: `listOf str` +2.7% thunks and +1.0% function
calls, a distinct `submodule` each +0.1%, `port` +0.07% and +0.18%. The measured members are under
[Known byte-mode boundaries](#known-byte-mode-boundaries-deliberate).

**A redeclared option accepts a definition only if every declared check does** (the
meet). An `addCheck` keeps its base's name and relation, so no name
separates `addCheck int p` from `int`, and the relation answers the bare base:
`[int, addCheck int (x: x > 0)]` serves -1 on nixpkgs, in either order. Every type merge here answers
the relation's join restricted by each operand's check the join does not carry (`interface.metWith`,
at `mergeTypes` and at `declaredPair`'s veto arm), so that pair merges to `int` and rejects -1, with
the wrapper first or second, under a gen parametric (`union [ int ]`), under a container
(`listOf (addCheck int p)` beside `listOf int`), in a longer list, and in gen's engine for a foreign
operand too (`addCheck lib.types.int p` beside `lib.types.int`, and a nixpkgs partner of any check).
The join still decides the record (its fold, name and functor, nixpkgs' later operand); the meet
decides acceptance, a lower bound by induction over the fold. **Every fold step is met, a held step
included**: an answer stating that it holds is met with both operands again, because an operand's
exported `typeMerge` answers a record met with that operand alone, and a stated relation supplies the
join, never a certificate. **An operand is exact, and owes
nothing, only where gen-merge constructed its relation**: every relation this library builds carries a
construction witness (`typeMergeRel.exact`), and an operand stating neither `check` nor `admits` owes
none. A `typeMergeRel` an author states is author vocabulary and no witness, so an author type whose
relation answers a join keeping every name still owes its own check. **The witness certifies an
operand only where the answer carries it**: where the answer is the operand's own construction (one
check witness, compared by `==`; a `//` copy keeping it, as a description copy does, is the same
construction), or where the answer states parameters, a join built over the operands'. A leaf answer
carries its own construction's check alone, so an author record reusing gen's relation over its own
check (`lib.mkOptionType { name = "int"; check = c; … } // { inherit (types.int) typeMergeRel; }`), a gen
record holding another construction's relation, and two `defineType`s of one name each owe their own
check beside `int` or each other, in either order and under a container: `[int, B]` refuses a value `B`'s
check rejects, where nixpkgs serves it. The parameter test does not ask whose parameters the answer
states, so an answer stating a payload that is not a join over this operand's parameters still certifies
it: beside `number` or `pathLike`, whose own answer states one, and under a container relation
transplanted onto another container, which answers a join over the relation's parameters rather than its
holder's, such an operand's check is still dropped, an open defect. **`wraps` is the meet's
declared-base surface**: a record naming the record whose constructor and parameters its own are; its
own check stays owed. The meet reads an operand's parameters (`shapeOf`) and the stock it is owed
relative to (`relativised`) off the innermost declared base, so gen-schema's `refined B rs`, whose
functor is its own (`refined<B>`), widens and is relativised as `B` is and still owes its refinements. A
met record whose operands owe no merged-value `verify` names its gen join's `verify` reason on refusal where
the join's check is still that `verify`'s witness; any other record's `verify` is read only past its check. A gen x gen step whose answer carries both
operands owes nothing and is
answered before the meet is built, except to a `//` copy whose `verify` no completion vouches for
(`interface.replacesVerify`: it replaced its completion's `verify`, or states one with no completion
stamp). Its `check`, witness and relation are still its base's, so no relation carries that `verify`, and
the step owes the copy its `check` per definition, any it rewrote included, and its `verify` once, on the
merged value, as a foreign operand's is owed: a definition alone is not the value it refines.
That `verify` is stated where a fold asks membership, a v2 merge's `headError`, so a union
choosing its member by it moves on to the next one; a non-v2 join is lifted into that protocol. The
carrier (`interface.joinRenames`) reads such a copy, and one departing only at its name, its description
or its `typeMerge` (`interface.carrierTolerated`), as its completion, so beside nixpkgs' `enum` its
verdict is the same in both orders; a raw copy overriding `typeMerge` is therefore read
as its completion too, which moves it from refused to served only. A
fresh join that widens a constructor's own parameters keeps that
constructor's law over them (two `enum`s union their values), and each operand stays owed for the
values its own parameters admit, so a wrapper over an `enum` is kept. Where an operand's functor
states no coherent type at its own parameters (a v2 ad-hoc override it rebuilds), those parameters are
the ones its v2 merge was built at, read from that merge's `headError`. Where a foreign operand states no
v2 merge and its functor rebuilds the operand itself, whose check is then the one owed, its parameters are
judged by gen's own constructor for its functor name, since nixpkgs names a constructor by its functor
name, over the element or alternatives it states: beside a widening `listOf`, `["a" "a"]` is refused for a
`listOf (enum ["a"])` whose check rejects it, and `["a" "b"]` is served. A foreign operand of a name gen
does not recognise as one of its containers keeps its own check, an open defect. A container's element is one of
its parameters, read as the meet reads its roles (an element type, or a pair of alternatives), so
`nullOr`, `uniq`/`unique`, `either` and `oneOf` over an `enum`, and their nests, union as the bare
`enum` does, a gen `enum` under them included; a foreign union of three members is not a pair the meet
reaches, and its operand stays owed whole. The step sits in `mergeTypes`, so
the declaration and freeform planes, every container's element relation and the published
`genMerge.mergeTypes` all answer it. **One wrapped value declared twice keeps its operand**:
`w = addCheck int p` declared as `[w, w]`, or as two `listOf w`, merges to `w` and rejects what `p`
rejects. One value is decided **without the type's phrase** (`description`, `descriptionClass`), which is
display data and, for a nesting type, an output of its own module set, so comparing it would evaluate that
module set (inside a registry knot, an uncatchable infinite recursion): `w` beside `w // { description = …; }`
is one value, keeps `p` in either order, and publishes the phrase nixpkgs publishes, the join's, in either
order (`ci/tests/phrase-free-sameness.nix`). **At a module set the step carries a dropped wrapper's check**: the module-set fold does not enforce a met record's check, so the step answers the join
restricted by the dropped check (`carriedAtDepth`), a witnessed rewrite the fold enforces as it does
one declared alone, on the declaration and freeform planes alike; `gt.submodule M // { check }` and
`addCheck (gt.submodule M) p` beside `gt.submodule M` serve what the override admits and refuse what
it rejects, by name. A foreign wrapper over a module set states no witness and is not enforced (Known
byte-mode boundaries, "Not covered"). In nixpkgs' engine gen is asked only when declared later, and
then with a functor, so a check that functor does not rebuild is not seen there (nixpkgs' own drop);
a join the nixpkgs twin refuses is not served there. The cost,
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

### An option declared beneath a `submodule`

`options.thing` typed `submodule { … }` in one module and `options.thing.sub` in another (the
`nix.settings` shape) is nixpkgs' `optionTreeToOption`: the option-group is one more declaration of
`thing`, whose module set gains `{ options.sub = …; }` beside the leaf's, in authored order. The
admission is nixpkgs' own predicate, every leaf at the loc has a type named `submodule`, and it holds
under gen's `submodule`, nixpkgs' `submodule`/`submoduleWith` and the tree-as-a-type, in either module
order and at any depth (`decl-merge.test-an-option-declared-beneath-a-submodule-joins-its-module-set`).
The group's declaration is the last leaf's type rebuilt over the group: the leaf's constructor,
partiality, shorthand and class, with no `specialArgs`, which is nixpkgs' converted declaration
(`specialArgs = { }`, `class = null`, `shorthand = null`, neutral in every field the relation joins).
So a `submoduleWith` stating `specialArgs` takes the group without a duplicate-`specialArgs` refusal.

Any other leaf admits no nested option and is refused by name, the refusal naming the option and the
type: `str`, `attrsOf submodule` (whose nested meaning nixpkgs calls ambiguous), `nullOr submodule`,
`deferredModule` (`ci/tests-error.nix` `test-leaf-group-collision-refusal-names-the-option`, a `str`
leaf). The group redeclaring an option the submodule already declares is the redeclaration rule
above: with a `default` on both, gen's submodule serves the later default where nixpkgs refuses
`already declared`, the ordered fold's divergence, reached through this spelling as through two leaves.

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
| `description`, `nestedTypes`, `getSubOptions`       | the freeform datum crosses, each through nixpkgs' refusal: the base's (`unroledNested.freeformType`, its empty value forced first) gives `nestedTypes.freeformType`, the documentation evaluation's (`substructure.freeformType`) nixpkgs' "open submodule of …" and `_freeformOptions`                                                                      |
| `getSubOptions`, `getSubModules`, `substSubModules` | the tree's declarations under the foreign prefix, its module set, and its rebuild over another                                                                                                                                                                                                                                                               |
| `check`, `merge`, `emptyValue`                      | the module-value domain, the fold through the bridge (one root evaluation of the tree), and the tree over no definitions                                                                                                                                                                                                                                     |

**`submodule` and the tree name their modules as nixpkgs' `submoduleWith` does.** Each child with definitions gets
`_module.args.name` = the last step of its position (the attribute name under `attrsOf`, the
`[definition n-entry m]` step under `listOf`, the option's own name bare or under a union), resolved as
one definition at normal priority beside its modules' own. The child over no definitions, `emptyValue`
and `getSubOptions` read the placeholder `mkOptionDefault "‹name›"`. So a module's `mkForce` or
`mkDefault` on `_module.args.name` resolves by priority as nixpkgs resolves it, a plain definition
refuses as defined multiple times, naming its files in the order the `_module.args` record lists them,
and a caller's `specialArgs.name` (`withArgs` on `submodule`) outranks it. `withArgs` therefore admits `name`, as it
admits `config`, `options` and `prefix`: a caller's value for each is the one the modules read. A module reading `name` while its
declarations are folded (`imports`, an option key) refuses by name as it would for any module argument,
unless a caller supplied it. A module whose `_module.args` key set reads `name`
(`_module.args = if name == … then { … } else { }`) dies with infinite recursion, as in nixpkgs: whether
a module states `name` is decided by that key set, so it cannot wait on `name`.

**A nesting type may evaluate its child at the position its seed was declared at (`nests.locOf`).** A
nesting type that states `nests.declAt = true` is handed, on each seed, its declaration address (`declAt`):
the declaring module's anchor, the option path and the structural path the discharge took, which no
reorder of keyed or path modules moves. Such a type may also state `nests.locOf = loc: d: …`. It is
opt-in, and read only together with `declAt` and only for a child over ONE seed: `loc` is the merge
position and `d` that seed's `{ file; value; declAt; }`, and the list it returns is the child tree's
`prefix`. So the child's option locs, the positions its messages name and its default `name` render
the declared position rather than the merge one (under `listOf`, `[definition n-entry m]` moves with
module order). A child over several seeds (one key defined by two modules) keeps the merge position.
`prefix` is a rendering only: the knot's node identity reads the child's `id`, never its `prefix`, so no
node moves (`ci/tests/declaration-address.nix`, `test-locOf-names-a-single-seed-tree-and-not-a-multi-seed-one`).

**A once-declared nesting type's own modules are read before its definitions, as nixpkgs reads them.**
nixpkgs hands each module of a type it locates (`getSubModules` non-null, so never through `either` or
`oneOf`) through `setDefaultModuleLocation`, one breadth-first level below the definitions, and an
option reads its definitions last-collected first. A `listOf` defined by a submodule's own module and by
two definitions therefore merges `[ "q" "def" "def2" ]`, at every forwarding container and depth, and for
every order-reading merge (lists, `lines`, `commas`, `functionTo`, `attrs` last-wins, the child option's
`files`, `_module.args`' definitions). gen-merge states that level as an ORDER of the child's top level
(the root's `located` count), taken after each module's coordinate is assigned, so no module node, key or
declaration address moves. A redeclared option is already located by the declaration fold, and keeps that
(`ci/tests/gen-nesting-definition-order.nix`). A child's own `extendModules` re-evaluates over the
published module set, whose own modules are located, so it reads them before the definitions too
(`ci/tests/published-module-set.nix`).

**The published option records carry nixpkgs' declaration shape.** An evaluation's `.options` (and
`declaredOptions`) records carry `loc`, `declarations` (the declaring modules' files) and nixpkgs'
string form, `__toString = _: showOption loc`, so nixpkgs' `optionAttrSetToDocList` renders a mounted
tree's docs byte-equal to its own in `make-options-doc`'s view (`visible && !internal`). They also
carry the evaluated keys nixpkgs adds beside a declaration: `value` (the option's
own merged value), `isDefined`, `definitions`, `definitionsWithLocations`, `files`, `highestPrio`,
`declarationPositions` and `options` (`[ ]`, nixpkgs' value), each equal to nixpkgs', on `.options`, on
`getSubOptions` and on a module's own `options` argument alike (`ci/tests/option-record-keys.nix`); they
project gen's fold, which puts a declared default first among the definitions, as nixpkgs' does.
`valueMeta`, nixpkgs' v2-merge metadata, is nixpkgs' own where the type is foreign and gen folds it by
that type's own merge (a v2 merge's `valueMeta` with `_internal.type`, `{ }` for a merge stating no `v2`),
and refused by name, never absent, at every other type: a gen type, or a foreign one holding a gen type.
A met record over a foreign join (a redeclared option whose declarations' join is foreign) answers its
join's metadata where every declaration admits the definitions, and refuses by name where one rejects
them; a met record below a foreign container is refused.
Below a module set it is the metadata of the call gen's fold folds by, and each `configuration` in it is
that call's own merged value, served only where the value is and guarded as the value is (a `verify` copy
inside the submodule, an `addCheck` over it), as are `attrListOf`'s `attrListValue` and `definitions`;
`lib.modules.mapAttrsOfSubmodule` reads it as nixpkgs'. So a deep force of a published `.options` tree refuses for a tree holding any gen type
(`test-a-deep-force-of-a-declaration-tree-meets-the-unanswered-keys`). `declaredOptions`, which
publishes declarations, refuses the other eight by name and answers `options` as `[ ]`. Its records
are the evaluation's own declarations, the ones `.options` serves, so a declaration that reads
`options` (a renamed option), a module argument (`with utils;`) or `config` (its presence, or a
`default`) is served there as nixpkgs serves it, and its `type` is nixpkgs' `fixupOptionType`'s: an
untyped declaration, `_module.specialArgs` included, reads `unspecified`, and a module set is located
at its declaring file (`ci/tests/declared-options-door.nix`). A gen-typed declaration that needs its
own stratum is refused by name on both, and a throwing declaration refuses both, as nixpkgs' `.options`
does.

**The engine's own `_module` records are served too.** nixpkgs' `internalModule` declares
`_module.args`, `check`, `freeformType` and `specialArgs` in every evaluation, and gen-merge serves the
four records at every position it serves one (`.options`, a module's `options` argument,
`getSubOptions`), typed as nixpkgs types them: `lazyAttrsOf raw`, `bool`, `nullOr optionType` and, for
`specialArgs`, which states no type, `unspecified`. A record's `value` is the value
`config._module.<k>` holds, and its definitions list the last module first, as nixpkgs' do.
`declaredOptions` carries the four declarations, whose evaluated keys refuse by name. They stay out of
the tree the warm walk, lint and the docs projection read. So nixpkgs' docs walker lists the four
entries as nixpkgs does, internal below the root, each with nixpkgs' type; their descriptions are
gen's own. `args` lists the definitions nixpkgs' option lists, in nixpkgs' order: the internal
module's `{ extendModules; moduleType; }` (`lib/modules.nix`, the engine's own whatever a module defines),
and in a nested evaluation the position's `name` and the placeholder's, both `<unknown-file>`
(`ci/tests/module-args-definitions.nix`). One departure is stated: under
`evalModuleTree { check = false; }`, a door nixpkgs lacks, the `check` record reads the door's
definition (`ci/tests/module-option-records.nix`).

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
that level is read. The CALLED folds (`mergeDefs` applied, `.reported`) refuse by name. An evaluation's
own type's `whenEmpty.value` is that evaluation's on-demand `type` child (below), so no second
evaluation is made for a tree an evaluation holds. A free-standing `submodule`'s `whenEmpty.value`, which no gen evaluation holds, is the bridge's one root
evaluation, nixpkgs' `base.config`. To wrap a tree's fold, **replace `mergeDefs` whole**.
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
its own fold reads. An `attrsOf` whose element nests directly, at the evaluation's root, reads the
key walk's own records instead, since the walk has already applied the split there. `lazyAttrsOf` is
the one exception: its fold is the split's twin, held equal by a cell, because it is the
`wideFreeform` hot path.

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
in. The walk does not run below a gen container, so an element marked `true` there is bound as gen's
container binds it, at a declared option and through `mkOptionType` alike. Pinned by `ci/tests/nesting-declaration.nix` and `ci/tests-error.nix`
(`nesting-declaration.*`).

**Where the refusal fires, and re-homing.** A type is HOMED where it is bound to a position: at a
declared option (`evalModuleTree`), and when a record crosses whole through `mkOptionType`. One of
the six stock foreign containers whose element may nest is folded as gen-merge's own container, so
`nixpkgs.lib.types.attrsOf (submodule …)` threads like gen's. A stock container over no nesting
element and no owed copy keeps its own fold, unless its two statements of the element disagree (below). The six are recognised by their functor, the relation they merge by,
and rebuilt over the element their carrying spellings state, never over their payload's.

**A container gen-merge itself completed crosses `mkOptionType` as itself.** It is already in the
door's image, so where it may nest (`nullOr`, `attrsOf`, `listOf`, `either`, … over a gen
`submodule`, cyclic ones included) the door returns it re-tied by the import's identity rule, and
it serves the value nixpkgs' `lib.evalModules` serves on the same record. The door's result is
`typeEq` to the record handed in, a `description` copy keeps its completion's identity, and a copy
whose `check` was rewritten keeps that check: the value it rejects is refused by name, where
nixpkgs drops the check and serves it. An element below it that only offers a nesting type through
its functor payload is refused, with the same text, where the option is bound rather than at
construction. A record stating `carries` without the completion stamp asks the door to complete it
and keeps the import refusal. Pinned by `ci/tests/gen-container-door.nix` and `ci/tests-error.nix`
(`gen-container-door.*`).

**A door's return taken as itself states its check where nixpkgs reads it.** nixpkgs' v2 protocol
reads a type's rejection from `merge.v2`'s `headError` alone, and a `check` marked
`isV2MergeCoherent` promises that it is stated there; a `//` copy can keep such a mark beside a merge
that does not state it. So every return that publishes the caller's own `merge` states the caller's
whole `check` in its `headError`, as nixpkgs' `addCheck` does: a completed container or nesting
record re-homed as itself, a foreign record stating no relation or no check witness, or that is its
own constructor's record, a foreign record stating no module set, a carried `verify` copy's base merge, and a re-home
that returns the caller's record. For a coherent record this is the identity. Its price is that the
check runs again on each definition under a nixpkgs fold, because the door cannot tell a truthful
mark from a forged one without comparing functions. Pinned by
`ci/tests/door-as-itself-states-check.nix`.

**A `//` copy's `verify` is read inside a foreign container.** A copy whose `verify` no completion
vouches for (`interface.replacesVerify`) still publishes its base's `check`, and a nixpkgs container's
fold reads an element's `check` alone, so declared alone under one the value its `verify` rejects was
served, where gen's own fold reads that `verify` bare and under a gen container. A foreign container
holding such a copy at any depth (`interface.owedCopyBelow`, a walk bounded as `canNest`'s is and
asked only where `canNest` answered `false`) is now folded so the copy is read: one of the six is
re-homed as gen's own container; one whose functor states an element (`uniq`, `functionTo`,
`attrsWith` with another placeholder) is rebuilt by that functor over its element completed, its
declared domain published as its `check` (`interface.completedOver`); `coercedTo` keeps its fold,
with its merged value restricted by a copy that is its `finalType`, or a definition it coerces
restricted by a copy on its coercion side. A gen container whose element is such a foreign container
(`listOf`, `attrsOf`, `lazyAttrsOf`, `nullOr`, `either` and `partialAttrsOf`) homes that element
before it folds it, selected once when the container is built (`interface.owesThroughForeign`;
`partialAttrsOf` asks it per key, at the same cost per key as `attrsOf`). The
copy's domain is the one the engine reads for it bare (`interface.copyDomain`, as `carriedCopy`
publishes it): its `verify` alone while its `check` is its completion's, so a copy of a gen
completion (one carrying `_checkWitness` or `__typeSelf`) whose `verify` admits what its base's
`check` rejects is served under `listOf`, `attrsOf`, `attrsWith` and `functionTo` as it is bare,
where nixpkgs refuses it. A foreign record carrying `verify` keeps its foreign `check` over each
definition (`interface.checksDefs`), so its `verify` judges only the merged value, widens nothing,
and a value outside the base is refused by name, as nixpkgs refuses it. Inside a nixpkgs `submodule` or
`attrTag` the copy is read at the nested option (next paragraph). **The prices, stated:** `coercedTo`
whose `finalType` holds the copy under a container, and a record outside the stock vocabulary whose
`nestedTypes` hold one (a hand-rolled `mkOptionType`), are refused whole by name, values nixpkgs serves
included, naming `types.defineType`; on `coercedTo`'s coercion side a definition the copy rejects is
refused by name even where the `finalType` would take it uncoerced, and under a container there the
copy is read as the container's head, as both engines read a check copy; under `nullOr`, `either`,
`uniq` and either side of `coercedTo` the container's own `check`, its base's, still decides what a
weaker `verify` admits (refused as `finalType`, left uncoerced as `coercedType`, as nixpkgs does). The walk
costs per option, Nix thunks: +7 for `listOf int`, +19 for a three-deep stock nest, +26 for `uniq (listOf int)`, +14 for gen `listOf` over a stock one, and +836 (1.2%) over a self-referential
`valueType`, against a floor that no longer serves the copy's rejected value.

**A `//` copy's `verify` is read inside a nixpkgs submodule.** A stock nixpkgs `submodule` (also as an
`attrTag` tag, or a container's element) is evaluated by nixpkgs' own option evaluation, which reads each
option's `check` alone. Its merge is kept and its value is served with each option guarded at its own read,
where nixpkgs reads that option's check: on the option's final definitions, before `apply`, and only along
the members nixpkgs' read forces (`interface.frontierAt`: what `getSubModules` reaches, and the member an
`either` or `oneOf` merge chooses). A copy declared there, over a gen leaf or a gen container of leaves alike
(a gen container folds its own `verify`, but a `//` copy's `merge` is its base's and never reads the one it
replaced), or below a container, an `either`'s chosen member or a `coercedTo`'s final member there, is refused
by name where the value its `verify` rejects was served:
the copy itself with the spine's message (`… is not of the expected type: <verify's message>`), a copy
reached through a container or `attrTag` with nixpkgs' phrase over the completed record. A value nixpkgs
refuses there with no copy anywhere, at an option typed by an `either` or by a container over a submodule
(`nullOr (submodule …)`), is refused with gen's phrase in place of nixpkgs'
(`gen-merge: a definition for option … is not of the expected type: …`), which drops the type's
description. An option read both by a sibling inside the evaluation and from outside it is folded
twice, once by nixpkgs and once by the guard, so its `apply` runs twice; the values agree. **Open
defects**, served where nixpkgs' own `addCheck` refuses, each pinned as a value in
`check-carriage.test-a-verify-copy-inside-a-nixpkgs-submodule-is-read-where-nixpkgs-reads`: a copy read
through a sibling's cross-read inside the evaluation (`config.z = config.y`, read at `z`), since the guard
holds the evaluation's returned value and not its fixpoint; a copy below a record outside nixpkgs'
vocabulary (a hand-rolled `mkOptionType` merging over it), since walking an unknown record forces what
nixpkgs may not force; and a copy below a freeform type, since nixpkgs merges the freeform definitions
internally and its merged value cannot be merged again unchanged. A further open defect, not yet pinned: a
copy of a gen container over a gen nesting element (`listOf (submodule …)`, `attrsOf (submodule …)`) is
served at a value its `verify` rejects, where gen's root refuses it.

**An unrecognised container threads through its own rebuild** (ruled 2026-09-30, arm (T)). At a
declared option, a foreign type outside the six that declares a gen nesting element (`coercedTo`,
`uniq`, `unique`, `functionTo`, `attrListOf`, `attrsWith` with a non-default `placeholder`, a
hand-rolled `mkOptionType` whose rebuild forwards its argument, …) is rebuilt through its own
`substSubModules`, handed a marker that a gen element answers with itself. The container keeps its
own `merge` and `check` (`coercedTo` keeps its coercion), and the element under it folds as a node
of the one evaluation, so the value is nixpkgs'. Whether the rebuild threads is judged on the
ORIGINAL record against its rebuild, position by position and at any depth: every declared position
that may nest comes back as the marked element (or as a record that threads in turn), and every
other declared position is a sibling with no module set to lose: its `getSubModules` is not a list,
so the walk does not call its `substSubModules` on the marker, a call nixpkgs never makes,
or its own `substSubModules`, called on the marker, answers `null`. Either way the
sibling still receives whatever the container's own rebuild hands it. The marker's import throws the import
refusal if anything evaluates it as a module. Five things are refused by name instead:

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

The refusal of the first is an **open defect where nixpkgs serves the shape** (the parity-defect rule), not a price. nixpkgs serves a
foreign `either` or `oneOf` holding a gen submodule below its own `coercedTo` or `uniq`, and a
hand-rolled container whose rebuild drops its argument or stores or relabels the module list; gen
refuses each by name. No threading door lands (owner, 2026-10-10): the `coercedTo` rebuild is
reachable only from nixpkgs' side or through a carrier on the gen element, and neither is available.
What the refusal keeps is the one graph: the alternative is a second root evaluation, which loses
one graph, the declared identity of the tree's options, and an evaluation per tree. Pinned by
`ci/tests/nesting-threaded.nix` (`nesting-threaded-open-defects`, nixpkgs' value beside gen's
refusal) and `ci/tests-error.nix` (`nesting-threaded.*`).

A stock `unique` over the tree is decided stock and served, since its check is its element's. A
refinement on the element is carried as it is under the six. **The prices, stated:** `unique`'s
message is lost on rebuild, as nixpkgs' own rebuild loses it; the element handed into a rebuild answers `check` in
gen's words and `getSubModules` with `null`; the container's merge runs three times per option
against nixpkgs' once. A foreign closure, the container's own merge and check, runs inside gen's
evaluation over a gen-threaded element fold; no foreign engine evaluates the tree, and the channel
is entered only in gen's own evaluation.

**A chain over an `attrsWith` is keyed by its stated steps.** A level is step-free wrappers
(`unique`, `coercedTo`, `nullOr`), then one `attrsWith` of any placeholder, lazy or strict. Where
step-free wrappers and a gen element that may nest sit below a lazy step, the split keys the merge's
attribute names and reads an element only where it is read. Where another container sits below
either step (`lazyAttrsOf`, `attrsOf`, `listOf`, `nullOr`, at any depth), each key is a container
node: its own walk is that record's,
read off the merge's result at that key only, and it keys its elements in that record's regime
(exactly below a stock `attrsOf`, `listOf` or `nullOr`), as gen keys its own. Either way a sibling
whose key set, `mkIf` or alias reads the read tree is served as nixpkgs serves it. **The price,
stated as an extension of the overridden-merge price below:** the steps are trusted from the
functor names at each level, while the run still says which tree sits at which key. A tree the
`merge` folds under a key not its own (keys renamed, swapped or fanned out) is the evaluation's own
child at the position its definitions declare, or, where the levels are keyed from the result, at
the position it is read, so it serves nixpkgs' value; two entries of the result at one loc are each
keyed apart. A stock-named `attrsWith`, lazy or strict, whose `merge` holds no element's tree at a key
read (one key deeper) is refused by name at the key read, where nixpkgs serves it; this is an open
defect (the owner's parity-defect rule, 2026-10-09), not a price. One whose result is not an
attribute set keeps the eager walk. **A merge that reads its elements' values** is run twice: once
over the definitions' sites, which are records, to key the tree, and once over the evaluation's
values. Where it places an element by a value, a moved read re-runs the fold over the values at the
read path. An element that fold reached, placed at the key read or read while deciding placement,
where the run over the sites holds another element there, has its nested-tree read refused by name at
its own loc, where nixpkgs serves the value: its position is not found without forcing a sibling
nixpkgs does not force; this is an open defect (the owner's parity-defect rule, 2026-10-09), not a
price. Below a key whose list the walk keys eagerly, an element the merge reads, whose own position
the run over the sites gave another key's element, is refused by name at its own loc, naming that
position; this is an open defect (the owner's parity-defect rule, 2026-10-09), not a price. Those
causes are stated on the moved-read and moved-node paths only. A value-reading merge that reads,
with a default, a field the sites lack drops the element, makes no moved read, and its refusal names
a position the merge does not expose; one that reads that field without a default aborts
uncatchably, where nixpkgs serves. Both are open defects (the owner's parity-defect rule,
2026-10-09), not a price. **The cost**, read on the hub perf-bench: `threadedRegistry` gains 4 thunks
and about 590 bytes per threaded element, and 51 thunks of per-process load on each of
`threadedRegistry` and `wrappedRegistry`, both still below their nixpkgs reference; startup gains 100
bytes, every one of them gen-merge's own allocation (the member row rises by the same 100 bytes); no
other load row rises. A node's regime is trusted from its record's name the same way: a stock-named
`attrsOf`, `listOf` or `nullOr` whose `merge` was overridden to a lazy one is keyed exactly. **A
`listOf` step is a level where its chain is stock.** Its positions, the `[definition n-entry m]`
segments nixpkgs' merge names, are keyed from the definitions it folds, which is sound only where
stock code folds them, and no probe of a merge can tell that. So the level stands only where every
record on the chain, its wrappers above the step and every record below it down to the gen element,
is bound where its own functor's fresh build binds it; nothing compares functions. **Not reached, an
open defect:** a list on a chain holding an overridden record, an `addCheck`, or any `unique` (whose
merge a hand-built type copying its functor binds at the same position), and a list below a
`coercedTo` that coerces its definitions, keep the eager walk and abort with a sibling reading the read
tree, where nixpkgs serves: `uniq (listOf (lazyAttrsOf e))` with a key below the list `mkIf` on the
read tree, or `uniq (listOf (attrsOf e))` with a second element's key `mkIf` on it.

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
`elemType` it never folds, gives nixpkgs' value at the root and under a forwarding container. A gen
container carrying, through gen containers alone, a module set no gen constructor built
(`reachesModuleSet`: `attrsOf`, `listOf`, `nullOr` or `lazyAttrsOf` over a nixpkgs `submodule`, a
deeper or mixed chain) is mounted too, rebuilt through its own forward with every level's owed check
carried (`carriedAtDepth`), as nixpkgs' containers forward `substSubModules` to their element, so the
element's modules name the declaring file. The record's own `check` rides on the rebuild, gen's own or foreign, so the domain is the meet of the two
(`carriedCheck`, the re-home law): an `addCheck` over such a root refuses what it rejects, where
nixpkgs' rebuild erases it silently. A rebuild that is no option type (null, a bare attrset, absent,
or stating `merge` but no `check`) is refused by name (`rootRebuildRefusal`), where nixpkgs aborts, and
an ad-hoc `type // { check = ...; }` is such a `check`, riding on the rebuild as an `addCheck` does. A freeform type is no option's root
and is not mounted. The fix-up item's `_file` is the file of the declaration that carries the type, as
nixpkgs' `mergeOptionDecls` locates `opt.options`, so the nested evaluation's own `options` argument and its
refusals name it (an untyped declaration before it included; the served type takes the same declaration),
and the module set is the merged type's, not a union per declaration. Where two or more typed declarations
declare the option, the declaration fold has already located each one's set at its own file, as
`mergeOptionDecls` does once per declaration plane, so the mount rebuilds over that list and does not locate
the merged type's set a second time: a function definition's own body reads where nixpkgs reads it
(`ci/tests/gen-nesting-definition-order.nix`, the `gmnp` arm). Refused by name. The first two are open defects, where nixpkgs serves the shape; the
last two are not measured against nixpkgs:

- a record declaring a gen nesting element that nixpkgs never rebuilds (no module set at the root,
  or below a union: `uniq (either (attrsOf sub) str)`, `either int copy`, any non-six container over
  a union holding a gen element) and whose marker rebuild does not thread;
- a fan-out container whose sibling of the threaded element substitutes a module set or becomes
  `null`; the opt-out serves it;
- a gen root container over such a record (`attrsOf copy`, `listOf copy` from gen-merge's types),
  whose element is homed at an inner site, never fixed up;
- a root whose fix-up result still declares a gen nesting element (a copy whose rebuild re-wraps
  itself).

**A record built through gen-merge's own `mkOptionType` is mounted the same way**. Its
author stated its fold apart from its rebuild, as a foreign author does, so where the descriptor states a
module set and is not ad-hoc checked, `importType` marks it (`substructure.mount`, a
presence datum pending the owner's reading of whether it is a published field) and the root fix-up mounts
it, alone or under gen's `listOf`, `attrsOf`, `lazyAttrsOf` and `nullOr`, each of which forwards its
element's mount through its own `recarry`. The record's own `check` rides on the mount, built from the
record handed in. The mark is re-tested where it is read (`crossedRoot`), so a marked record passed
through the door again with a `verify`, overridden `// { check }`, or given `getSubModules = null` is
judged as it now stands, not as it first crossed: a record stating `verify` is never mounted while it
states it, and a copy that drops it is mounted as nixpkgs mounts the same copy. The walk to a crossed
element takes the type walk's fuel and answers no at exhaustion, so a cycle through containers alone is
served as before. Gen's own constructors state their fold and rebuild
together and are never marked; a door record whose fold is its rebuild's serves what it served before.

**The prices, stated.** None of what follows is a price where nixpkgs serves the shape: those are
open defects (the owner's parity-defect rule, 2026-10-09, rule 1), pinned as the refusal or value
they are, never as a verdict that it is right. A hand-rolled position the declarations do not show
whose evaluation of the old empty marker module happened to equal nixpkgs' value is refused by name,
and one whose merge STORES the handed list (`deferredModule`) is served with gen's marker item in
its value: inspecting the stored list (its length, its `_file` labels) differs from nixpkgs
silently, and evaluating it refuses by name. No predicate reaches it without reading a payload: it
is the half of arm (T)'s stated domain (a merge that does not inspect element values) that has no
predicate here. Both are open defects.

**Open defects** (PU is not built, no construction is in view). First, silent, so ranked first by rule 4: a DECLARED sibling whose `getSubModules` does
not show the module set it stores (`deferredModuleWith` stating `null`) is not asked by the walk,
and a container that rebuilds it hands it the marker, so its value reads `<gen-merge thread marker>` where nixpkgs reads `static`. Second, uncatchable: an override of a nixpkgs `either` or
`oneOf` (or any foreign record) whose `substSubModules` forwards over a gen submodule, tree or
union, below a threaded container, aborts where nixpkgs serves it, because the walk's call hands
the rebuild a `null` it dereferences (204 such shapes measured, 68 per element kind; a container's
own rebuild of a sibling is the same class). The first is pinned by
`test-a-sibling-storing-a-module-set-it-does-not-state-carries-the-marker`.

**Design note: the root mount's cost, and its measured out.** Measured against nixpkgs' own
evaluation of the same workload on stock submodule roots, on nix, Determinate and Lix, the full
mount costs +4.8% thunks and +2.5–3.7% bytes. The measured alternative skips the rebuild for a
recognised intact record: it is 10% cheaper than nixpkgs there, and on `attrsOf submodule` it saves
nothing. It is not taken, because it serves a wrong value silently over a class no witness can
detect: any record whose `substSubModules`, `getSubModules` or functor payload differs from its
rebuild, including an override assembled from stock parts with attrset algebra
(`ySub // intersectAttrs { substSubModules = null; } donor` reads as intact). Adopting it is a new
ruling, and that ruling must state the whole class as an exception to the rule that every read
yields a value or a named refusal.

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
A stock container stating a module set whose `//` override of `merge` nixpkgs' own mount keeps (its
`substSubModules` rebuild forwards the override) is folded by that `merge`: it threads. An override
nixpkgs' mount erases is erased here too. An `addCheck` or a copied `check` over the override changes
nothing. **Open defects:** an override spelled in `merge.v2`, one on a release whose constructor
states no `v2` (every container on nixpkgs 25.05, `nullOr` on nixos-25.11 and 26.05), and one on an
`either`/`oneOf` (which cannot thread) cannot be told from the stock record and are re-homed silently,
losing the override.
**The price, stated:** a foreign type
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
its own. Its knot is a node of the kind `module-tree`, which declares a non-terminal attribute
(Vogt, Swierstra & Kuiper 1989 §3), `nested`: each nested tree the value holds is a child of that
node, minted at its POSITION (the option's path and the position below it), and a child's own nested
trees are its children. It declares a second, `type`, ON DEMAND (gen-scope's `ntaOnDemand`): every tree
holds one `type` child with an empty seed, its own type's empty value (nixpkgs' `base.config`, one more
`‹name›` placeholder per level), read by `whenEmpty.value` and never enumerated. A child's `result` is its tree's evaluation, read from its host's position
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
  A container of trees below a step under an over-approximating container — `lazyAttrsOf`, or any
  other split container (gen-aspects' `aspectsRoot`, a freeform plane typed by one), bare or as a
  union member — is S1 class (a): its position is a **container node**, a child whose own
  `container` group keys the inner trees over that position's definitions only, so no sibling is
  forced to key them, and whose `result` is `{ value; _nested; }`, the inner container's fold, not a
  tree's evaluation. The inner container's fold reads the node wherever the walk minted one: the
  evaluation's accessor states what the walk minted at a position, read off the walk's own records,
  so a container built through `defineType` needs no mark of its own. It serves nixpkgs' value.
  At the walk's own root (an option's position, or a container node's) under a container that adds
  no step (`uniq`, `unique`, `coercedTo`), the position is walked as the root is, and the shape
  serves nixpkgs' value: that container's fold is its element's over the same definitions, so keying
  forces nothing a read does not.
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
- **The `type` chain has no fuel.** Each `type` child holds its own, as each nixpkgs `base` holds a
  `moduleType` whose `base` is another, so the family is unbounded and only laziness bounds a read: a
  hop to a `type` child restarts the empty-seed run at 0, and a read that never ends aborts uncatchably,
  as nixpkgs' does. No enumerating read descends it.
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

## Module removal (`disabledModules`)

A module may state `disabledModules`, a list naming other modules, and the collection removes every
occurrence of each named module, with its imports, before anything is merged: nixpkgs'
`collectModules`, in gen-merge's one collection, so every reader (`.config`, `.options`,
`declaredOptions`, `substructure.declares`, the staged declaration passes and nested trees) sees the
same modules.

- **An item names a key**, as nixpkgs' `moduleKey` resolves it: a string is absolute as is, or
  relative to `specialArgs.modulesPath`; a value `toString` converts (a path, say) is its string, and
  refused where it is a set whose `key` differs; a set with `key` is that key. Any other item is
  refused, with nixpkgs' sentence after `gen-merge: `.
- **A module's key** is its path's string (its own `key` where the file states one), a set's `key`, or
  `<importer's key>:anon-<n>` for an anonymous module (1-based, the top level's importer `""`): the
  coordinates the module graph already identifies it by, spelled over keys, so a comparison mints
  nothing. Matching is string equality, so an item whose key is not a string names nothing.
- **Every occurrence is read.** nixpkgs gathers the lists from every occurrence of the import tree,
  so a list on a module that loses its key to an earlier one, or under it, is read, and each such
  module is loaded: its syntax and class checks fire, as they do on a removed module. An occurrence of
  a file is that file; a keyed set is one per key, importer and position, so a keyed import cycle
  closes where nixpkgs overflows.
- **A list reading `config`** or a module argument that is not special refuses by name, as an
  `imports` that reads it does (nixpkgs recurses infinitely).
- **Cost.** A module list with no path and no module stating `imports`, `require`, `key` or
  `disabledModules` is its own collection, as before. Any other list is walked as before and then read
  once for a list; only a list that names modules pays for the removal. A `graph` read binds the key
  set once.

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
  does not have, in its content or on its functor record (`null` there publishes none). Where a later occurrence shares the key of the one kept, and either publishes it, the
  pair is decided rather than the later one dropped: `decide kept.subject later.subject` true is one
  module; false, a non-boolean, or only one of the two publishing it is refused by name, the same in
  both import orders wherever both occurrences publish one symmetric `decide`, as gen-schema's do;
  gen-merge applies the kept occurrence's `decide`. A throw inside `decide` propagates. Where neither
  publishes it, nixpkgs' rule holds and the later occurrence is dropped. Two occurrences of one
  spelled path are the one file and keep nixpkgs' rule; two different path files sharing an in-file
  key, or a path import sharing its key with a content module, are decided like any other pair. A module publishing `__keyEq` without a `key` is refused by name. gen-schema keys a
  kind with parents by its mark and publishes its sealed comparison on the kind value's record
  (`ci/tests/key-eq.nix`).

- **A `__functor` module may name its graph node on its record, `__moduleKey`, and its meeting,
  `__keyEq.meeting`.** The node key is read before the module is applied, and keys the module graph
  (node ids, the warm origin split, declaration anchors); the result's `key` stays the REFERENCE key,
  which every evaluator dedups by and a `disabledModules` item names. The merge path meets
  occurrences by meeting: a key `<meeting>#<refinement>` meets every key sharing `<meeting>`, so a
  record's reference key is forced only where another occurrence shares its meeting, and every pair
  sharing a reference key still meets and is decided as above. A record stating no meeting meets by
  its result's `key`, as a plain module does. **The stated meeting is trusted:** a record whose key
  it does not prefix is refused by name where it meets, but a plain module stating that key never
  meets it, and both compose where nixpkgs keeps one, because detecting the mismatch would force the
  key at every import (`ci/tests/key-meeting.nix`).

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

- **A `submodule`'s identity splits by evaluator over one function reached through two slots.** Its
  sealed component is the caller's module list (`lib/types.nix` `mkSubmodule`), compared under `==`,
  so the split of the bullet above holds there too. `typeEq (sub s.f) (sub s.f)`, with
  `sub = m: submodule { options.a = mkOption { type = m; }; }` and the function selected at each
  site, is refused on Nix and Determinate and `true` on Lix. Its partner, one bound function in two
  constructions, is `true` on all three, and Lix gives the two one verdict, so no construction here
  can move the split without moving the partner, and upstream has no observer of closure identity to
  raise it. It closes when the caller lambda migrates to a first-order term.
  `ci/tests-error.nix` `submodule-evaluator-divergence` pins the split to each evaluator's own `==`
  on a literal two-slot shape, beside its partner at `true` ×3.

- **`types.unspecified`, the type an option stating no `type` carries, departs from nixpkgs' in four
  stated places**, at the top level, at an element site (`attrsOf unspecified`) and mounted in
  `lib.evalModules` alike (`mergeUntyped`, lib/modules.nix; cells `ci/tests/parity-surface.nix`
  `test-untyped-*`, `ci/tests/module-option-records.nix` and `ci/tests-error.nix`
  `untyped-default-merge`):

  - *Equal floats, nulls and paths, and `1` beside `1.0`, are served* where nixpkgs' law refuses
    (`Cannot merge definitions`). This is the refuse half of nixpkgs parity, which no parity ruling
    reaches; it rests on the ruling of 2026-10-06 that serving beyond nixpkgs is an option wherever it
    never costs correctness, and serving an agreement costs none. A check-only `mkOptionType` refuses
    the same shapes, so the two folds differ there by design.
  - *Function and functor definitions are compared, never applied.* nixpkgs returns a merged lambda
    that aborts uncatchably, or silently unwraps a `{ value; }` result, when applied. This is the
    function carve-out of the constructor default above; one function bound once and written twice
    keeps the evaluator split stated there.
  - *A shared attrset key whose values differ is refused by name* (`heddle.a`) where it is read,
    where nixpkgs' `//` keeps one value without a word: the parity criterion's carve-out.
  - *Two derivations equal by `outPath` that differ at another attribute are decided key by key.*
    Built separately (two `makeOverridable` results), their `outPath` serves and their `override`
    refuses where it is read. nixpkgs' `//` serves the last whole; the leaf fold this option used
    before compared them by `outPath` alone and served the first whole, so this is a narrowing of
    what was served, the shared-key carve-out applied to the attrsets a derivation is. A derivation
    held in one slot by both definitions serves whole.

  An untyped attrset pair reaches the cyclic-value abort below through the constructor default's
  shared-key compare rather than through `mergeLeaf`, and so only at the read of the cyclic key. The
  price, measured with every value forced: about five thunks and nine calls per key of an attrset
  pair over the leaf fold's one `==`; five to ten thunks and three to seven calls per option for two
  scalar definitions; one thunk per option with one definition (the length test).

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
  foreign container there is `deriveType`'s named refusal, argued under its costs and residues. A cycle through a container outside
  the six is then the walk's named refusal at its fuel, with its three remedies.
  `ci/tests-process-cells.nix` pins both deaths and the way out. The exception is
  argued, not merely declared: a record whose key set does not wait on the walk is a fixed shape,
  and both fixed shapes change answers given today. Crossing every stock container as itself
  stops re-homing one that nests and refuses `deriveType` over it; crossing every one as gen's
  container drops an override on one that nests nothing and admits `deriveType` over a foreign
  container, a base `deriveType` refuses by name.

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

- **A module's `_module.check` is honoured at its own level only; nixpkgs' reaches nested trees
  too.** nixpkgs declares four `_module` options. gen-merge reads `args` and `freeformType` itself
  and declares `check` per evaluation as the `bool` option it is (default `true`), so a module's
  definition merges with priorities, a conflicting pair is refused by `bool`'s merge, and
  `evalModuleTree { check = …; }`, when passed, enters as one `mkDefault` definition, as nixpkgs'
  deprecated `check` argument does. The merged value decides whether this evaluation refuses an
  undeclared key, and a module reads it back as `config._module.check`. Modules receive this level's
  merge before its refusal, as nixpkgs hands them its unchecked fixpoint, so a `check` computed from
  `config` is no cycle. The departure: a nested tree inherits the door's strictness, never the
  module-computed one. nixpkgs' `.type` carries no strictness, while this engine refuses a lax
  child's undeclared key under a strict parent
  (`test-a-lax-nested-tree-is-still-refused-by-a-strict-parent`), and keying that on a value
  computed from `config` cycles uncatchably where the parent's check reads the child's value. So
  under a module's `false` a lax child's key is still refused by its owner, and under a module's
  `true` with a caller `false` it is reported on `.undeclared`, where nixpkgs drops both. A
  `submodule` value's own `_module.check = false` drops its undeclared key silently, as nixpkgs
  does, where a named refusal is owed. That is the non-leaf branch: a `submodule`-typed
  `options._module` leaf plus a module's `_module.check` is refused by name
  (`` The option `_module.check' does not exist ``) where nixpkgs serves. Warm re-evaluation is served
  and equals cold: a reused leaf and the prior's identity walk read the prior's unchecked config
  through its warm continuation (`warmDecision.next`), so a prior's refusal is never this evaluation's.
  `_module.specialArgs` is refused by presence (`… is set by the caller, never by a module …`):
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

- **A redeclared option's type refuses where an earlier relation's refusal ends the step, even
  where nixpkgs accepts.** The declared-type list folds as nixpkgs brackets it, and on every all-foreign
  list whose joins keep their operands' names the two engines agree, on the declaration and freeform
  planes (see "Redeclaring an option"). An earlier relation's refusal ends a fold step wherever it is
  not the decider's answer alone ("Redeclaring an option"), and where nixpkgs, asking only the later
  declaration, serves a value every declaration admits, that refusal is an **open defect** (the
  parity-defect rule), not a stated limit. Under a **foreign** outer container the element relation
  runs in foreign code and accepts what nixpkgs accepts. The list fold's cost is linear in the number of
  modules that declare one option with a type, in thunks and calls ("Redeclaring an option", **Cost**).
  Measured members:

  - two constructions of one name, `[mkOptionType { name = "int"; check = lt10; }, gt.int]` at 5, where
    each admits 5 (at 50 the refusal is the meet's: `lt10` rejects it);
  - a foreign author relation before a gen-native type, `[mkOptionType fnull, gt.int]` at 4 with
    `fnull = int` stating `typeMerge = _: null`, which the raw `[fnull, gt.int]` serves;
  - a gen union before a nixpkgs one: gen `either int bool` before `either u8 bool` at 5 and `true`;
  - a gen `enum [ "a" ]` before a nixpkgs `enum [ "z" ]` whose relation answers its own values, at
    `"a"` and `"z"`, where nixpkgs serves each though one declaration alone refuses it, an open defect
    because an enum's merged type is the union of its members.

- **A foreign join that drops a name an operand states is met** ("A foreign join that drops an
  operand's check is met"). A check family whose join renames it (`port ∥ int`, `u8 ∥ u16`, two
  separately built `ints.between 0 1`, `passwdEntry str ∥ str`, a relation answering a type keeping
  neither operand's name), raw or imported through `mkOptionType`, merges to that join and rejects what
  any operand rejects, where nixpkgs serves it. Measured members of the remaining departures:

  - one shared value declared twice, `[port, port]`, which answers `port` where nixpkgs answers `int`;
  - an author type imported through `mkOptionType` and declared BEFORE its partner, whose stated
    relation answers a renaming join: gen's engine asks the earlier relation too and meets its answer,
    so it serves what every declaration accepts, where nixpkgs asks only the later operand and refuses
    the pair. gen serves beyond nixpkgs here only within the meet's bounds.

- **A redeclared option rejects what any declaration's check rejects, even where nixpkgs serves it**
  ("A redeclared option accepts a definition only if every declared check does"). Measured members,
  each served by nixpkgs: `addCheck int p` beside `int` in either order, beside `union [ int ]`, under
  `listOf` and in a three-declaration list; two separately written `addCheck int p`; a nixpkgs
  partner of any check beside a gen type, in gen's engine, in any order and any number of
  declarations. In gen's engine a pure-nixpkgs pair is met too, so it rejects what nixpkgs serves with a
  check dropped. One shared wrapped value declared twice merges and keeps its check. An author relation whose join
  renames neither operand and drops the author's check (an author type named `int` answering plain
  `int`, completed through `mkOptionType`) is not read as exact, because gen-merge did not construct it,
  so the author's check stays owed and the dropped value is refused.

  In gen's engine this reaches a module set: nixpkgs' `addCheck` over a submodule, alone or beside
  another submodule declaration, gen or nixpkgs, at the top or as a container's element at any depth
  of gen's own fold (below a gen container too), rejects what it rejects, where nixpkgs' own rebuild
  (`fixupOptionType`) erases it and serves. A foreign record states no check witness, so every foreign
  module-set declaration's check is asked of each definition, a wrapped one or not. An ad-hoc
  `type // { check = ...; }` override there is the same check, enforced the same way: what it admits
  is served and what it rejects is refused by name. The same holds for such a record imported through
  `mkOptionType` (declared beside its twin, twice, or as the element of a nixpkgs container declared
  alone), as a member of gen's `either` or `oneOf`, as the `freeformType` of two modules, and for a
  module set copied with a `// { verify }`, whose `verify` is asked as part of its check: every step
  that joins module sets carries what the join does not.

  Not covered: in nixpkgs' engine, a wrapper over a module set (nixpkgs' rebuild erases it), and a
  check on a gen type declared first that leaves the door stating no declaration, or whose later
  relation is nixpkgs' own (nixpkgs asks only the later relation), or hidden behind a functor gen is
  handed. Nor such a check on a submodule-typed option declared inside a stock nixpkgs
  submodule, or as an `attrTag`'s tag: that option is merged by nixpkgs' own evaluation of the
  enclosing type, which erases it and serves, as nixpkgs does. Nor a drop under a
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
  every route). A second recogniser sits outside that exception, because it reads no payload: a
  record stating `carries.moduleSet` in gen's own spelling (a gen submodule, `evalModuleTree`'s
  `.type`, gen-merge's own import of a nixpkgs submodule, and any copy of them re-entering
  `mkOptionType`, gen-schema's `refined` among them) states `nestedTypes` as a function of that set
  too, so its role is the carried module set and the field is never read
  (`ci/tests/gen-module-set-laziness.nix`, a poisoned module set). A hand-built
  record claiming that spelling is served as a module set with any static `nestedTypes` role unread,
  and one stating no sub-protocol, refused by name before, is served
  (`test-a-forged-gen-module-set-record-is-served`). The residue, pinned (`test-the-residue-is-served-as-a-module-set`): such a record
  that also states a static role in `nestedTypes` (a nixpkgs submodule given an `elemType` by `//`)
  is served as a module set with that role unread; a record whose `nestedTypes` is evaluation-derived
  but whose payload states no `modules` (a hand-copied submodule) or which states no
  `getSubModules` is not recognised: one stating a module set is mounted at an option root as
  nixpkgs' `fixupOptionType` mounts it (arm (T), the root fix-up), before its `nestedTypes` is
  read, and one stating none keeps the refusal (an open defect where nixpkgs serves the shape). At an option root
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

The option names the engine serves in an option tree beside the declared ones are published as
`engineOptionNames`, one list per shape: `submodule` (`[ "_module" ]`, every evaluation) and
`freeformSubmodule` (`[ "_freeformOptions" "_module" ]`, a submodule with a freeform type), the
roots of that shape's `getSubOptions [ ]` here and in nixpkgs. The record is computed by the two
constructors that serve the names, run over a tree declaring nothing, so reading it evaluates no
submodule: a consumer refusing a name the engine owns (gen-aspects' `keySemantics` door) reads it
as data, where a submodule's own `getSubOptions` runs two evaluations
(`ci/tests/engine-option-names.nix`; the process plane's `engine-option-names` counts 0).

The module reader is nixpkgs' `unifyModuleSyntax`: a module is structured iff it carries `config` or
`options`, a structured module admits exactly nixpkgs' `attrsToRemove` and refuses any other key by
name (naming every surplus key and the file, whatever `check` says), and a shorthand module strips
nixpkgs' `shorthandAttrsToRemove` and reads every other key as config (`require` joins `imports`;
`meta` on a structured module is folded into config). Both lists also carry gen-merge's engine keys
`__pureModule`, `__reservedKeys` and `__keyEq`, and the shorthand list carries `_module`, which a shorthand module reads as config.
`__reservedKeys`, `__keyEq` and `__moduleKey` are read off the RECORD of a `__functor` module, its unapplied
value, published as `moduleSyntax.functorRecord`: nixpkgs applies a functor and collects only its
result, so a key carried there reaches no foreign evaluator, where in a module's content it is an
unsupported attribute (structured) or a configuration key (shorthand). Such a module classifies as
`dirty` for warm reuse, as every function module does.
A top-level `_module` beside `config`/`options` is refused by name as an unsupported attribute, as
nixpkgs refuses it. Its departures:

- `_class` is stripped in both forms. It is checked against the evaluation's `class` when one is
  requested, on every module nixpkgs loads; with `class = null` it is never checked, as in nixpkgs.
- `disabledModules` is a module key in both forms, as in nixpkgs, and is read by the collection
  ([Module removal](#module-removal-disabledmodules)).
- **The refusals above fire on each door's first read of a module**, as nixpkgs' `unifyModuleSyntax`
  does. That read is the declaration stratum's, which every `evalModuleTree` read forces before any
  config, and which `declaredOptions` and `substructure.declares` read directly, at any nesting; `lint`
  refuses at its own first read. So a declaration-only read refuses exactly as a config read does: on
  the typo `{ options.b = mkOption …; option.c = mkOption …; }` both `.options` and `declaredOptions`
  refuse by name, where they once answered `[ "b" ]` silently. A warm trace over an edited module the
  reader refuses is refused with it: `warmDecision.mode` on a surplus-key edit is refused where it
  once read `"warm"`.
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
  `` (module `<file>') ``. The marker is read off the RECORD of a `__functor` module first, then off
  its content: `{ __functor = …; __reservedKeys = …; }` scopes the closure of what the functor
  returns, and is the carrier for a module a foreign evaluator may also import (gen-schema and
  gen-aspects wrap a kind entry's importing defs so). The closure is every route the collector follows: nested `imports`,
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
    A content marker on the result of a module whose record carries one does not displace the
    record's: the record is read first, so a kind entry def writing its own `__reservedKeys` beside
    an imported formal is still refused.
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

| kind                    | what it catches                                                                        | why it diverges                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| ----------------------- | -------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `order-pass`            | a config def carrying an `_type = "order"` marker (`mkOrder` / `mkBefore` / `mkAfter`) | ⚠ **STALE — the divergence this row names is CLOSED.** It was true while the order pass was absent (the marker was carried as an ordinary value and mis-ordered); the pass now ships and the two engines agree on order-marked defs. The finding still fires, so a module using `mkBefore`/`mkAfter` is reported non-portable when it is not. Retiring the finding moves shipped lint cells and is therefore held for its own change, not folded into the landing that made it stale                                                                                                                                                                                                                                                   |
| `options-introspection` | a module **function** whose formals include `options`                                  | byte-mode `.options` is a minimal descriptor map (the merged decl tree), not the nixpkgs-shaped `options` structure                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `type-merge`            | the same option loc declared **with a `type`** in more than one module                 | on the type the engines agree on every all-foreign declaration list whose joins keep their operands' names (both fold it as nixpkgs brackets it, the later type deciding), and gen-merge departs by refusing where an earlier relation's refusal ends a fold step, a foreign join drops a name an operand states or a merge drops a gen record's added check, or by keeping one shared value declared twice (Known byte-mode boundaries); nixpkgs *additionally* refuses outright when both declarations carry any of `default`/`example`/`description`/`apply` (`bothHave`, ahead of the functor), where gen-merge right-biases those fields. The flag over-approximates on purpose — only the field-colliding pairs actually diverge |
| `function-to`           | an option type named `functionTo`                                                      | intentionally omitted from the type surface (wrap guard functions as data)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `unverifiable`          | an option type nested deeper than the type-walk fuel                                   | can't decide `functionTo` at that depth — reported rather than silently accepted (a portability lint must not false-negative)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |

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
# ⇒ [ { kind = "order-pass"; loc = [ "tags" ]; file = "<unknown-file>"; detail = "…"; } ]
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

### nixpkgs' `modules.sh` on this engine

`ci --tests-process` first runs nixpkgs' own `lib/tests/modules.sh` (from the `ci` flake's `nixpkgs`
input) twice: once over nixpkgs' own `lib` (the reference), and once with top-level `lib.evalModules`
replaced by `evalModuleTree`. It scores every gen assertion against the committed register
`ci/modules-sh-baseline.jsonl`: one row per assertion, keyed by its check function, env flags and argv,
with verdict `PASS`, `PASS-CLASS` (gen-merge refuses by name for nixpkgs' reason, pinned by the row's
`class` literals) or `FAIL`. Any disagreement in either direction exits 1, so a fix ratchets the
register in the same change:

```sh
nix run ./ci#modules-sh -- --write-baseline ci/modules-sh-baseline.jsonl
nix run ./ci#modules-sh -- --fold F A.log B.log C.log  # merge CI's three column logs' PERF lines
bash ci/modules-sh-ratchet.sh   # the history guard; CI runs it as the evaluators' extra step
```

- **The reference run** is nixpkgs' `lib` under the same hook, and it must PASS every assertion of its
  own suite; a reference FAIL exits 2, since that row then has no reference to be scored against. Both
  trees are named `lib`, the upstream layout: the suite's L481 assertion matches
  `.*lib/tests/modules/deferred-module-error.nix`, which nixpkgs' own lib fails from a tree of any
  other name. Before either run, one evaluation per tree checks that the gen tree runs gen and the
  reference runs nixpkgs (`deprecations` answers `true` and `false`), and after both the two runs must
  have recorded the same assertions; either one unmet exits 2.

- **Perf, per assertion**, on the 259 rows where nixpkgs serves (`checkConfigOutput`,
  `checkExpression`): each row carries, per evaluator `--version` line, both trees' `nrThunks`,
  attributed bytes and wall `ms`, read in the process that gave the verdict, with stage 2's exact bound
  on gen's thunks and bytes (`COST-REGRESSED`, `COST-RATCHET`, `UNANCHORED`, each a disagreement), and
  each run prints one `PERF modules-sh {…}` line per row with its parity. An evaluation that exits 0 and
  writes no counters exits 2. The 151 `checkConfigError` rows carry no perf: no evaluator writes
  counters for a refusing evaluation, on either tree. So stage 1's "perf at or under nixpkgs" is a claim
  over 259 assertions, and it says nothing about what a refusal costs. An `above-parity` row is the
  bar's perf criterion NOT MET, even when CI is green because the ratchet admitted its rise: admitted
  is not approved. At nixpkgs `02c087f3` on gen-merge `9edc257`, on CI's three evaluators, every one of
  the 259 rows is NOT MET: gen's thunks run from ×1.086 to ×55.368 nixpkgs' (median ×2.111, a median
  of 2343 more thunks per assertion), and its bytes at a median of ×1.883 (Nix), ×2.037 (Determinate)
  and ×2.104 (Lix).

- **The register's perf** is written from CI's own columns, as stage 2's is (`--fold`). The local
  process plane reads it only on an evaluator whose `--version` line is one of CI's (Determinate
  3.23.3, Lix 2.96.0); any other reads 259 `UNANCHORED` by construction, and a local
  `--write-baseline` never makes that green. A change that moves per-evaluation cost moves every row,
  259 per evaluator: one arm-scoped trailer, `Bar-Perf-Rise: modules-sh:* parity`, admits them all (see
  the ratchet guard below).

- **The evaluator** is resolved once from PATH and never falls back. A run for a named column sets
  `MODULES_SH_EVALUATOR` (its bin directory) and `MODULES_SH_EVALUATOR_VERSION` (the first line of its
  `--version`); either unmet exits 2, before any evaluation.

- **Each evaluation** is bounded at 120 s, and an exit other than 0 or 1 exits 2. The whole run is
  bounded at 60 minutes (three times the budget below, well inside GitHub's 360-minute job limit):
  past it the run exits 2, naming how many assertions completed. Without it, ~410 × 120 s of hanging
  evaluations would outlast the job limit and be cancelled without saying why.

- **The over-reach check** is a witness test: a class literal that also fires where nixpkgs serves
  must carry an `overreach` argument. It does not see a literal that matches a different refusal only
  on rows where nixpkgs refuses too, so authoring a class stays a review judgement.

- **The ratchet guard** refuses a register revision that lowers a key (PASS > PASS-CLASS > FAIL, or a
  PASS / PASS-CLASS key gone) unless a commit from the older revision to HEAD carries
  `Modules-Sh-Decrease: <hash> relock <census row>` (admitted only if nixpkgs' lock node moved between
  the two revisions) or `Modules-Sh-Decrease: <hash> correction <reason>`; `--write-baseline` prints
  each lowered key's hash. On a GitHub force-push it also walks the register revisions the push
  replaced and compares the replaced tip's register with HEAD's.
  What it does not decide, review reads: a relock admission is as wide as the gap between two register
  revisions, so a regression landed in a gap where nixpkgs also moved is admitted by a `relock` trailer;
  and it runs from HEAD's own tree, so a commit that edits `ci/modules-sh-ratchet.*`, or moves a
  register together with the guard's `registers` table, escapes it.
  A rise of a committed gen count needs `Bar-Perf-Rise:`, as stage 2's does; this register's reference
  node is `nixpkgs` and its arm inputs are `ci/modules-sh-lib.nix`, `ci/modules-sh-hook.bash` and
  `ci/modules-sh.nix`. Every register also takes an ARM-SCOPED trailer, `Bar-Perf-Rise: <arm>:* <class>` (`modules-sh`, `nixos-bar`, `hm-bar` or `fp-bar`), which names every rise of that register in its
  range, with each row's class still read per row: under `parity`, a row that was at or under its
  reference at the anchor and is above it now is refused even under the wildcard. The commit body still
  states the rise (each row's old and new figures, or the count, minimum, median and maximum per
  evaluator) and its attribution.

- **The budget** for the process-plane step is 20 minutes per column. Exceeding it is not a red: a
  gated cost bound counts thunks and allocation, never CPU time. It calls for running the two runs
  concurrently, then sharding the run inside the process plane.

### NixOS on this engine

Right after `modules.sh`, `ci --tests-process` evaluates NixOS through nixpkgs' own
`nixos/lib/eval-config.nix`, once with nixpkgs' `lib` and once with that `lib`'s `evalModules` replaced
by `evalModuleTree`, and scores each cell against `ci/nixos-bar-baseline.jsonl`:

- `toplevel`: `nixos/release.nix`'s eight `closures`, read to `toplevel.drvPath`; `options`: its
  `options` job, read to `optionsJSON.drvPath`. Both carry `"claim":"identity"`: an equal drvPath is
  the identity of one derivation, evidence and never acceptance.
- `doc`: one row per node of the options documentation, nixpkgs' own `optionAttrSetToDocList` entry
  for each option of the `options` job's evaluation, compared by value. These rows are the stage's
  acceptance. A node gen refuses is re-evaluated alone to read its refusal for `class`. A node both
  arms refuse is also re-evaluated alone on each arm with `--show-trace`: it scores `PASS-CLASS` when
  both refusals were caught by `tryEval` (a `throw` or a failed `assert`, never an evaluator's refusal
  for its mode), their innermost positions are one site under nixpkgs, and their final error texts are
  byte-identical (the shared throw, `ci/nixos-bar-compare.jq`). The reference arm never imports
  gen-merge, so that site is never gen-merge's code. A `toplevel` or `options` cell carries no trace,
  so one both arms refuse stays `FAIL`.
- `docs-walk`: the walk's own cost row.

Every `toplevel`, `options` and `docs-walk` row carries `perf`, per evaluator `--version` line: both
arms' `nrThunks`, attributed bytes (`envs + list + sets + values + symbols`) and wall `ms`. gen's
thunks and bytes are an exact bound: above it is `COST-REGRESSED`, below it `COST-RATCHET` (lower it in
the same change), and an evaluator with no entry is `UNANCHORED`; each is a disagreement. Wall time is
recorded and never compared. Each row also prints `at-parity` or `above-parity` against nixpkgs. An
`above-parity` row is the bar's perf criterion (perf at or under nixpkgs) NOT MET, even when CI stays
green because the ratchet admitted its rise: admitted is not approved.

```sh
nix run ./ci#nixos-bar -- --write-baseline F      # verdicts, and this evaluator's perf
nix run ./ci#nixos-bar -- --fold F A.log B.log C.log  # merge CI's three column logs' PERF lines
```

The register's perf is written from CI's own columns: dispatch `ci.yml` on the branch, download each
column's job log with `gh api --allow-escape-sequences repos/sini/gen-merge/actions/jobs/<id>/logs`,
`--fold`, commit. The fold prints each `RISE` with its trailer hash; the hash is that of
`<id>\t<evaluator>`, so it never changes between folds, and only which rows rise does. The commit that
adopts a rise names each row's old and new figures, the change that caused it, and the ruling that
admits it, with every trailer in its last paragraph. The ratchet guard reads this register too: a verdict fall needs
`Nixos-Bar-Decrease:`, and a rise of a committed gen count needs `Bar-Perf-Rise: <hash> <class>`, the
hash being that of `<id>\t<evaluator>`, where the class is `reanchor` (admitted only when nixpkgs'
lock node moved and no gen member lock node, no `lib/` byte and none of the arm's own inputs
`ci/modules-sh-lib.nix`, `ci/nixos-bar-eval.nix`, `ci/nixos-bar-cells.bash` and `ci/nixos-bar.bash` did), `parity` (the new gen figure is
at or under the new reference figure, or the row was already above its reference at the older
revision), `floor <row>` or `owner <row>`. Each program prints its `PERF` lines under its own name
(`PERF nixos-bar {…}`), and `--fold` reads only its own.

### home-manager on this engine

After NixOS, `ci --tests-process` runs home-manager (the `ci` flake's `home-manager` input, a
reference pin as `nixpkgs` is) through its own test and docs drivers, once on nixpkgs' `lib` and once
with that `lib`'s `evalModules` replaced by `evalModuleTree`, and scores each cell against
`ci/hm-bar-baseline.jsonl`:

- `test`: one row per test of home-manager's x86_64-linux suite (every attribute of
  `tests/default.nix`'s `tests`), read to what the generation writes (`home.file`, each target with its
  text's hash or its source) with `home.activationPackage.drvPath` riding along as evidence. These
  rows and the `doc` rows are the stage's acceptance.
- `doc`: one row per published node of each of home-manager's three option-doc sets (`hm`, `nixos`,
  `darwin`), nixpkgs' own `optionAttrSetToDocList` entry, over the entries the manual publishes
  (`visible && !internal`; `ci/bar-walk.nix`).
- `tests` and `docs-walk` (per set): cost rows, with stage 2's perf columns and exact bound.

The tests run in chunks of 50 (home-manager's own CI chunk size), one evaluation per chunk per arm,
up to `BAR_JOBS` at once (default: the host's cores), each under a GC heap of `BAR_HEAP` bytes
(default: the host's memory over `BAR_JOBS`); running out of it is a control failure, never a
verdict. A chunk that dies on either arm is re-run one test per process on both, and its last error
lines are printed. The `tests` cost row sums only the processes whose every test served on both
arms, so both arms sum the same work, and it carries that set's identity (process count and a sha):
its bound is compared only between equal sets, and a set that moved reads `SET-MOVED`.

Every evaluation runs `--read-write-mode` (home-manager's tests copy path literals into the store),
with import-from-derivation off (no builds) and restricted evaluation with no allowed URI (no
network); `ci/hm-bar.patch` makes the test driver return nmt's argument record and the docs driver
export each set's evaluation, and nmt comes from home-manager's own `fetchTarball` pin, fetched at
build. A doc node or test both arms refuse scores `PASS-CLASS` by stage 2's shared throw, its subject
roots nixpkgs, the patched home-manager tree and nmt: a nixpkgs alias `throw` both arms reach passes,
while an import-from-derivation refusal, which this arm's mode raises and `tryEval` cannot catch, stays
`FAIL`. A test in a chunk that died is read once more on each arm as a one-test chunk for that catch.
home-manager's NixOS and nix-darwin
integration (`tests/integration`, a VM run), the darwin suite and the release branches are not in
this arm.

An `above-parity` row is the bar's perf criterion NOT MET, even where CI stays green: admitted is
not approved. At home-manager `cb7de2c` on gen-merge `9edc257`, on CI's three evaluators, every
perf row is NOT MET: the `tests` row at ×2.450 nixpkgs' thunks (Determinate ×2.451, Lix ×2.452; 37
processes summed on both arms), the `hm` `docs-walk` at ×1.373, the `nixos` `docs-walk` at ×1.031 and
the `darwin` `docs-walk` at ×1.030.

```sh
nix run ./ci#hm-bar -- --write-baseline F
nix run ./ci#hm-bar -- --fold F A.log B.log C.log
```

The register is written as stage 2's is, and the ratchet reads it with `Hm-Bar-Decrease:` and
`Bar-Perf-Rise:`. Its reference nodes are `nixpkgs` and `home-manager`, and its arm inputs
`ci/modules-sh-lib.nix`, `ci/hm-bar-eval.nix`, `ci/bar-walk.nix`, `ci/hm-bar.patch`, `ci/hm-bar.nix`,
`ci/hm-bar-cells.bash` and `ci/nixos-bar.bash`: a `reanchor` is refused when home-manager moves
together with any of them.

### flake-parts on this engine

After home-manager, `ci --tests-process` runs flake-parts (the `ci` flake's `flake-parts-src` input) and
two real flakes built on it (`nix-fast-build`, `hercules-ci-effects`), all reference pins as `nixpkgs`
is. Each tree's own `flake.nix` is called with flake-parts' `nixpkgs-lib` input replaced by one whose
`lib` is nixpkgs' or nixpkgs' with `evalModules` replaced by `evalModuleTree`, so every evaluation
flake-parts makes runs on the engine named and nothing upstream is patched. Every real flake is handed
this flake-parts and this `nixpkgs`; its other inputs are its own lock's entries, fetched at build.
Cells, scored against `ci/fp-bar-baseline.jsonl`:

- `unit`: one row per test of flake-parts' own nix-unit suite (`dev/tests/nix-unit.nix`), read to the
  hash of its `expr`.
- `memo`: flake-parts' own memoize check (`dev/tests/perSystem-memoize`), read to its `result` and the
  number of stderr lines carrying the trace that check counts. The check asserts the trace fires once,
  so a count that differs is `FAIL`.
- `template`: one row per flake-parts template, read to its outputs.
- `flake`: each real flake's output names. These rows and the three above are the stage's acceptance.
- `flake-drv`: each real flake's x86_64-linux `packages`, `checks` and `devShells`, each name to its
  drvPath, carrying `"claim":"identity"` (evidence, never acceptance). hercules-ci-effects' `checks`
  and `devShells` are its `dev` partition's, which fetches a second nixpkgs at evaluation, and are not
  in this arm.

Every row is a perf row, read in the cell's own process. The suite cells run concurrently, as stage 3's
do; the real flakes run one evaluation at a time. Each run also evaluates each real flake and template
once more with `evalModules` throwing a token generated for that run and never written down; that read
must refuse with the token, or the seam did not reach it and the run is a control failure. The mode is
stage 3's (read-write, no import from derivation, restricted with no allowed URI).

An `above-parity` row is the bar's perf criterion NOT MET, even where CI stays green: admitted is not
approved.

```sh
nix run ./ci#fp-bar -- --write-baseline F
nix run ./ci#fp-bar -- --fold F A.log B.log C.log
```

The register is written as stage 2's is, and the ratchet reads it with `Fp-Bar-Decrease:` and
`Bar-Perf-Rise:`. Its reference nodes are `nixpkgs`, `flake-parts-src`, `nix-fast-build` and
`hercules-ci-effects`, and its arm inputs `ci/modules-sh-lib.nix`, `ci/fp-bar-eval.nix`,
`ci/fp-bar-cells.bash`, `ci/fp-bar.nix` and `ci/nixos-bar.bash`.

## Theoretical foundations

- **byte-mode = the conformance oracle + terminal contract** (structural-dedup spike §3).
- **priority = one override rule**, the grepped subset (design spec §7), plus the nixpkgs **order
  pass** as compat vocabulary — precedence itself is gen's graph-position-and-provenance question, not
  the integer lattice's.
- **deferredModule = a lazy constructor**, inspectable before forcing (Lorenzen 2025 §2.3).
- **the `(loc, defs)` hook = the escape the engine rides** (nixpkgs `mkOptionType.merge`).
