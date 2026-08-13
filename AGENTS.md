# gen-merge — agent capability sheet

## Scope

Byte-mode module **merge** engine: `evalModuleTree` collects a module tree, ties one local `config`
fixpoint, resolves per-option definitions by priority, dispatches structural types to their
`.merge`, routes undeclared keys through a `freeformType`, and verifies leaves through injected
gen-types checkers — reproducing `lib.evalModules` + `lib.types`-merge **output** with zero nixpkgs.

## Not this library's job

Quoted text is the owner's own `flake.nix` `description` field, verbatim.

| Responsibility | Owner |
|---|---|
| Deciding whether a value is well-typed (`verify : v -> null\|err`); every leaf CHECKER (`str`, `int`, `enum`, `struct`, `union`, `refined`, …) | `gen-types` — "gen-types: pure, nixpkgs-lib-free structural type checker for the gen ecosystem". Injected as a VALUE (`flake.nix:13`, `lib/default.nix:18`); gen-merge owns only the def→value fold |
| General utilities (gen-merge's only other dep; every `builtins` re-export and vendored helper) | `gen-prelude` — "gen-prelude: vendored, nixpkgs-lib-free pure utilities for the gen ecosystem" |
| Kinds, instances, typed registries, refs, content-addressed identity | `gen-schema` — "gen-schema: typed record registry with extension points for the pure-gen module system". A CONSUMER: `gen-schema/flake.nix:11,25` takes `gen-merge.url` and passes `merge = gen-merge.lib` |
| Aspect traits / classification / aspect composition types | `gen-aspects` — "gen-aspects: aspect-oriented composition types (pure-gen, re-hosted on gen-merge)". A CONSUMER: `gen-aspects/flake.nix:9,23` takes `gen-merge.url` and passes `merge = gen-merge.lib` |
| Class partition / contract / apply / gate; deciding what a fixed-input core projection contains | `gen-class` — "gen-class — pure-Nix class-share mechanism (partition / contract / apply / gate) for the pure-gen module system". gen-merge is **injected**, never a gen-class flake input: `gen-class/lib/default.nix:6` takes `merge ? null`, and the hub supplies it (`gen/lib/mkGenLibs.nix` `class` entry imports `${genInputs.gen-class}/lib` with `merge = genInputs.gen-merge.lib`). Its tier-2 `applyCoreFixed` calls `merge.mkOption` / `merge.mkCoreValue` / `merge.evalModuleTree { coreShortCircuit = true; }` (`gen-class/lib/apply.nix:160-179`) and throws when `merge == null` (`:167`) |
| Cross-node demand scheduling, convergence loops, the D>I>P conductor | `gen-resolve` — "gen-resolve — demand-driven higher-order RAG evaluator over algebraic scope graphs (Knuth 1968 attribute schedule + Vogt 1989 HOAG)". gen-merge is the *within-node* merge, BELOW it |
| The nixpkgs boundary, composing flakes, building systems, and deciding whether an edit reduces to a modules-append (the caller side of the warm knobs) | `gen-flake` — "gen-flake — the pure composition boundary of the pure-gen module ecosystem". Its `compose` result carries the `override` handle that supplies `warmFrom` / `editedModules` (`gen-flake/lib/compose.nix:118-119,146,194-195`) |
| Search monad, records, intensional functions, either-as-a-monad | `gen-algebra` — "gen-algebra: pure Nix algebra — search monad, records, intensional functions, either". gen-merge does not depend on it: `grep -rn 'gen-algebra\|genAlgebra' lib/ flake.nix default.nix` exits 1 with no output, while the same instrument over the same roots for `'gen-types\|genTypes'` hits `lib/modules.nix`, `lib/types.nix`, `lib/default.nix`, `flake.nix`, `default.nix` |
| Injecting external arguments into NixOS modules | `gen-bind` — "gen-bind: module binding with external arguments for Nix" |
| Layered settings resolution, refs-as-data, graduated injection | `gen-settings` — "gen-settings — stratified settings resolution as a pure layered fold, with refs-as-data, structured provenance, and the graduated injection construct" |
| Change propagation / the AFFECTED set across a build graph | `gen-rebuild` — "gen-rebuild: pure-Nix incremental rebuilder core (Mokhov rebuilder dimension)". gen-merge's warm path is per-eval loc reuse, not a rebuilder |
| Selector predicates over graph positions | `gen-select` — "gen-select: selector algebra for attributed graph positions" |
| Choosing a winner among matched rules, ordered groups | `gen-dispatch` — "gen-dispatch: relational rule dispatch over ordered groups (the dispatch STEP)" |
| Scope-graph attribute evaluation | `gen-scope` — "gen-scope: demand-driven attribute grammar evaluator over algebraic scope graphs" |

## Exports

Entry: `inputs.gen-merge.lib` (flake). Root `default.nix` is a **function** of
`{ lock ? …, fetch ? …, prelude ? …, types ? … }` — every argument defaulted from `flake.lock` via
`builtins.fetchTree`, so `import ./default.nix { }` works standalone. `lib/default.nix` takes
`{ prelude, types ? { } }`; `types` is optional (see traps).

**Engine + the shared fold**

| Export | Signature |
|---|---|
| `evalModuleTree` | `{ modules; specialArgs ? {}; check ? true; prefix ? []; coreShortCircuit ? false; warmFrom ? null; editedModules ? []; } -> result` |
| `mergeDefs` | `loc -> type\|null -> [{ file; value; }] -> value` (the `(loc, defs)` escape hatch; never short-circuits) |
| `mergeOneOption` | `loc -> [{ file; value; }] -> value` (exactly one def permitted, else throw) |
| `showOption` | `[string] -> string` (dot-join) |

`result` = `{ config; options; provenance; undeclared; type; freeformConfig; freeformProv; warmDecision; }`.
`config` is the merged output, `options` the merged decl tree, `provenance` a lazy per-loc record,
`undeclared` the definitions not merged into `config` (`[ { path; file; } ]`, empty under a
`freeformType`), `type` the tree-as-a-type for nesting; `freeformConfig` / `freeformProv` /
`warmDecision` are the warm-path memo layers and decision trace.

**Priority / property algebra** — `lib/priority.nix`

| Export | Signature |
|---|---|
| `mkOverride` | `int -> a -> { _type = "override"; priority; content; }` |
| `mkOptionDefault` / `mkDefault` / `mkForce` | `a -> override` at priority `1500` / `1000` / `50` (a bare def is `100`) |
| `mkMerge` | `[a] -> { _type = "merge"; contents; }` |
| `mkIf` | `bool -> a -> { _type = "if"; condition; content; }` |

**Option + type constructors** — `lib/types.nix`

| Export | Signature |
|---|---|
| `mkOption` | `descriptor -> descriptor // { _type = "option"; }`; the engine reads `type` / `default` / `apply` / `readOnly` |
| `mkOptionType` | `{ name; check? ; merge? ; verify? ; … } -> optionType` — completes the record to the full 14-field nixpkgs protocol |

**Structural merge strategies** — `lib/types.nix`

| Export | Signature |
|---|---|
| `submodule` | `module\|[module] -> type` (nested `evalModuleTree`; binds per-key `name`) |
| `listOf` | `type -> type` (concat in def order, each element merged through the element type) |
| `attrsOf` / `lazyAttrsOf` | `type -> type` (per-key merge; byte-identical output, distinct functor names) |
| `deferredModule` | `type` (a value) — merges defs into `{ imports = [ … ]; }`, never forced |
| `nullOr` / `option` | `type -> type` (`option` is the same binding as `nullOr`); null defs drop |
| `either` | `type -> type -> type` |
| `oneOf` | `[type] -> type` (right-nested `either`; empty list throws) |
| `raw` | `type` (a value) — one winner, or all-equal winners |
| `anything` | `type` (a value) — lists concat, attrsets recurse per key, else one value survives |

**Unified type namespace**

| Export | Signature |
|---|---|
| `types` | `attrset` — `(mapAttrs completeExport <injected gen-types>) // <gen-merge strategies>` (`lib/default.nix:117`) |

**Markers consumed by the opt-in knobs** — `lib/modules.nix`

| Export | Signature |
|---|---|
| `mkCoreValue` | `{ digest; values; } -> { __coreValue = true; digest; values; }` — recognised only under `coreShortCircuit = true` |
| `pureModule` | `fn -> { __pureModule = true; __functor = self: fn; }` — the author's clean-module assertion, read pre-application |

**Portability lint** — `lib/lint.nix`

| Export | Signature |
|---|---|
| `lint` | `{ modules; } -> [ { kind; loc; file; detail; } ]` (empty ⇒ portable). Kinds: `order-pass`, `options-introspection`, `type-merge`, `function-to`, `unverifiable` |

**Completed `optionType` shape** (14 fields, `lib/types.nix:145-176`): `_type`, `name`,
`description`, `descriptionClass`, `deprecationMessage`, `check`, `merge`, `emptyValue`,
`getSubOptions`, `getSubModules`, `substSubModules`, `typeMerge`, `nestedTypes`, `functor`.

**Provenance record** (per declared loc): `{ defs = [{ file; priority; }]; winners = [{ file; }]; priority = <int>; defaulted = <bool>; }`. Per freeform loc: `defs` only, the other three `null`.

**`warmDecision` record**: `{ mode = "warm"|"cold"; reason = <string|null>; reused = [<loc-string>]; remerged = { <loc-string> = <reason>; }; modules = { clean; dirty; edited; }; }`.

## Entry points by task

| Task | Reach for |
|---|---|
| Evaluate a module tree | `evalModuleTree { modules = […]; }` → `.config` |
| Declare a typed option | `mkOption { type = types.X; default? ; apply? ; readOnly? ; }` |
| Override / conditionalise a definition | `mkForce` / `mkDefault` / `mkOverride N` / `mkIf` / `mkMerge` |
| Custom `(loc, defs)` combine for one option | `mkOptionType { name = "…"; merge = loc: defs: …; }` |
| Custom combine that permits exactly one def | `mergeOneOption` as that type's `merge` |
| Fold a def list outside the engine | `mergeDefs loc type defs` (consumes YOUR list order — see traps) |
| Nest a keyed collection of sub-configs | `types.attrsOf (types.submodule …)`; the `name` formal is bound per key |
| Carry a module value without forcing it | `types.deferredModule` |
| Absorb undeclared keys | a top-level `freeformType = types.lazyAttrsOf types.raw`, or `_module.freeformType` (lower priority) |
| Nest a whole tree inside a parent tree | `(evalModuleTree …).type` as an option's `type` |
| Ask where a value came from | `.provenance.<path>` → `{ defs; winners; priority; defaulted; }` |
| Re-evaluate after an APPENDED edit | `evalModuleTree { modules = base ++ edited; warmFrom = prev; editedModules = edited; }` |
| Assert a function module reads only specialArgs | `pureModule (args: …)` |
| Hand the engine a pre-merged subtree | `mkCoreValue { digest; values; }` + `coreShortCircuit = true` |
| Check a module set stays inside the byte-mode surface | `lint { modules = […]; }` |
| Mount a gen type inside a real nixpkgs `lib.evalModules` | any `types.*` value — already protocol-completed (except the tree-as-type; see traps) |

## Measured traps

Each row verified in this run against the flake's wired `.lib`. Preamble: `flk = builtins.getFlake "…/gen-merge"`; `l = flk.lib`; `t = l.types`; `gt = flk.inputs.gen-types.lib` (the injected leaves);
`cfg = args: (l.evalModuleTree args).config`; `ev = l.evalModuleTree`; `try = e: (builtins.tryEval (builtins.deepSeq e e)).success`.

| Trap | Evidence |
|---|---|
| `types` is a union in which gen-merge's strategies WIN, and exactly three names collide: `listOf`, `attrsOf`, `option` | `lib/default.nix:117`; `builtins.filter (n: gt ? ${n}) <strategy names>` ⇒ `["listOf","attrsOf","option"]`. `gt.listOf t.str ? merge` ⇒ `false` vs `(t.listOf t.str) ? merge` ⇒ `true`; `(t.option t.str).name` ⇒ `"nullOr"`. gen-types' `list` is a separate name and survives |
| `import ./lib { prelude = …; }` with no `types` arg SUCCEEDS and yields a strategies-only namespace — no leaf checkers, no error | `lib/default.nix:18` (`types ? { }`); bare import ⇒ `builtins.attrNames bare.types` = 13 names, `bare.types ? str` ⇒ `false`. Control, same run, flake-wired: `l.types ? str` ⇒ `true` |
| `types.mkOption` and `types.mkOptionType` are inside the `types` namespace (the whole strategies set is unioned in) | `l.types ? mkOption` ⇒ `true` |
| `functionTo` is absent from the type surface | `t ? functionTo` ⇒ `false`. The lint kind `function-to` is the detector. Test: `test-reject-function-to` (`ci/tests/lint.nix`) |
| gen-types' PARAMETRIC leaves reach `types` as bare constructors; the completion descends through the application, but the completed result **never merges with another of its own kind** | `lib/default.nix:26-53`; `builtins.isFunction t.enum` ⇒ `true`, `(t.enum "e" ["a"])._type` ⇒ `"option-type"`, `(t.enum "e" ["a"]).typeMerge (t.enum "e" ["a"]).functor` ⇒ `null`. Control, same run, nullary leaf: `(t.str.typeMerge t.str.functor) == null` ⇒ `false`. Diverges from nixpkgs `enum`, whose functor unions the value sets. Tests: `test-parametric-leaf-protocol-complete`, `test-parametric-leaf-typeMerge-refuses`, `test-typeMerge-nullary-self-merges` (`ci/tests/nixpkgs-protocol.nix`) |
| The tree-as-a-type `(evalModuleTree …).type` is the ONE type on the surface that is NOT protocol-completed | `lib/modules.nix:1169-1178`; `builtins.attrNames inner.type` ⇒ `["merge","name"]` — no `check`, `functor`, `emptyValue`, `deprecationMessage`. Control, same run: `builtins.attrNames t.raw` ⇒ the 14 protocol fields; a completed gen-types leaf `t.str` ⇒ 17 (those 14 + `__id`, `__name`, `verify`) |
| A nested tree surfaces `.config` only — the inner tree's provenance is not threaded out | `lib/modules.nix:1171-1177`; nested merge ⇒ `{ i = "I"; }`, while the outer `provenance.nested` is the OUTER option's leaf record `["defaulted","defs","priority","winners"]` |
| `attrsOf` and `lazyAttrsOf` never merge with each other, and same-name containers merge only if their ELEMENTS do | `lib/types.nix:298-301`; `(t.attrsOf t.str).typeMerge (t.lazyAttrsOf t.str).functor` ⇒ `null`; `(t.attrsOf t.str).typeMerge (t.attrsOf t.int).functor == null` ⇒ `true`. Control, same run: `(t.attrsOf t.str).typeMerge (t.attrsOf t.str).functor != null` ⇒ `true`. Test: `test-typeMerge-container-elements` |
| DECLARATION merging does not use the functor at all: the same option declared with different types in two modules field-unions, **later type wins, silently** | `lib/modules.nix:100-122`; `str` then `int` ⇒ `.options.x.type.name` ⇒ `"int"`. `l.lint` on the identical pair ⇒ `["type-merge"]`. Tests: `test-reject-type-merge`, `test-accept-apply-redeclare-is-not-type-merge` (`ci/tests/lint.nix`) |
| Definition order is REVERSE module order — but `mergeDefs` does NOT reverse, it consumes the caller's list order | `lib/modules.nix:999-1004`; three modules contributing `["a"]`/`["b"]`/`["c"]` to a `listOf str` ⇒ `["c","b","a"]`, while `l.mergeDefs ["loc"] (t.listOf t.str) [{file="f1";value=["a"];} {file="f2";value=["b"];}]` ⇒ `["a","b"]`. Test: `test-oracle-has-teeth-list-order` (`ci/tests/oracle.nix`) |
| `anything` never reports a scalar conflict — it silently keeps the value from the EARLIEST module (the reversed def stream's last element) | `lib/types.nix:468-485`; modules `{ x = 1; }` then `{ x = 2; }` ⇒ `1`; `[1]` then `[2]` ⇒ `[2,1]` |
| `raw` collapses multiple EQUAL defs instead of refusing (nixpkgs `raw` is `mergeOneOption`) | `lib/types.nix:459-463` + `:126-139`; two `x = 1` defs ⇒ `1`; `x = 1` / `x = 2` ⇒ threw. `mergeOneOption` is exported separately for the strict rule: one def ⇒ value, two ⇒ threw |
| An order marker (`mkOrder`/`mkBefore`/`mkAfter`) is carried through as an ORDINARY VALUE — no throw, no ordering | `lib/priority.nix:56-89`; `{ _type = "order"; priority = 500; content = ["z"]; }` on a `t.raw` option ⇒ the marker attrset IS the merged value. `l.lint` on the same shape ⇒ `["order-pass"]`, the only detector. Test: `test-reject-order-pass-in-config` |
| `check = false` keeps undeclared keys OUT of `config` (that is the flag's purpose) but no longer drops them silently — they are listed on the result SIBLING `undeclared`, never inside `config` | `lib/modules.nix:1175-1182` (report), `:1149-1155` (the `check = true` throw); `check = false` with `{ nosuch = 1; }` ⇒ `builtins.attrNames config` ⇒ `[]` **and** `result.undeclared` ⇒ `[ { path = ["nosuch"]; file = …; } ]`. Controls, same run: `check = true` ⇒ threw; the same input under a `freeformType` ⇒ the key is absorbed into `config` and `undeclared` ⇒ `[]`. Tests: `ci/tests/undeclared.nix` |
| `either` dispatches on the FIRST def's shape then merges ALL defs through that member; a mixed-shape pair fails with a raw Nix type error that `builtins.tryEval` CANNOT catch | `lib/types.nix:439-446`; `either str (listOf str)` with defs `"s"` and `["z"]` ⇒ `nix eval` exit **1**, `error: expected a list but found a string: "s"`, escaping a `tryEval (deepSeq …)` wrapper. Controls, same run: the `["z"]` def alone ⇒ `["z"]`; the `"s"` def alone ⇒ `"s"` |
| `mkCoreValue` with the knob OFF is an ordinary attrset — its `__coreValue`/`digest`/`values` keys reach the merged value | `lib/modules.nix:69-86`, `:547`; `attrsOf raw` option, default off ⇒ `builtins.attrNames config.x` ⇒ `["__coreValue","digest","values"]`; `coreShortCircuit = true` ⇒ `{ a = "A"; }`. Tests: `test-default-off-marker-is-plain-value`, `test-sole-core-skips-throwing-spine` (`ci/tests/core-kernel.nix`) |
| EVERY function module is classified DIRTY — including one that ignores its argument entirely | `lib/modules.nix:267-279`; `(_: { options.x = …; })` ⇒ `warmDecision.modules` = `{clean=[];dirty=["<gen-merge>"];edited=[]}`. Controls, same run: the SAME function under `l.pureModule` ⇒ `clean=["<gen-merge>"]`, `dirty=[]`; a plain attrset module ⇒ `clean=["<gen-merge>"]`. Tests: `test-bare-lambda-is-dirty`, `test-pure-module-is-marked-pure` (`ci/tests/classify.nix`) |
| Reading provenance forces that loc's defs to WHNF — a bare-`throw` def fires on a plain `.defs` LENGTH read, before any value is touched | `lib/modules.nix:590-611`; `builtins.length prov.x.defs` over `{ x = throw "BOOM"; }` ⇒ `try` `false`. Control, same run, non-throwing config: `builtins.length prov.x.defs` ⇒ `2`, `.priority` ⇒ `50` (an `mkForce`), `.defaulted` ⇒ `false`. Tests: `test-discharge-attribution`, `test-provenance-does-not-disturb-values` (`ci/tests/provenance.nix`) |
| A FREEFORM provenance record reports `winners`/`priority`/`defaulted` as `null` — "not observable", not "no override" | `lib/modules.nix:1073-1099`; a freeform loc ⇒ `{ winners = null; priority = null; defaulted = null; }` with `defs` length `1`. Test: `test-freeform-reduced-record` |
| Warm splices only declared leaves outside the dirty footprint, and refuses outright on `disabledModules` in an edited entry | `lib/modules.nix:421-503`, `:956-973`; base+edited ⇒ `mode = "warm"`, `reused = ["a"]`, `remerged = { b = "edited-def"; }`, and `warm.config == cold.config` ⇒ `true`. Controls, same run: no `warmFrom` ⇒ `mode = "cold"`, `reused = []`; an edited entry carrying `disabledModules` ⇒ `mode = "cold"`, `reason = "disabledModules on an edited module (warm refused)"`. Tests: `test-registry-reuse-whole-result-and-decision`, `test-disabled-modules-edited-refuses` (`ci/tests/warm.nix`) |
| `.options` is a bare descriptor map, not the nixpkgs `options` structure | `lib/modules.nix:947`; `builtins.attrNames result.options.x` ⇒ `["_type","default","type"]` — no `loc`, `declarations`, `files`, `isDefined`. A module function taking an `options` formal is lint kind `options-introspection`. Test: `test-reject-options-introspection` |
| The returned `.config` is `_module`-free even when a module sets `_module.args` | `lib/modules.nix:1046-1058`; a module with `_module.args.foo = 1` ⇒ `builtins.attrNames config` ⇒ `["x"]`. The `_module`-bearing view exists only inside module bodies |
| An undefined option is an error ONLY when its type declares no `emptyValue` | `lib/modules.nix:505-520`; undefined `attrsOf str` ⇒ `{}`, undefined `submodule {}` ⇒ `{}`, undefined `str` ⇒ threw. Same split for a SOLE `mkIf false` def: `listOf str` ⇒ `[]`, `str` ⇒ threw. Test: `test-emptyValue-matches-nixpkgs` |
| `deferredModule.check` is STRICTER than nixpkgs — it rejects a string that looks like an absolute path | `lib/types.nix:332-353`; `t.deferredModule.check "/abs/mod.nix"` ⇒ `false`, `t.deferredModule.check { }` ⇒ `true`. Tests: `test-deferredModule-check-shapes`, `test-deferredModule-check-and-getSubOptions-agree` |
| The core-seam predicates are NOT on the public `.lib` | `lib/default.nix` re-exports a subset of `lib/modules.nix`; `l ? mergeOption`, `l ? classifyModule`, `l ? collectModules`, `l ? warmDecide`, `l ? setDefaultModuleLocation`, `l ? isOptLeaf`, `l ? mergeOptionDecls` all ⇒ `false`. CI reaches them by importing the file directly (`genMergeCore = import ../lib/modules.nix …`, `ci/flake.nix`) |
| `oneOf []` throws at construction; `submodule` binds `name` per key | `lib/types.nix:449-457`, `:246-252`; `try (l.oneOf [ ])` ⇒ `false`; an `attrsOf (submodule ({ name, … }: …))` registry with key `host1` ⇒ the sub-option default resolves to `"host1"` |

Read, **not exercised** in this run: `substSubModules` replacement semantics (`lib/types.nix:222` —
covered by `test-substSubModules-rebuilds`), `coalesceUnmatched`'s per-module freeform regrouping
(`lib/modules.nix:193-204`), and the compat path that injects nixpkgs `lib.types` as the leaf
`types` (`ci/flake.nix`, suite `compat`).

## Theory

`README.md` states its claims as one flat **Theoretical foundations** list (no Implements /
Informed-by split), restated in code comments:

- **byte-mode = the conformance oracle + terminal contract** (structural-dedup spike §3). It
  reproduces nixpkgs' order-sensitive merge; it does not implement the confluent semilattice merge,
  structural equivalence (`≈ₛ`), or pre-eval identity dedup. The per-option combine is a swappable
  kernel (`README.md` §Byte-mode scope).
- **priority = one override rule**, the grepped subset (design spec §7) — lowest priority-number
  wins, ties merge, nixpkgs' order pass dropped (`lib/priority.nix:1-17`).
- **`deferredModule` = a lazy constructor**, inspectable before forcing (Lorenzen 2025 §2.3).
- **the `(loc, defs)` hook = the escape the engine rides** (nixpkgs `mkOptionType.merge`).

Two further claims live in their own sections rather than that list:

- the nixpkgs `optionType` **protocol** is replicated purely — `defaultFunctor`,
  `elemTypeFunctor`, `defaultTypeMerge`, `mergeEqualOption` reproduced with no nixpkgs import
  (`lib/types.nix:43-176`), so one type value serves both engines.
- the warm path is described as "the reverse-cone reuse of adios's `mkOverride`, but sound under
  gen-merge's config *fixpoint* (adios has none)", with `warmDecision` delivering "what was reused
  vs re-evaluated" as data (`README.md` §Warm re-eval).

Design spec (cross-repo citation):
`den-architecture/gen-specs/gen-resolve/2026-07-02-evalmoduletree-byte-mode-design.md`.

**Checked invariant**: `lib/` is `nixpkgs.lib`-free — enforced by `ci/tests/purity.nix` over
`lib/**.nix` + the root `flake.nix` + `default.nix` (NOT `ci/`, where nixpkgs is the harness and the
equivalence oracle's reference side).

## Drift check

```sh
nix eval --json .#lib --apply 'l: { top = builtins.attrNames l; types = builtins.attrNames l.types; }'
```

Current output (verbatim):

```json
{"top":["anything","attrsOf","deferredModule","either","evalModuleTree","lazyAttrsOf","lint","listOf","mergeDefs","mergeOneOption","mkCoreValue","mkDefault","mkForce","mkIf","mkMerge","mkOption","mkOptionDefault","mkOptionType","mkOverride","nullOr","oneOf","option","pureModule","raw","showOption","submodule","types"],"types":["any","anything","attrs","attrsOf","bool","defaultOnError","deferredModule","derivation","either","enum","float","formatErrors","function","int","intensionalEq","intersection","lazyAttrsOf","list","listOf","mkOption","mkOptionType","mkValidator","never","null","nullOr","number","oneOf","option","optionalAttr","path","pathLike","raw","refined","refinements","runValidators","str","strict","string","struct","submodule","tuple","typeEq","typedef","typedef'","union"]}
```

The `types` half depends on the LOCKED `gen-types` input (`flake.lock`), so a leaf-name change there
moves this output without any gen-merge commit.

The command observes export *names* only; signatures, trap rows and `file:line` refs rot without
changing its output.

**Checks.** Test-runner invocation (from the repo root; CI runs the same command with
`working-directory: ci`, `.github/workflows/ci.yml:13,18` — then `nix fmt -- --ci` at `:19`):

```sh
nix flake check ./ci
```
