# gen-merge public API — the byte-mode module MERGE engine (`evalModuleTree`).
#
# The MERGE half of the pure-gen module system: reproduces `lib.evalModules` + `lib.types`-merge
# OUTPUT for den's surface with zero nixpkgs (design spec
# `gen-specs/gen-resolve/2026-07-02-evalmoduletree-byte-mode-design.md`). Checking is gen-types'
# job (spec §4); gen-merge owns the def→value fold + the structural strategies.
#
# Class layering: gen-prelude → gen-types → **gen-merge** → { gen-schema, gen-aspects }; BELOW
# gen-resolve (the schedule-only conductor). Function <=> deps (convention §8): this file has deps,
# so it is a function of named VALUES.
#
#   prelude : gen-prelude.lib (the pure builtins/utility base)
#   types   : gen-types.lib (the injected leaf CHECKERS — { <name> = { verify; check; } }).
#             OPTIONAL for byte-mode bring-up: defaults to {}; tests inject a minimal stub. Wiring the
#             real gen-types later is a one-line input swap — the checker contract is `verify:v->null|err`.
{
  prelude,
  types ? { },
}:
let
  priority = import ./priority.nix { inherit prelude; };
  core = import ./modules.nix { inherit prelude priority; };
  strategies = import ./types.nix { inherit prelude core; };
  lintLib = import ./lint.nix { inherit prelude priority core; };

  completeParametric =
    v:
    if builtins.isFunction v then
      (x: completeParametric (v x))
    else if builtins.isAttrs v && v ? verify then
      # `typeMerge` REFUSES for a parametric leaf. Its parameters live behind the `verify`/`check`
      # closures and are not introspectable, so there is no payload to compare — and the two candidate
      # substitutes both fail: gen-types' `__id` is NAME-only (`enum "e" [ "a" ]` and `enum "e" [ "b" ]`
      # share an id, as do two `struct "s"` over different fields), and value equality is pointer-based
      # over the closures (two identical constructions compare UNEQUAL). Left on the nullary default,
      # `pureTypeMerge` would answer "mergeable" for any same-named partner and silently discard one
      # declaration's allowed values — precisely the unsoundness the structural functors removed. So the
      # honest answer is "not mergeable": a consumer declaring one option twice with a parametric leaf
      # gets nixpkgs' `already declared` error rather than a wrong type. This diverges from nixpkgs'
      # `enum`, whose functor UNIONS the value sets; gen-merge cannot reproduce that without reading
      # parameters it cannot see.
      strategies.mkOptionType (v // { typeMerge = _f': null; })
    else
      v;
  # A NULLARY leaf keeps the plain completion: it has no parameters, so `pureTypeMerge`'s self-merge is
  # correct for it and `str.typeMerge str.functor` must stay non-null.
  completeExport =
    v:
    if builtins.isFunction v then
      completeParametric v
    else if builtins.isAttrs v && (v ? verify || v ? name) then
      strategies.mkOptionType v
    else
      v;
in
{
  # Portable-subset lint (README "Portable-subset lint") — statically flag modules using constructs
  # outside the byte-mode surface, so the byte-identity claim is mechanically verifiable.
  inherit (lintLib) lint;

  # The engine + the shared fold (spec §2) + module-system helpers consumers need.
  inherit (core)
    evalModuleTree
    mergeDefs
    mergeOneOption
    showOption
    # Fixed-input kernel marker (spec §2.5) — pairs with `evalModuleTree { coreShortCircuit = true; }`.
    mkCoreValue
    # Source-class substrate (design spec §3): the author's `pureModule` clean-module marker. Its
    # companion `classifyModule` predicate stays on the INTERNAL core seam (lib/modules.nix) — the
    # lint-predicate export precedent: additive to core, public surface unchanged. The warm re-eval path
    # and the classify suite read it through core, not this public surface.
    pureModule
    ;

  # The priority subset (spec §1 / §7) — one override rule + two combinators.
  inherit (priority)
    mkOverride
    mkOptionDefault
    mkDefault
    mkForce
    mkMerge
    mkIf
    ;

  # Structural strategies (spec §2/§4) also surfaced at the top level.
  inherit (strategies)
    mkOption
    mkOptionType
    submodule
    listOf
    attrsOf
    lazyAttrsOf
    deferredModule
    nullOr
    option
    either
    oneOf
    raw
    anything
    ;

  # The unified `types` namespace — gen-types leaf CHECKERS ⊎ gen-merge structural strategies.
  # This is the `lib.types` drop-in the re-host (C2/C3) points at: `lib.types.X` → `genMerge.types.X`.
  # The injected gen-types leaf checkers are PROTOCOL-COMPLETED (via `strategies.mkOptionType`) so they
  # too mount inside a real nixpkgs `lib.evalModules` — mkIdentityModule's `id_hash` uses `types.str`,
  # which the corpus's `mkInstanceRegistry` mounts in flake-parts. gen-merge's own strategies are already
  # completed at their constructors (types.nix). A non-type entry (non-type value) passes through.
  #
  # gen-types exports two shapes, and completing only the first leaves half the namespace unmountable.
  # The NULLARY leaves (`str`, `int`, `bool`, …) are attrsets and complete directly. The PARAMETRIC ones
  # (`enum`, `struct`, `union`, `tuple`, `refined`, `optionalAttr`, …) are CONSTRUCTORS — functions — so
  # completing the export is a no-op and the type the constructor RETURNS reaches a consumer bare. That is
  # the same shape as the crash the protocol completion was introduced for: nixpkgs' module system reads
  # `deprecationMessage` off every option type and aborts with `attribute 'deprecationMessage' missing`.
  # So descend THROUGH the application, at any arity, and complete the first result that is a type.
  types = (builtins.mapAttrs (_: completeExport) types) // strategies;
}
