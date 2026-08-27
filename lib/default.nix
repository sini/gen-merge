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
  linkset = import ./linkset.nix { inherit prelude; };

  # A leaf vocabulary arrives from OUTSIDE this library — gen-types by default, and in compat mode a
  # foreign one — so entering the published namespace is an inbound crossing followed by an outbound
  # one: the record is read through the boundary's import environment and rebuilt as a gen type, which
  # is then expressed in the foreign protocol like every other type this library publishes.
  #
  # ★★★ THE REFUSAL IS PROPAGATED, AND RETURNING IT AS AN ABSENCE WAS THE DEFECT. The import
  # environment is PARTIAL: handed a record that carries an element type or a module set while
  # answering only part of the sub-protocol, it computes W4a's refusal BY NAME. Swallowing that and
  # publishing the record unchanged put a protocol-incomplete value into `lib.types`, where a mounting
  # consumer dies INSIDE the foreign engine on a missing attribute — the uncatchable, unnamed abort
  # that this boundary's own `refuseMount` exists to convert into a refusal. A computed refusal thrown
  # away is worse than one never computed: the library knew and declined to say.
  #
  # ★ "NO SHIPPED ROSTER TRIPS IT" IS NOT A REASON TO SWALLOW, because the foreign vocabulary is the
  # UNCONTROLLED input. The default roster does not trip it, measured; the `types` parameter names
  # whatever vocabulary a consumer supplies, and being total over that is the entire reason the import
  # environment answers with a refusal rather than best-effort.
  #
  # There is no absence arm because there is no reachable case for one: both callers below have
  # already established `isAttrs` and `verify`-or-`name`, which excludes the import environment's
  # other two refusals by construction, so the carrier refusal is the only one that reaches here — and
  # a refusal is not an absence. A caller wanting the value back unrefused would be asking to publish
  # a type the boundary has just said it cannot translate.
  importLeaf =
    v:
    let
      answer = core.interface.importType v;
    in
    if answer ? refused then throw answer.refused else answer.imported;

  # A PARAMETRIC leaf's merge relation, revisited at gen-types' k1uv mint (43adfdc, pushed
  # a1a5de3): a checker's identity is now minted over its CONSTRUCTION — constructor plus inert
  # arguments — rather than its name, and `typeEq`/`conservativeEq` (gen-types `lib/default.nix`)
  # dispatches on that mint via the tagged `__mint` sum. Two claims this relation used to make are
  # retired by it, and one is not:
  #   · "gen-types' `__id` is NAME-only" — false: `enum "e" [ "a" ]` and `enum "e" [ "b" ]` now mint
  #     apart, and `struct "s"` over different fields does too.
  #   · "value equality is pointer-based over the closures (two identical constructions compare
  #     UNEQUAL)" — false for a MINTED family: two separately-built `enum "e" [ "a" "b" ]`s mint the
  #     SAME digest and compare equal. It is STILL TRUE for a SEALED one (`refined`, a `struct`
  #     carrying a caller `verify`, `typedef`/`typedef'`): their `check` is a bare lambda rebuilt on
  #     every call, and gen-types' own README says `typeEq` still separates two identical sealed
  #     constructions ("What a checker's identity is minted over"). Sealed and foreign leaves (no
  #     `__mint.minted` at all) therefore keep the ORIGINAL refusal below, unchanged.
  #
  # What the MINTED half buys is real but narrower than nixpkgs' own `enum`, whose functor UNIONS two
  # DIFFERING value sets on merge (`binOp = a: b: unique (a ++ b)`) — that half is NOT reproduced
  # here. `__mint.minted` is a one-way `"type:<sha256>"` digest (gen-identity `hashIdentity`), and the
  # checker record `mkChecker` returns carries neither a constructor's arguments (an enum's `elems`,
  # a struct's `members`, …) nor any accessor for them — deliberately, per gen-types' own README
  # ("publishing a caller-facing construction form would decide that open vocabulary by accretion").
  # So a differing-construction pair is not "cannot be compared" — the mint compares it fine, and
  # says unequal — it is "cannot read component values" to reconcile the difference. Reading them
  # back would need a NEW channel, on gen-types or on this boundary, and picking one is a design fork
  # of its own: banked on den-hoag-parametric-merge-unlock-6wb87 for an owner ruling rather than
  # settled here.
  #
  # So: two checkers that mint to the SAME construction merge — trivially, to either operand, since a
  # digest match means they denote one type — and every other pair still refuses by name. A consumer
  # declaring one option twice with an unreconciled parametric leaf still gets a NAMED REFUSAL rather
  # than a wrong type: gen-merge's own on its declaration path (lib/modules.nix `redeclareDecl`), and
  # the foreign engine's `already declared` under a mount.
  refuseParametricMerge = name: other: {
    refused = "`${name}' and `${
      if builtins.isAttrs other then other.name or "<unnamed>" else "<not a type>"
    }', whose parameters live behind their own predicate and cannot be compared";
  };
  # The MINTED-but-differing refusal — same shape as `refuseParametricMerge`, a different reason,
  # because the two are no longer the same failure. This one fires only when a digest was minted and
  # the two did not match, so "cannot be compared" would be a lie: the mint compared them and they
  # are not the same construction. What is missing is a channel back to their arguments.
  refuseUnreconciledMint = name: other: {
    refused = "`${name}' and `${
      if builtins.isAttrs other then other.name or "<unnamed>" else "<not a type>"
    }', which mint to different constructions and carry no readable component values to reconcile";
  };
  completeParametric =
    v:
    if builtins.isFunction v then
      (x: completeParametric (v x))
    else if builtins.isAttrs v && v ? verify then
      let
        base = importLeaf v;
        digest = base.__mint.minted or null;
        # `self` is threaded exactly as `mkTypeWith` threads its own — the value a caller holds is
        # the EXPORTED type, so a match answers with that rather than with the pre-export record.
        rel =
          self: other:
          if digest == null then
            refuseParametricMerge (base.name or "<unnamed>") other
          else if builtins.isAttrs other && (other.__mint.minted or null) == digest then
            { merged = self; }
          else
            refuseUnreconciledMint (base.name or "<unnamed>") other;
        exported = strategies.defineType (base // { typeMergeRel = rel exported; });
      in
      exported
    else
      v;
  # A NULLARY leaf keeps the default relation: it has no parameters, so a same-named partner really is
  # the same type, and `str` merged with `str` must stay non-null.
  completeExport =
    v:
    if builtins.isFunction v then
      completeParametric v
    else if builtins.isAttrs v && (v ? verify || v ? name) then
      strategies.defineType (importLeaf v)
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
  # ★ AN OPEN TENSION, RECORDED HERE BECAUSE THIS IS WHERE A READER MEETS IT — NOT RESOLVED HERE. The
  # paragraph above is a claim that a gen leaf type MOUNTS in a foreign (flake-parts) options tree, and
  # that mount is the whole reason this completion exists. gen-schema's own demo states the opposite
  # invariant about the same boundary: "No gen *type* ever enters the flake-parts options tree — the
  # value-injection invariant that lets a gen schema coexist with flake-parts"
  # (gen-schema `examples/demo/README.md`). Both cannot hold unqualified of the same ecosystem.
  # ADR-0023 rules the unqualified form — what crosses is provably plain data — the TARGET, BY
  # CONSTRUCTION, and today's unstated crossings a DECLARED INTERIM: "every currently-unstated crossing
  # site becomes a declared opt-out or is fixed". The two readings may yet reconcile, since the demo
  # composes purely through gen-flake while the corpus path named above may be a different crossing.
  # But whether the site named above really mounts a gen TYPE, rather than composing through gen-flake
  # like the demo, has never been measured — so this states the tension and picks no side.
  # Deciding it belongs to the crossing chain ADR-0023 governs (with ADR-0014 — the boundary is the
  # eval, not the repo — supplying why a foreign `evalModules` is a crossing at all), not to this file.
  #
  # gen-types exports two shapes, and completing only the first leaves half the namespace unmountable.
  # The NULLARY leaves (`str`, `int`, `bool`, …) are attrsets and complete directly. The PARAMETRIC ones
  # (`enum`, `struct`, `union`, `tuple`, `refined`, `optionalAttr`, …) are CONSTRUCTORS — functions — so
  # completing the export is a no-op and the type the constructor RETURNS reaches a consumer bare. That is
  # the same shape as the crash the protocol completion was introduced for: nixpkgs' module system reads
  # `deprecationMessage` off every option type and aborts with `attribute 'deprecationMessage' missing`.
  # So descend THROUGH the application, at any arity, and complete the first result that is a type.
  # ★ THE EXPORT MERGE IS DECIDED, NOT DEFAULTED. This was `(mapAttrs completeExport types) //
  # strategies` — two libraries' export environments joined by `//`, with a non-empty intersection,
  # silently. Nix `//` is right-biased, so `strategies` won at every shared name and a consumer got
  # gen-merge's `listOf` where it may have wanted gen-types'; nothing said so and nothing could.
  #
  # ★ AND THE GROUNDS BELOW UTTER NO FOREIGN CONSTANT, WHICH IS NOT A STYLE CHOICE. A ground that
  # named the foreign namespace would put a foreign constant in the type vocabulary — the exact thing
  # the protocol boundary exists to confine to one unit. This library's own purity scan is what
  # caught the first draft doing it, which is the scan working rather than the scan being in the way.
  #
  # Cardelli 1997 gates a linkset merge on `exp(L) ∩ exp(L') = ∅` (Definition 5-7's precondition).
  # The overlap here is real and is not going away, so the rule is disjointness WITH A DECLARED
  # ALLOWLIST: every collision is named, carries the ground for which side wins AT THAT NAME, and
  # leaves the shadowed value reachable. An undeclared collision refuses.
  types =
    (linkset.mergeExports {
      left = {
        library = "gen-types";
        exports = builtins.mapAttrs (_: completeExport) types;
      };
      right = {
        library = "gen-merge";
        exports = strategies;
      };
      allow = {
        listOf.ground = ''
          This namespace is the drop-in a foreign module system mounts, and at this name such a
          consumer requires the CROSS-DEFINITION MERGE meaning: the strategy folds definitions
          across modules, where gen-types' constructor is a structural PREDICATE over one value.
          The cost is exactly the unqualified spelling inside this namespace — the gen-types
          predicate stays reachable through the hub's flat roster and from gen-types directly.
        '';
        attrsOf.ground = ''
          The same cross-definition merge meaning as `listOf`, over attribute sets rather than
          lists: a mounting consumer declaring `attrsOf` in a foreign module system needs
          definitions from several modules folded, not one value checked. Stated for THIS name
          rather than carried from `listOf` because the two constructors differ in what they fold.
        '';
        option.ground = ''
          ★ THE WEAKEST ENTRY, AND IT SAYS SO. This library's `option` is a bare alias for
          `nullOr`, so what shadows gen-types' parametric `option` is an alias rather than a
          distinct construct — the winning side wins by sitting in the drop-in namespace, not by
          meaning more. This is the first entry to retire if the namespace is ever split.
        '';
      };
    }).exports;
}
