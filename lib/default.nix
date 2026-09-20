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
#             REQUIRED, no default — the `memo` precedent below, and here the reason is measured
#             rather than chosen. This formal read `types ? { }` and the prose above it called the
#             argument optional for byte-mode bring-up; that default DID NOT EVALUATE. The published
#             `types` namespace is a linkset merge whose allowlist names three collisions AGAINST THE
#             LEAF VOCABULARY, so an empty vocabulary makes every entry stale and `merge.types`
#             throws from inside: `linkset: allowlist entry 'attrsOf' names no actual collision
#             between 'gen-types' and 'gen-merge'`. A default that throws is strictly worse than no
#             default at all — a caller reading this header cannot tell "I called it wrong" from
#             "the library is broken", whereas a missing required formal aborts AT THE CALL SITE
#             naming `types`. Nothing loses a default it was using: every construction in this repo
#             and every by-path consumer in the ecosystem already passes it explicitly, swept
#             (den-hoag-qsrcp). The checker contract is `verify : v -> null|err`.
#   memo    : gen-memo.lib (ADR-0008 item 2 — the ONE incremental plane's reuse DECISION,
#             `warmDecision`). REQUIRED, no default: gen-merge computes the bipartite
#             contribution-relation FACT (design spec §2.1) and hands it to gen-memo, which decides
#             `isClean` over it — this library no longer decides reuse on its own footprint set.
#   scope   : gen-scope.lib (ADR-0006, ADR-0008 §1 — the ONE universal graph evaluator). REQUIRED,
#             no default, and bound HERE rather than at `evalModuleTree` because that is the only
#             channel reaching `lib/types.nix`'s structural folds: `submodule`'s `mergeDefs` is a
#             2-arity protocol field (`loc: defs`) the engine invokes through `ownFold` from the
#             top-level binding `mergeDefsWith`, over a type value `strategies` constructs before
#             any per-call argument exists. `core` closes over it once, `types.nix` inherits
#             `evalModuleTree` from `core`, and every nested invocation acquires the evaluator
#             without naming it — so NO call site anywhere changes. Measured both ways
#             (den-hoag-0pk67): a per-call formal reddens `types.submodule` with
#             `called without required argument 'scope'` through `lib/types.nix:298`.
#             The foreclosed arm is a DEFAULT: a defaulted formal cannot refuse, and the door below
#             is the component. The convention `types`/`memo` state above governs here too.
{
  prelude,
  types,
  memo,
  scope,
}:
let
  # ── THE EVALUATOR DOOR, TOTAL, ONCE PER CONSTRUCTION ──────────────────────────────────────────
  # A published door that ADMITS a value outside its contract and then diverges inside the fixpoint
  # is `den-hoag-qy84y`'s defect. This one refuses a non-evaluator BY NAME, at the first demand of
  # `core`, `tryEval`-catchably — never as an `attribute '…' missing` raised from inside the knot,
  # which is what the absence of a door reads as (measured: `scope = { }` ⇒ an uncontained abort at
  # the driver site). The shape is gen-scope's own `carrierDefect`: a total arm per term, each arm
  # establishing what the next one reads, returning the REASON rather than throwing it, so the
  # message is a value a cell can assert instead of text `tryEval` discards.
  #
  # The terms are the names this library actually uses and no others — `eval`, `buildRoots`,
  # `vertex`, `empty`. A door quantifying over gen-scope's whole surface would refuse a conformant
  # partner for a name nothing here demands; a door naming fewer would let one through to abort
  # inside the knot, which is the state it exists to end.
  scopeDefect =
    s:
    if s == null then
      "declares no `scope' — the module tree is evaluated on the one universal graph evaluator (ADR-0006), and there is no second driver to fall back to"
    else if !builtins.isAttrs s then
      "declares a `scope' that is a ${builtins.typeOf s} rather than the gen-scope library record"
    else
      let
        # `empty` is a graph VALUE; the other three are applied. Both lists are ordered so the
        # message is stable across evaluations rather than in whatever order the record was built.
        applied = [
          "buildRoots"
          "eval"
          "vertex"
        ];
        missing = builtins.filter (n: !(s ? ${n})) (applied ++ [ "empty" ]);
        unapplicable = builtins.filter (n: !builtins.isFunction s.${n}) applied;
      in
      if missing != [ ] then
        "declares a `scope' with no ${builtins.concatStringsSep ", " missing} — the evaluator terms this engine drives the module-tree knot through"
      else if unapplicable != [ ] then
        "declares a `scope' whose ${builtins.concatStringsSep ", " unapplicable} cannot be applied"
      else
        null;

  checkedScope =
    let
      defect = scopeDefect scope;
    in
    if defect == null then scope else throw "gen-merge: ${defect}";

  priority = import ./priority.nix { inherit prelude; };
  # ★ THE DOOR IS FORCED BY `core` ITSELF, NOT BY THE FIRST USE OF THE EVALUATOR. `scope` is read
  # only where the knot is driven, so without this `seq` a defective evaluator would sit unexamined
  # until some consumer happened to evaluate a module tree — a refusal raised inside the fixpoint,
  # which is the shape the door exists to replace. Hung here, every member derived from `core`
  # raises it at the construction instead, and `flake.nix`'s surface force reaches all of them: there
  # is no state in which `gen-merge.lib` exists and its evaluator has not been checked.
  core = builtins.seq checkedScope (
    import ./modules.nix {
      inherit prelude priority memo;
      scope = checkedScope;
    }
  );
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
    # STRATUM 1 ON ITS OWN — the declared option records, from the same fold the full result's
    # `options` field is merged by, and with no fixpoint driven at all (ADR-0033: a two-level type
    # system's declaration stratum is a fold, not an ascent). A consumer wanting declarations
    # WITHOUT values — an introspection pass, an identity key set — asks for them here instead of
    # evaluating a whole tree and projecting `.options` off it, and gets a named refusal rather
    # than a divergence if the declarations it is asking about turn out to need the value stratum.
    declaredOptions
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

  # ── THE nixpkgs-PARITY SURFACE — COMPAT VOCABULARY, AND AN INTERIM ───────────────────────────
  #
  # Two things land here together, and the marker below governs both.
  #
  # ★★★ MARKER — INTERIM (ADR-0031 F1's marker discipline). `mergeDefaultOption` is a NEW EXPORTED
  # SURFACE BESIDE `mergeLeaf`, NOT a replacement for it. `mergeLeaf` (lib/modules.nix) REMAINS this
  # engine's no-`.merge` default and keeps its agree-or-refuse posture, so no existing consumer's
  # merge semantics move on that axis. Nothing inside this library routes through the law; the one
  # caller it exists for is gen-aspects' freeform primitive arm.
  # **What it explicitly does NOT claim: whole-pipeline nixpkgs parity.** It is ONE law at ONE arm.
  # Replacing `mergeLeaf` with it would not have bought parity either — nixpkgs' own
  # `attrsOf`/`listOf` merge each key THROUGH the element type, where this law's attrset arm is a
  # shallow `//` chain that never consults it, so two definitions of `attrsOf (listOf str)` sharing
  # a key CONCATENATE under nixpkgs and DROP THE FIRST under this law. The interim is therefore not
  # a compromise against a better-but-larger option. Real parity at the leaf is a per-type merge
  # question, and it is the merge design review's subject rather than this export's.
  #
  # ★★ AND THE ORDER VOCABULARY IS COMPAT SURFACE, NOT gen's AUTHORITY MODEL. gen expresses
  # precedence by GRAPH POSITION AND PROVENANCE, deliberately not by an integer priority lattice.
  # `mkOrder`/`mkBefore`/`mkAfter` and the pass behind them exist because gen accepts nixpkgs module
  # vocabulary and a definition written in it must not leak its wrapper into the value domain — they
  # are the compatibility promise being kept, and they carry no architectural claim about how gen
  # itself decides which contribution wins.
  #
  # ★ PARITY IS VERIFIED AGAINST A PINNED nixpkgs, AND THE PIN IS STAMPED HERE SO IT CANNOT AGE
  # SILENTLY. This library's `lib/` is nixpkgs-free (ci/tests/purity.nix), so the law and the pass
  # are an INDEPENDENT REIMPLEMENTATION rather than a wrapper: when the module system upstream
  # moves, nothing here notices. The rev below is read back out of this file by
  # ci/tests/parity-surface.nix and compared, both directions, against the rev `ci/flake.lock`
  # actually resolves for the root's own `nixpkgs` input. A routine bump reds that cell with both
  # laws byte-unchanged — which is intended: it is a prompt to re-verify parity and re-stamp, never
  # an assertion that the law broke.
  #
  # nixpkgs-parity-rev:begin
  #   20b1ddd1aa5ace70c9468305030aa4f9ef79671b
  # nixpkgs-parity-rev:end
  inherit (core) mergeDefaultOption;
  inherit (priority)
    mkOrder
    mkBefore
    mkAfter
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
  # composes through the hub's rehomed `flakeModules.default` (ADR-0031 F1, INTERIM — gen-flake
  # dissolved) while the corpus path named above may be a different crossing. Whether a gen leaf type
  # mounting in a *foreign*, non-gen-authored `lib.evalModules` can work at all is no longer an open
  # empirical question in the ecosystem — a real external consumer does exactly this and it discharges
  # once identity keys are declared at the kind boundary (`den-hoag-i546n`) — but that is evidence
  # about the general phenomenon, not a re-examination of this file's own `nixpkgs-protocol.nix` site,
  # and it settles nothing about which reading ADR-0023 ultimately rules. So this still states the
  # tension and picks no side.
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
        attrs.ground = ''
          The one name at which BOTH sides mint a nullary VALUE rather than a constructor, and the
          drop-in meaning here is the folding one twice over: a mounting consumer declaring `attrs`
          needs what several modules contribute to that option COMBINED, and needs an answer for the
          case where nobody contributed anything. Neither is sayable by a predicate over one value,
          which is what gen-types' entry is; that predicate stays reachable through the hub's flat
          roster and from gen-types directly, unchanged and still minted where it was.
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
