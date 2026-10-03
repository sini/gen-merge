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
#             REQUIRED, no default — the `memo` precedent below. A defaulted vocabulary cannot be
#             told apart from a forgotten one: `{ }` now publishes a strategies-only namespace (it
#             once threw from inside), so a `types ? { }` default would hand a caller who forgot the
#             argument a namespace with no leaves, where a missing required formal aborts AT THE
#             CALL SITE naming `types`. Every construction in this repo and every by-path consumer
#             already passes it explicitly, swept (den-hoag-qsrcp). The checker contract is
#             `verify : v -> null|err`.
#             It is the gen-types LIBRARY, bound by its roster key, and not a pluggable leaf
#             vocabulary: the core builds every exported type through gen-types' check-witness
#             protocol (`witnessRecord`, `witnessedCheck`, `rewritesCheck`), so a `types` without it is refused by
#             name at construction (den-hoag-ydro3, owner-ruled). A nixpkgs `lib.types` value is
#             still accepted wherever a type is, as a FOREIGN VALUE through the protocol boundary
#             (`lib/interface.nix`); it is never the vocabulary. The foreign-vocabulary mode this
#             formal once documented is withdrawn, and a consumer needing one gets a parameter of
#             its own rather than this slot.
#             WHAT THE ASSEMBLY CHECKS OF IT, and no more: that it is an untagged attribute set
#             (`vocabularyDefect` below — a null, a list, or a tagged value such as a flake's
#             outputs refuses by name), that it carries the check-witness protocol and that the
#             protocol agrees with the test this library restates inline (the same door), that
#             each type-shaped member imports through the refusing import environment
#             (`importLeaf`), and that every name it shares with this library's strategies is
#             declared in `types-allowlist.nix`. Beyond the protocol, which names it carries is
#             not judged: a name it shares UNdeclared with the strategies refuses, by name, when
#             demanded, and every other name still publishes. Members that are neither a type
#             record nor a function pass through unexamined, and a function member is examined
#             only when applied (den-hoag-ltnf7).
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
      "declares no `scope' — the module tree is evaluated on the one universal graph evaluator, and there is no second driver to fall back to"
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
        # `buildRoots` and `eval` are gen-scope DOORS (functors, den-hoag-7gp66 P2), which
        # `builtins.isFunction` reads as `false`; the prelude's reader is the functor-aware one.
        unapplicable = builtins.filter (n: !prelude.isFunction s.${n}) applied;
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

  # ── THE VOCABULARY DOOR — `scopeDefect`'s shape, over the one fact this library demands of `types`
  # before the per-member import: that it is a RECORD OF NAMES. A non-attrset aborted `mapAttrs`
  # uncatchably. A TAGGED attrset is a value, not a namespace — `_type` is how Nix marks one, and a
  # flake's outputs carry `_type = "flake"` — and admitting one published `narHash`/`inputs`/… as types,
  # so the consumer's `types.str` aborted uncatchably instead.
  #
  # ★ THE LAST CLAUSE IS THE CHECK-WITNESS PROTOCOL, AND IT IS WHAT THE `types` FORMAL MEANS. gen-types
  # owns the protocol (`witnessRecord` builds the published `check`, which is also its witness,
  # `witnessedCheck` the pair's layout, `rewritesCheck` the test), and this library's core builds every exported type through it and reads every
  # fold's witness by it, its own strategies included, so a `types` without it leaves the core with
  # no way to publish a type at all. The formal is the gen-types library, bound by its roster key
  # (den-hoag-ydro3, owner-ruled): a leaf vocabulary of another origin is not what it takes, and a
  # default for a missing protocol would publish unwitnessed exports, whose rewritten `check` is
  # then dropped without a word. Which other names the library carries is not judged here.
  protocolNames = [
    "rewritesCheck"
    "witnessRecord"
    "witnessedCheck"
  ];
  vocabularyDefect =
    t:
    if !builtins.isAttrs t then
      "declares a `types' that is a ${builtins.typeOf t} rather than a leaf vocabulary record (an attribute set)"
    else if t ? _type then
      let
        tag = if builtins.isString t._type then t._type else builtins.typeOf t._type;
      in
      "declares a `types' that is a tagged `${tag}' value rather than a leaf vocabulary record"
      + (if tag == "flake" then " — a flake's outputs; its vocabulary is the flake's `lib'" else "")
    else
      let
        missing = builtins.filter (n: !(t ? ${n})) protocolNames;
        unapplicable = builtins.filter (n: !prelude.isFunction t.${n}) protocolNames;
      in
      if missing != [ ] then
        "declares a `types' with no ${
          builtins.concatStringsSep ", " (map (n: "`${n}'") missing)
        } — the `types' formal is the gen-types library, whose check-witness protocol every type this library exports is built and read through (a gen-types older than that protocol lacks them)"
      else if unapplicable != [ ] then
        "declares a `types' whose ${
          builtins.concatStringsSep ", " (map (n: "`${n}'") unapplicable)
        } cannot be applied — the check-witness protocol every type this library exports is built and read through"
      else
        witnessDisagreement t;

  # ── THE AGREEMENT DOOR — the protocol's test against the spellings this library restates ───────
  # Four per-fold sites restate `rewritesCheck` inline rather than call it, because a call is an
  # environment on every fold and the fold's allocation ratchets have no headroom for one:
  # `interface.importedFold`, `modules.nix` `ownFold` and `threadedAs`, and `types.nix` `isValid`,
  # which asks it negated. So the protocol has two spellings, gen-types' and this one, and a change to
  # what gen-types' witness holds would leave the inline one reading every record wrong: a renamed
  # field reads every rewritten `check` as the type's own, and a field holding something else reads
  # every own `check` as rewritten. Either can keep verdicts green. This door asks both spellings, and
  # the exported test, about the two records the protocol itself makes — the pair `witnessedCheck`
  # builds, and that pair with its `check` replaced as a wrapper replaces it — and refuses, by name,
  # a protocol any of them answers against, or answers other than a boolean about them (an `if` over
  # a non-boolean aborts uncatchably at the first fold that asks).
  #
  # `exportType` restates the PAIR too: it publishes the one record `witnessRecord` builds under
  # both field names itself, because taking `witnessedCheck`'s two-field result costs every exported
  # type a set it must then read or copy (den-hoag-ydro3, owner-ruled arm (c)). So `witnessedCheck`'s
  # output is the layout that spelling is held to: the door refuses a pair whose fields are not
  # exactly the two `exportType` spells (a field beyond them would be lost from every exported type),
  # a `witnessRecord` whose record is not shaped as the one `witnessedCheck` publishes, and a
  # protocol whose readers read the spelled pair otherwise than `witnessedCheck`'s. Its claim is
  # scoped to those records: every fold meets only records of these shapes, or witness-less ones,
  # which it never asks about. The inline spellings read a witness-less record `false` by their `?`
  # guards; that `rewritesCheck` does too (and answers a boolean there) is held by gen-types' own
  # suite, not by this door. It costs a few small records per construction.
  witnessDisagreement =
    t:
    let
      own = t.witnessedCheck (_: true);
      # `exportType`'s spelling, restated: `witnessRecord`'s one record under both fields.
      record = t.witnessRecord (_: true);
      spelled = {
        check = record;
        _checkWitness = record;
      };
      # The inline test, spelled as the sites spell it: positively, and as `isValid` asks it.
      inline = r: r ? _checkWitness && r ? check && r.check != r._checkWitness;
      inlineOwn = r: !(r ? _checkWitness && r ? check) || r.check == r._checkWitness;
      readers = {
        "gen-types' `rewritesCheck'" = t.rewritesCheck;
        "the inline test" = inline;
        "the inline test's negation" = r: !(inlineOwn r);
      };
      # Each reader's answers over `pair` and over `pair` with its `check` replaced. A non-boolean
      # answer is named before any answer is compared.
      readPair =
        pair: what:
        let
          replaced = pair // {
            check = _: true;
          };
          answers = builtins.mapAttrs (_: rewrites: {
            own = rewrites pair;
            replaced = rewrites replaced;
          }) readers;
          notBool = builtins.concatLists (
            builtins.attrValues (
              builtins.mapAttrs (
                reader: a:
                builtins.concatMap
                  (
                    n:
                    if builtins.isBool a.${n} then
                      [ ]
                    else
                      [
                        "${reader} answers a ${builtins.typeOf a.${n}} over ${
                          if n == "own" then what else "${what} with its `check' replaced"
                        }"
                      ]
                  )
                  [
                    "own"
                    "replaced"
                  ]
              ) answers
            )
          );
          wrong = builtins.concatLists (
            builtins.attrValues (
              builtins.mapAttrs (
                reader: a:
                (if a.own then [ "${reader} reads ${what} as rewritten" ] else [ ])
                ++ (
                  if a.replaced then [ ] else [ "${reader} reads that pair with its `check' replaced as its own" ]
                )
              ) answers
            )
          );
        in
        if notBool != [ ] then
          "declares a `types' whose check-witness protocol answers other than a boolean: ${builtins.concatStringsSep "; " notBool}. Its test is a predicate"
        else if wrong != [ ] then
          wrong
        else
          null;
      ownRead = readPair own "the pair `witnessedCheck' built";
      spelledRead = readPair spelled "the pair this library spells from `witnessRecord'";
      fieldList = r: builtins.concatStringsSep ", " (map (n: "`${n}'") (builtins.attrNames r));
    in
    if !builtins.isAttrs own then
      "declares a `types' whose `witnessedCheck' builds a ${builtins.typeOf own} rather than the record carrying `check' and its witness"
    else if builtins.isString ownRead then
      ownRead
    else if ownRead != null then
      "declares a `types' whose check-witness protocol disagrees with the test this library restates inline at its per-fold sites: ${builtins.concatStringsSep "; " ownRead}. The two spellings must say the same thing, so a gen-types whose witness changed needs a gen-merge restating the changed test"
    else if builtins.attrNames own != builtins.attrNames spelled then
      "declares a `types' whose `witnessedCheck' builds the fields ${fieldList own} rather than exactly `check' and `_checkWitness', the two this library publishes on every exported type, so a field beyond them would be lost from each"
    else if !builtins.isAttrs record then
      "declares a `types' whose `witnessRecord' builds a ${builtins.typeOf record}, where the check witness this library publishes under both fields of every exported type must be a record"
    else if
      !builtins.isAttrs own.check || builtins.attrNames record != builtins.attrNames own.check
    then
      "declares a `types' whose `witnessRecord' builds a record with the fields ${fieldList record} where the record `witnessedCheck' publishes has ${
        if builtins.isAttrs own.check then
          fieldList own.check
        else
          "none (it is a ${builtins.typeOf own.check})"
      }, so the pair this library spells from it on every exported type is not the pair `witnessedCheck' builds"
    else if builtins.isString spelledRead then
      spelledRead
    else if spelledRead != null then
      "declares a `types' whose check-witness protocol reads the pair this library spells from `witnessRecord' otherwise than the pair `witnessedCheck' builds: ${builtins.concatStringsSep "; " spelledRead}. Every exported type publishes the spelled pair, so its witness would be misread"
    else
      null;

  checkedTypes =
    let
      defect = vocabularyDefect types;
    in
    if defect == null then types else throw "gen-merge: ${defect}";

  priority = import ./priority.nix { inherit prelude; };
  # ★ THE DOOR IS FORCED BY `core` ITSELF, NOT BY THE FIRST USE OF THE EVALUATOR. `scope` is read
  # only where the knot is driven, so without this `seq` a defective evaluator would sit unexamined
  # until some consumer happened to evaluate a module tree — a refusal raised inside the fixpoint,
  # which is the shape the door exists to replace. Hung here, every member derived from `core`
  # raises it at the construction instead, and `flake.nix`'s surface force reaches all of them: there
  # is no state in which `gen-merge.lib` exists and its evaluator has not been checked.
  # The vocabulary door is forced the same way and for the same reason: the core builds every export
  # through `types`' check-witness protocol, so there is no state in which the library exists over a
  # `types` without that protocol, or with one its inline test disagrees with.
  core = builtins.seq checkedScope (
    builtins.seq checkedTypes (
      import ./modules.nix {
        inherit
          prelude
          priority
          memo
          strategies
          ;
        scope = checkedScope;
        types = checkedTypes;
      }
    )
  );
  strategies = import ./types.nix {
    inherit prelude core;
    types = checkedTypes;
  };
  lintLib = import ./lint.nix { inherit prelude priority core; };
  linkset = import ./linkset.nix { inherit prelude; };

  # A leaf vocabulary arrives from OUTSIDE this library — gen-types, a library of its own — so
  # entering the published namespace is an inbound crossing followed by an outbound
  # one: the record is read through the boundary's import environment and rebuilt as a gen type, which
  # is then expressed in the foreign protocol like every other type this library publishes.
  #
  # ★★★ THE REFUSAL IS PROPAGATED, AND RETURNING IT AS AN ABSENCE WAS THE DEFECT. The import
  # environment is PARTIAL: handed a record that carries an element type or a module set while
  # answering only part of the sub-protocol, it computes W4a's refusal BY NAME. Swallowing that and
  # publishing the record unchanged put a protocol-incomplete value into `lib.types`, where a mounting
  # consumer dies INSIDE the foreign engine on a missing attribute — the uncatchable, unnamed abort
  # that this boundary exists to convert into a refusal. A computed refusal thrown
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
  #     SAME digest and compare equal. A type with a SEALED component (`refined`, a `struct` carrying a
  #     caller `verify`, `typedef`/`typedef'`) mints too, with the component in `__sealed`, and `typeEq`
  #     decides it (`same`, below): one binding is one type, two separately written lambdas are
  #     refused. A leaf with no `__mint.minted` at all (an `enum` over a path, a self-referential type)
  #     keeps the ORIGINAL refusal below, unchanged.
  #
  # A differing-construction pair is not "cannot be compared" — the mint compares it fine, and says
  # unequal — so what reconciles it is a LAW over the two constructions, read back through the
  # vocabulary's certifying reader `payloadOf` (gen-types: the construction payload, read-only and
  # non-identity-bearing; owner ruling on den-hoag-parametric-merge-unlock-6wb87). One law exists:
  # nixpkgs' own `enum` functor UNIONS two differing value sets (`binOp = a: b: unique (a ++ b)`), and
  # so does this relation for two `enum`s under one name. The digest stays the identity: a payload
  # decides WHICH law applies and what the union holds, never whether two types are one.
  #
  # So: two checkers that mint to the SAME construction merge — trivially, to either operand, since a
  # digest match means they denote one type — two same-named `enum`s merge to their union, and every
  # other pair still refuses by name, saying whether a payload was unreadable or no law exists for the
  # constructions. A consumer declaring one option twice with an unreconciled parametric leaf still gets
  # a NAMED REFUSAL rather than a wrong type: gen-merge's own on its declaration path
  # (lib/modules.nix `redeclareDecl`), and the foreign engine's `already declared` under a mount.
  #
  # Both operands are named through `interface.nameOf`, the library's one total reader, so a partner
  # whose name is not a string is refused by name here rather than aborting the interpolation.
  inherit (core.interface) nameOf;
  refuseParametricMerge = t: other: {
    refused = "`${nameOf t}' and `${nameOf other}', whose parameters live behind their own predicate and cannot be compared";
  };
  # The ONE-MARK refusal: two types that mint one mark and are not one type, because they differ at a
  # SEALED component the mark is blind to (a caller-supplied predicate, a registered construction).
  # `decided` says whether the vocabulary's `typeEq` answered `false` (two different registered
  # constructions) or refused (two separately written lambdas, which no `==` tells apart from one); its
  # own refusal text is caught by `tryEval`, so the reason and the way out are stated here.
  refuseSharedMark = t: other: decided: {
    refused =
      "`${nameOf t}' and `${nameOf other}', which mint one identity and differ at a sealed component (a caller-supplied predicate or a registered construction) that identity is blind to"
      + (
        if decided then
          ", and their sealed subjects decide them two types"
        else
          ", where two separately written predicates cannot be compared: declare one binding, or register the predicate (gen-algebra `mkIntensional`) so that two constructions of it decide"
      );
  };
  # The MINTED-but-differing refusal — same shape as `refuseParametricMerge`, a different reason,
  # because the two are no longer the same failure. This one fires only when the two carry DIFFERENT
  # marks (a pair sharing a mark takes `refuseSharedMark`), so "cannot be compared" would be a lie: the
  # mint compared them and they are not the same construction. `pa`/`pb` are the operands' certified payloads, or `null` where
  # one could not be read, and the message says which of the two is missing: a readable payload, or
  # a law reconciling the constructions both payloads name.
  refuseUnreconciledMint = t: other: pa: pb: {
    refused =
      "`${nameOf t}' and `${nameOf other}', which mint to different constructions"
      + (
        if pa == null || pb == null then
          " and carry no readable component values to reconcile"
        else
          let
            ctorOf =
              p: if builtins.isString p.ctor then p.ctor else "<a constructor of type ${builtins.typeOf p.ctor}>";
          in
          if pa.ctor == "enum" && pb.ctor == "enum" then
            ", and gen-merge reconciles two `enum's only under one name"
          else if pa.ctor == pb.ctor then
            ", and gen-merge has no reconciliation law for `${ctorOf pa}'"
          else
            ", and gen-merge has no reconciliation law between `${ctorOf pa}' and `${ctorOf pb}'"
      );
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
        # ★ SAMENESS FIRST, decided by the vocabulary's own `typeEq` (den-hoag-6orb8 U1; design §1,
        # "Where both operands carry a gen identity … gen-merge decides redeclaration on that
        # identity"). A digest match alone is NOT sameness: gen-types' mark is blind to a type's
        # SEALED components (a caller lambda, a registered construction), which `typeEq` decides over
        # beside it, so two lambda `typedef`s sharing a mark would merge on the mark. `true` merges (one
        # binding redeclared, two constructions of one registered term); `false` or a refusal goes on to
        # the reconciliation laws below and otherwise to the named refusal.
        #
        # Where NEITHER operand seals anything, the mark is a total identity and a digest match is
        # that decision read off the operands' own fields (equal marks, `{ } == { }`), as before;
        # it is also the arm a wrapper's `//` keeps (`addCheck` over a parametric leaf declared
        # twice from one value), whose rewritten `check` sends `typeEq` to the record.
        markShared =
          other:
          builtins.isAttrs other
          && other ? __mint
          && builtins.isAttrs other.__mint
          && other.__mint ? minted
          && other.__mint.minted == digest;
        same =
          other:
          builtins.isAttrs other
          && other ? __mint
          && builtins.isAttrs other.__mint
          && other.__mint ? minted
          && other.__mint.minted == digest
          && (
            ((base.__sealed or { }) == { } && (other.__sealed or { }) == { })
            || (
              let
                r = builtins.tryEval (checkedTypes.typeEq base other);
              in
              r.success && r.value
            )
          );
        rel =
          self: other:
          if digest == null then
            refuseParametricMerge base other
          else if same other then
            { merged = self; }
          else if markShared other then
            refuseSharedMark base other (builtins.tryEval (checkedTypes.typeEq base other)).success
          else
            let
              # ★ THE READ IS TOTAL. The vocabulary's `payloadOf` refuses by `throw` whatever it cannot
              # certify (a sealed, foreign or `//`-derived partner), and that refusal is caught here
              # and becomes `null`, so the pair falls to this library's own named refusal rather than
              # surfacing the reader's. A vocabulary publishing no `payloadOf` reads `null` too.
              read =
                t:
                let
                  r = builtins.tryEval (
                    if checkedTypes ? payloadOf then
                      let
                        p = checkedTypes.payloadOf t;
                      in
                      builtins.deepSeq p (if builtins.isAttrs p && p ? ctor && p ? args then p else null)
                    else
                      null
                  );
                in
                if r.success then r.value else null;
              pa = read base;
              pb = read other;
              elemsOf =
                p: if builtins.isAttrs p.args && builtins.isList (p.args.elems or null) then p.args.elems else null;
            in
            # ★ THE ENUM-UNION LAW (owner ruling on den-hoag-parametric-merge-unlock-6wb87, nixpkgs
            # parity): two `enum`s under ONE name merge to the enum of their ordered union, left operand
            # first, first occurrence kept — nixpkgs' `enum` functor's `binOp`, `unique (a ++ b)`. Two
            # names still refuse, as the foreign protocol's functor-name clause already does. The union
            # is rebuilt through the vocabulary's own completed `enum`, so it mints, carries its own
            # certified payload and merges again. Every other pair keeps the refusal.
            if
              pa != null
              && pb != null
              && pa.ctor == "enum"
              && pb.ctor == "enum"
              && builtins.isString (pa.args.name or null)
              && (pa.args.name or null) == (pb.args.name or null)
              && elemsOf pa != null
              && elemsOf pb != null
              && checkedTypes ? enum
            then
              {
                merged = completeParametric checkedTypes.enum pa.args.name (
                  prelude.unique (elemsOf pa ++ elemsOf pb)
                );
              }
            else
              refuseUnreconciledMint base other pa pb;
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

  # The module-classification key lists `configOf`/`moduleSyntaxChecked` (lib/modules.nix) enforce,
  # published as plain data so a consumer's structured/shorthand guard reads the rule this engine
  # enforces instead of restating it (den-hoag-4kh.53.55; ADR-0014 — a list of strings crosses, never
  # a predicate; den-hoag-1n12c). No alias to nixpkgs' `lib.modules` `unifyModuleSyntax` locals: this
  # is a source comment, not a name equivalence. `structured` corresponds to its `attrsToRemove`,
  # `shorthandMeta` to its `shorthandAttrsToRemove` (plus this engine's `_module`/`__pureModule`/`__reservedKeys`/`__keyEq` on
  # both, and `structuring` to the `config`/`options` test that chooses between them — nixpkgs has no
  # published list for that arm).
  moduleSyntax = {
    structuring = core.structuringKeys;
    structured = core.structuredKeys;
    shorthandMeta = core.shorthandMetaKeys;
  };

  # The comparison subject of a value that can carry a type record, for a relation outside this
  # library deciding "one construction" over one (gen-schema's `constructionRelation`) — the same
  # subject `mkOptionType`'s own relation decides by (lib/interface.nix, den-hoag-bfc0k).
  inherit (core.interface) closuresFirst;

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
    mergeTypes
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
  # merge semantics move on that axis. The caller it exists for is gen-aspects' freeform primitive
  # arm. Inside this library one route reaches it: `mkOptionType`'s default for a descriptor stating
  # `name` and no fold (`mergeDescriptorDefault`, lib/modules.nix), which is nixpkgs' CONSTRUCTOR
  # default (`merge ? mergeDefaultOption`), not a leaf default, and keeps a named refusal at the two
  # arms where nixpkgs' answer is silent (owner parity criterion, 2026-09-25). A descriptor stating
  # `verify` is a gen leaf and keeps `mergeLeaf`.
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
  # ★ PARITY IS VERIFIED AGAINST THE LIVE nixpkgs, WHICH IS WHY NO REV IS STAMPED HERE. This
  # library's `lib/` is nixpkgs-free (ci/tests/purity.nix), so the law and the pass are an
  # INDEPENDENT REIMPLEMENTATION rather than a wrapper — and what watches upstream is
  # ci/tests/parity-surface.nix's `bothLaws`, whose `nixpkgs` arm calls `np.mergeDefaultOption` at
  # whatever rev `ci/flake.lock` resolves. Every parity cell there asserts BOTH sides against
  # literal expected values, so an upstream change to the merge law reds them ON THE PROPERTY.
  #
  # ★★ A STAMPED REV USED TO SIT HERE, read back out of this file by that suite and compared against
  # the lock both directions. It was retired by owner ruling 2026-09-22 — *"the parity contract
  # should move with upstream, remove the hardcode"* — because it watched LOCK MOVEMENT rather than
  # the law: a routine bump redded it with both laws byte-unchanged and blocked a whole roster
  # relock. What is given up is lock-movement notification, and nothing else. Do not re-stamp; the
  # retirement note at the foot of parity-surface.nix carries the reasoning.
  inherit (core) mergeDefaultOption;
  inherit (priority)
    mkOrder
    mkBefore
    mkAfter
    ;

  # The band each contributor's own evaluation resolved a leaf at, and per leaf the record it moves
  # or the reason it moves nothing (den-hoag-zakjg U1; `lib/priority.nix`). gen-view's
  # `headPositions` places the moved records and `joinedTrace` joins them back.
  inherit (priority) priorityBand bandedLeaves;

  # Structural strategies (spec §2/§4) also surfaced at the top level.
  inherit (strategies)
    mkOption
    mkOptionType
    deriveType
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
  #
  # ★ THE ALLOWLIST IS THIS LIBRARY'S DECLARATION, SO ITS STALENESS IS JUDGED AGAINST THIS LIBRARY'S
  # EXPORTS (`linkset.nix`, `stale`), never against the supplied vocabulary. An entry naming a name
  # the vocabulary lacks is INAPPLICABLE — no overlap there, nothing decided, nothing shadowed — which
  # is `scopeDefect`'s rule: the caller is judged only on names this library demands. Whether the
  # SHIPPED roster still collides at each entry is a fact about the pair, checked where the roster is
  # pinned (ci/tests/linkset.nix, `rosterMissing`). The left label is neutral because this library
  # cannot know which vocabulary it was handed.
  types =
    (linkset.mergeExports {
      left = {
        library = "the supplied `types` vocabulary";
        exports = builtins.mapAttrs (_: completeExport) checkedTypes;
      };
      right = {
        library = "gen-merge";
        exports = strategies;
      };
      allow = import ./types-allowlist.nix;
    }).exports;
}
