# Structural merge-strategy types (spec §2 + §4).
#
# These are the MERGE half — the types that own how their defs combine. Each carries a `.mergeDefs
# loc defs`. Leaf CHECKING types (str/int/bool/enum/path/…) come from gen-types (injected), NOT here
# — gen-merge answers "how do defs combine?", gen-types answers "is v well-typed?" (spec §4). `raw`
# and `anything` live here because they are defined by their MERGE behavior (one-def / recursive),
# not by a value predicate.
#
# ★★★ THE VOCABULARY UTTERS NO FOREIGN CONSTANT. What a type says about itself it says in gen's own
# words — `verify`/`admits` for its domain, `mergeDefs` for its fold, `typeMergeRel` for whether two
# of them merge, `carries`/`recarry` for what it wraps, `substructure` for what it declares,
# `whenEmpty` for what it is worth when nobody defined it. The nixpkgs `optionType` protocol — its
# fourteen field names, its payload spellings, its `option-type` tag — lives in ONE unit,
# `lib/interface.nix`, and a type acquires it only by being exported through that boundary. A foreign
# name appearing in this file is the boundary leaking, and `ci/tests/interface.nix` is what says so.
{
  prelude,
  core,
  # The leaf vocabulary (gen-types), for its exported identity half (`mkIdentity`). A vocabulary
  # publishing none leaves every composite here unminted.
  types,
}:
let
  inherit (prelude)
    isList
    isAttrs
    concatMap
    concatLists
    concatStringsSep
    map
    attrNames
    elemAt
    listToAttrs
    foldl'
    optional
    filter
    head
    tail
    length
    all
    imap0
    ;
  inherit (core)
    evalModuleTreeNested
    namePlaceholder
    calledNestingRefusal
    mergeDefs
    mergeDefsThreaded
    mergeLeaf
    slotsDiffer
    isDefinedValue
    isDefinedBy
    showOption
    setDefaultModuleLocation
    defsAsModules
    isPathString
    isModuleValue
    refusingOutside
    interface
    ;

  # mkOption — a plain descriptor; evalModuleTree reads .type/.default/.apply/.readOnly. Identity
  # (tagged) so the gen-aspects/gen-schema re-host is a `lib.mkOption` → `mkOption` rename.
  mkOption = descriptor: descriptor // { _type = "option"; };

  # ── the gen-native type constructor ─────────────────────────────────────────────────────────────
  # A gen type IS its record. `mkType` adds the one thing every type owes and most do not state — a
  # TYPE-MERGE RELATION — and enforces the one thing a wrapping type may not inherit.
  #
  # THE DEFAULT RELATION IS THE NULLARY ONE: a type with no parameters merges with a same-named
  # partner and refuses everything else. That is right for a type that takes no parameters and WRONG
  # for one that does — two `attrsOf` over different element types would report "mergeable" and
  # silently keep the first — so every parameterised constructor below states its own.
  #
  # ── the sub-protocol is a REQUIRED FORMAL of a wrapping type, not a default ─────────────────────
  # A leaf's answers are that it declares nothing, has NO module-set concept (which is what `null`
  # says, and the only thing it says — a module set that exists and is empty reports `[ ]`), and has
  # nothing to rebuild. They are wrong for every type that wraps another, and a wrapping type left on
  # them reports "declares nothing" indistinguishably from a type that genuinely declares nothing — a
  # consumer reflecting a declared surface off it then fails CLOSED and silently. A default cannot be
  # right for both, so a type that CARRIES something answers all three itself or is refused here, by
  # name. The missing declaration is the design choice; making the field required makes it total.
  #
  # THE DOMAIN IS WHAT THE TYPE CARRIES — a property of the constructor, read off the record, not of
  # any measurement. Two ways a record says it carries something: a `carries` role (an element type,
  # a union's members, a module set) or a substructure that names a module set. Everything else is
  # outside BY THE DOMAIN rather than by a carve-out:
  #   · a leaf carries neither;
  #   · `either`/`oneOf` carry MEMBERS, and they introduce no path level, so `{ }` is their correct
  #     `declares` answer — which they state, rather than inherit;
  #   · `deferredModule` carries a module set, and that set is EMPTY. gen-merge ships no
  #     `deferredModuleWith`/`staticModules`, so it is empty BY CONSTRUCTION rather than by
  #     omission — a fact to report (`[ ]`), not an absence (`null`). It is therefore IN this domain
  #     by the module-set arm and answers all three itself, below.
  #
  # `||` short-circuits, and the order is load-bearing: a container's module set IS its element's, so
  # reading it to decide the domain would force the element type at construction. A `carries` role is
  # settled before that read happens.
  subFormals = [
    "declares"
    "modules"
    "rebuild"
  ];

  # A partner's name, for a refusal — `interface.nameOf`, the one reader every refusal in this library
  # names an operand through, so it is total over anything that can arrive as a merge operand.
  #
  # ★ A REFUSAL'S REASON IS A NOUN PHRASE NAMING THE PAIR, never a sentence repeating the verdict.
  # The relation's reason is read back at the declaration site, which has already said "declared with
  # types that do not merge" before it opens the parenthesis; a reason that says so again produces
  # `types that do not merge (types do not merge: …)`. So every refusal below names the two operands
  # and, where there is one, the DISCRIMINATING FACT — which is the part the reader does not already
  # have from the sentence around it.
  inherit (interface) nameOf keyOf;
  # `self` is what this type's own default relation answers WITH — the value a caller actually holds.
  # It is threaded rather than closed over locally because a type built through `defineType` is used
  # in its EXPORTED form, and a relation answering with the un-exported twin would hand a consumer a
  # merged type its foreign engine cannot read. One knot, tied where the two forms are made.
  mkTypeWith =
    self: t:
    let
      name = t.name or "raw";
      declaresRole = t ? carries;
      carriesSomething = declaresRole || ((t.substructure or { }).modules or null) != null;
      missingSub = filter (f: !((t.substructure or { }) ? ${f})) subFormals;
      # ★ `recarry` IS OWED BY A TYPE THAT DECLARES A ROLE, and it is the last carried-role formal that
      # was left un-total. The boundary reads it to rebuild this type over another payload wherever it
      # DERIVES the relation, so a carrying record without one that is not answered for otherwise
      # constructs, exports, and then detonates with a bare missing-attribute error the moment a
      # foreign engine applies the functor — an interpreter error naming neither the type nor the
      # field, which is the exact shape making every other formal here required was meant to remove.
      #
      # SCOPED TO THE ROLE, not to carrying in general: `deferredModule` carries a module set through
      # its substructure without declaring a role, so it has no payload to be rebuilt over and owes
      # none. The domain is what the record SAYS it carries, as everywhere else in this check.
      #
      # AND SCOPED TO A REBUILD THIS BOUNDARY ACTUALLY PERFORMS. `recarry' is owed because the export
      # half rebuilds the type over another payload to derive a relation for it. A record that came
      # in STATING its own relation is answered by that instead and is never rebuilt that way, so it
      # owes nothing. `retainedRelation' is gen's own word for that fact and its PRESENCE is the
      # whole question — this file asks what the record says about itself in this library's
      # vocabulary, and the shape of what was retained stays behind the boundary, where it belongs.
      missingRecarry =
        if declaresRole && !(t ? recarry) && !(t ? retainedRelation) then [ "recarry" ] else [ ];
      missing = missingSub ++ missingRecarry;
      # THE LEAF RELATION. A gen partner is asked first and with no binding (the embedding is a fact
      # about a FOREIGN partner, and a gen x gen redeclaration, the fan-in of one loc, pays nothing for
      # it): the same key answers `self`. A RAW foreign partner is joined in its own published functor,
      # so the declared type is the partner's record in both orders:
      #  - keyed under an embedding with parameters (`path`, `pathLike`; `interface.embeddings`): in
      #    the partner's relation over the embedding (`interface.joinCarriedInStatedRelation`);
      #  - keyed under an embedding with none (`string`): as a leaf at the embedding's name;
      #  - of the same key (as `elementRel`'s carve-out): as a leaf, and a declined join answers `self`,
      #    EXCEPT for a partner stating a payload (`interface.statesPayload`), which is refused AS THE
      #    DECIDER only (`vetoes = false`, read by `lib/modules.nix` `declaredPair`): nixpkgs' default
      #    relation, which the twin states, asserts two leaves agree on a payload, so the twin refuses it
      #    where the twin decides; where the partner decides, its OWN relation answers, as nixpkgs lets
      #    it. `self` would drop the partner's check unsaid (ADR-0025 item 1). The other declines (a
      #    functor with no `type` or no `binOp`, a join that renames) keep `self`: nixpkgs' twin serves
      #    those pairs where it decides without aborting, and a refusal there would regress a serve
      #    (ADR-0039's serve half).
      # A declined embedding join is REFUSED, never `self`: the partner's own check would be dropped
      # unsaid (ADR-0025 item 1), so the table cannot widen the same-key fallback's reach.
      nullaryRel =
        other:
        if isAttrs other && other ? typeMergeRel then
          if (keyOf other) == name then
            { merged = self; }
          else
            { refused = "`${nameOf t}' and `${nameOf other}'"; }
        else
          let
            e = interface.embeddingOf name;
            embedKey = isAttrs other && interface.keyedUnderEmbedding name other;
            sameKey = isAttrs other && (keyOf other) == name;
            carriedJoin = interface.joinCarriedInStatedRelation {
              inherit name self;
              role = null;
              carried = null;
            } other;
            leafJoin = interface.joinLeafInStatedRelation { inherit name self; } other;
            # a join with a raw foreign partner: the step meets it (`lib/modules.nix` `mergeTypesBy`)
            meet = j: {
              merged = j;
              meets = true;
            };
            ownJoin = interface.joinInPartnerRelation self other;
          in
          if embedKey && e ? params then
            if carriedJoin != null then
              meet carriedJoin
            else
              { refused = "`${nameOf t}' and a `${e.name}' partner whose payload is not this type's embedding"; }
          else if embedKey && !sameKey then
            if leafJoin != null then
              meet leafJoin
            else
              { refused = "`${nameOf t}' and a `${e.name}' partner whose relation declines the join"; }
          else if sameKey && interface.statesPayload other && ownJoin != null then
            meet ownJoin // { twinRefuses = true; }
          else if sameKey && interface.statesPayload other then
            {
              refused = "`${nameOf t}' and a `${name}' partner stating a payload, which a leaf does not";
              vetoes = false;
            }
          else if sameKey then
            meet (if leafJoin == null then self else leafJoin)
          else
            { refused = "`${nameOf t}' and `${nameOf other}'"; };
    in
    if carriesSomething && missing != [ ] then
      throw (
        "gen-merge: the structural type `${nameOf t}' carries a parameter but does not supply "
        + concatStringsSep ", " (map (f: "`${f}'") missing)
        + "; a type that carries something answers for it rather than inheriting a leaf's answers"
      )
    else
      t // { typeMergeRel = t.typeMergeRel or nullaryRel; };

  # The gen record alone, answering with itself. This is the substrate vocabulary with nothing of the
  # foreign protocol on it, and it is what the boundary is handed.
  mkType =
    t:
    let
      self = mkTypeWith self t;
    in
    self;

  # defineType — the gen record AND its expression in the foreign protocol, as one value.
  #
  # ★ THIS IS THE CROSSING SITE, AND THERE IS ONE OF IT. Every type this library constructs is built
  # here, so "which values carry the foreign protocol, and where did they acquire it" has a
  # one-line answer instead of a survey. THAT THE SAME VALUE CARRIES BOTH IS FORCED, not convenient:
  # the published `types` namespace is the drop-in a foreign module system mounts, and the type a
  # consumer writes there is handed to this library's own fold as readily as to a foreign one. What
  # the boundary buys is not that the two vocabularies live in different values — it is that only ONE
  # unit knows how to get from the first to the second, and that everything above states itself in
  # the first alone.
  defineType =
    t:
    let
      exported = interface.exportType (mkTypeWith exported (core.readsMintedNode exported t));
    in
    exported;

  # ── A COMPOSITE'S IDENTITY (den-hoag-6orb8 U2) ──────────────────────────────────────────────────
  # `identified ctor members mkArgs sealed t` is the source record `t` carrying the identity fields
  # built by the leaf vocabulary's exported identity half (gen-types `mkIdentity`, ADR-0034's
  # per-component clause): a mark over the constructor and one tag per component, and `__sealed`
  # beside it. So a composite is minted whatever its components' regimes, and two constructions of
  # one composite over one component are one type, directly and after transport through `anything`
  # (which carries a `__mint` carrier whole). The constructor is spelled in THIS library's namespace,
  # `gen-merge.<name>`: gen-types' own `listOf`/`attrsOf` mint over the same argument shape, and they
  # fold differently (a concatenation here, the leaf fold there), so one spelling would decide two
  # types one. The fields are lazy, so a declaration that is never compared mints nothing.
  #
  # ★ EACH FIELD IS A SELECTION, NEVER `t // ids`. A `//` forces the identity half's own record, and
  # every binding of its `let` with it, at every construction; a selection leaves it unentered until a
  # field is read. Measured on the hub bench's `aspects` workload (2805 constructions, no mint
  # forced): `t // ids` cost about 22 thunks per construction, the selections about 10.
  #
  # `__typeSelf` is the completion stamp's slot: the export ties it to the record it completes (gen-types
  # `completedType`, `lib/interface.nix` `exportType`), so a `//` copy of a composite is refused at
  # `typeEq` as a copy of a leaf is.
  #
  # ★ IDENTITY AND VALUE ARE TWO QUESTIONS. These fields answer the first: one submodule binding
  # declared twice IS one type (`typeEq` `true`). A redeclaration's VALUE is the second, and it stays
  # the constructor's own relation, never "same type, so merge to the partner": a submodule's relation
  # unions the two module sets, which is not idempotent, so one binding declared twice evaluates its
  # module set twice, as nixpkgs `lib.evalModules` does (a doubled list option reads `[ 1 1 ]` there
  # and here). Merging to the partner served `[ 1 ]`, a value nixpkgs never produces (ADR-0039).
  identified =
    ctor: members: mkArgs: sealed: t:
    if types ? mkIdentity then
      let
        ids = types.mkIdentity "gen-merge.${ctor}" members mkArgs sealed (t.name or ctor);
      in
      t
      // {
        __mint = ids.__mint;
        __payload = ids.__payload;
        __sealed = ids.__sealed;
        ${if members == [ ] then null else "__okAt"} = ids.__okAt;
        __typeSelf = null;
      }
    else
      t;

  # mkOptionType — the (loc,defs) custom-merge escape hatch (spec §1 item 6). Its descriptor is
  # written in the FOREIGN protocol's words (`check`, `merge`, `emptyValue`, …) because that is what
  # a nixpkgs `mkOptionType` drop-in means, so it is exactly a round trip through the boundary: the
  # descriptor comes IN through the import environment, acquires the relation every gen type owes,
  # and goes back OUT through the export environment. Consumers write
  # `mkOptionType { name = "aspect"; merge = loc: defs: …; }` and get a type that both gen-merge
  # (dispatches on `.mergeDefs`) and nixpkgs (reads the full protocol) accept. A descriptor stating
  # no fold gets the constructor's default, as nixpkgs' does (`importDescriptor`). A descriptor
  # stating no relation gets `sealedRel` below: one construction redeclared merges, two
  # constructions of one name are refused, and the name alone never decides it.
  mkOptionType =
    descriptor:
    let
      answer = interface.importDescriptor descriptor;
      imported = answer.imported;
      # A descriptor stating no relation gets this one (den-hoag-bfc0k). Its `check` is a caller's
      # function, so it is SEALED (ADR-0034): the name alone cannot say two of them are one type, and
      # merging on it let the later declaration win with its own check. A same-named partner merges
      # only when it is this construction — decided by the reified value under Nix `==`, over
      # `closuresFirst`'s subject so the comparison terminates on two constructions — and every other
      # one is refused by name. A `//` derivation of a built record is a different value, and refuses.
      sealedRel =
        self: other:
        if !(isAttrs other) || (keyOf other) != keyOf imported then
          { refused = "`${nameOf imported}' and `${nameOf other}'"; }
        else if interface.closuresFirst [ other ] other == interface.closuresFirst [ self ] self then
          { merged = self; }
        else
          {
            refused = "`${nameOf imported}' and `${nameOf other}', two separately constructed `mkOptionType' types of one name whose checks are caller-supplied functions and cannot be compared";
          };
      exported = defineType (
        imported // { typeMergeRel = imported.typeMergeRel or (sealedRel exported); }
      );
    in
    if answer ? refused then
      throw answer.refused
    # A stock foreign container crosses as gen's own, already built (den-hoag-n6dh7 item 5).
    else if answer ? rehomed then
      answer.rehomed
    else
      exported;

  # deriveType — a type DERIVED from a completed one: the base's behaviour, a delta of metadata, and an
  # identity of its own (den-hoag-5kic).
  #
  #   deriveType base {
  #     id = "<string>";        # REQUIRED: the derivation's merge identity, and its functor name
  #     key = <plain data>;     # default null: content two derivations of one `id' must agree on, `=='
  #     fields = b: { … };      # default `_: { }': metadata, as a function of the base it is applied to
  #     name = "<string>";      # default the base's: the value vocabulary its messages speak
  #     description = "<string>";
  #     mint = { minted = …; }; # default per component: an identity the CALLER minted
  #   }
  #
  # ★★ WHY `base // Δ` IS NOT A DERIVATION. A completed type is a FIXPOINT: `defineType` ties the knot
  # once, and every answer that refers back to the type — its relation, `typeMerge`, `functor.type` —
  # is closed over that knot, while every answer that rebuilds it (`recarry`, `substructure.rebuild`,
  # `withArgs`) is closed over its constructor. `//` changes the record and leaves each of them
  # answering for the base: the derivation merges with itself to its base, rebuilds to its base, and
  # mints as its base, while its check and fold stay right, so nothing a value reaches says so. This
  # is the delta applied AFTER the fixpoint. Bracha & Cook 1990 §2.1 ("incremental derivation", the
  # inheritance operator `C = Δ(P) ⊕ P') gives the delta parametric in the parent, which is why
  # `fields` takes the base; that `self` is then re-bound is Cook 1989's account, which that paper
  # defers to and which is cited, not read — the ground here is this file's own knot (`mkTypeWith`'s
  # `self`) and the cells measuring it. So the derivation is built as `mkOptionType` and every
  # parametric leaf build theirs: a SOURCE record overridden first, then completed through
  # `defineType`. No protocol field is written here; the export derives all of them again.
  #
  # The source is the base with `interface.deriveClasses`' derived, tied, identity and datum fields
  # cut; its behaviour crosses unread. A base that is not gen's own record (a foreign type, or a gen
  # one whose `check` a wrapper rewrote) is read through the import boundary first, as `mkOptionType`
  # reads one. The tied fields are stated again, each the base's answer lifted through the derivation
  # (`recarry c' is the derivation over `base.recarry c', a natural map):
  #   · the RELATION merges only a derivation of the same `id' and `key', and answers the base pair's
  #     own join, re-derived. It asks `mergeTypes' — the one dispatch, so a foreign base merges through
  #     the boundary's arm — and never answers with this declaration's own value. Metadata is
  #     left-biased: `key' is the whole of what separates two derivations of one `id'.
  #   · IDENTITY is never the base's (ADR-0034). With no `mint' it is minted PER COMPONENT through the
  #     injected leaf vocabulary's identity half (`identified', den-hoag-6orb8 U2.3): the `id' and the
  #     `key' inert, the base by its mark, or sealed where it carries none or a wrapper rewrote its
  #     `check'. So a derivation is the same type everywhere whenever its arguments are, and gen-merge
  #     still mints nothing itself — the one minting authority is gen-identity, behind gen-types. A
  #     caller that minted one passes it and keeps that meaning: it owes a preimage covering the `id',
  #     the `key' and the base's identity, and one omitting the `key' mints two derivations as one.
  #
  # ★ ITS COST IS ONE COMPLETION PER LIFT: a merge, a `recarry' or a rebuild of a derivation
  # re-completes it through `defineType', so a fold over N derivation levels pays N completions and
  # N relation frames, the price gen-schema's `refined' pays for its own lifted relation today.
  #
  # ★ THE PUBLISHED DOOR IS OPTIONS FIRST, then the `id`, then the base (den-hoag-7gp66 P2, R7):
  # `deriveType { key = …; } "tagged" str`. The options are closed and refused by name at
  # `deriveType opts`; `id` is required, so it is a positional operand, configuration before the
  # base the derivation is taken from. A lift re-derives through the core with the spec it holds.
  deriveTypeOptions = [
    "key"
    "fields"
    "mint"
    "name"
    "description"
  ];
  deriveType =
    prelude.door
      {
        name = "gen-merge.deriveType";
        optional = deriveTypeOptions;
      }
      (
        o: id: base:
        deriveTypeCore base (o // { inherit id; })
      );
  deriveTypeCore =
    base: spec:
    let
      classes = interface.deriveClasses;
      id = spec.id or null;
      key = spec.key or null;
      fields = spec.fields or (_: { });
      gen =
        if base ? typeMergeRel && !(interface.rewritesCheck base) then
          base
        else
          let
            answer = interface.importType base;
          in
          if answer ? refused then throw answer.refused else answer.imported;
      delta = fields gen;
      # Cut from the source: everything but its behaviour. A delta may restate only the name-carried.
      cut = classes.derived ++ classes.tied ++ classes.identity ++ classes.datum;
      fixed = filter (n: !(builtins.elem n interface.exportClasses.nameCarried)) cut ++ classes.behaviour;
      notMetadata = filter (n: builtins.elem n fixed) (attrNames delta);
      holdsType =
        v:
        if isAttrs v then
          interface.isOptionType v || v ? typeMergeRel || builtins.any holdsType (builtins.attrValues v)
        else
          isList v && builtins.any holdsType v;
      defect =
        if !(interface.isOptionType base) then
          if interface.typeDefect base != null then
            interface.typeDefect base
          else
            "has not been completed (it states no foreign protocol; build it through `defineType' first)"
        else
          interface.typeDefect base;
      named = "`deriveType' over `${nameOf base}'";
      lift = b: deriveTypeCore b spec;
      relation =
        other:
        let
          theirs = other.__derivation;
          partner =
            if isAttrs other && other ? __derivation then
              "the derivation `${theirs.id}' of `${nameOf theirs.base}'"
            else
              "`${nameOf other}'";
          pair = "the derivation `${id}' of `${nameOf base}' and ${partner}";
        in
        if !(isAttrs other) || keyOf other != "derivation:${id}" then
          { refused = pair; }
        else if theirs.key != key then
          { refused = "${pair}, whose keys differ"; }
        else
          let
            joined = core.mergeTypesWithin base theirs.base;
            cause = core.mergeTypesReasonWithin base theirs.base;
          in
          if joined == null then
            { refused = "${pair}, whose bases do not merge${if cause == null then "" else ": ${cause}"}"; }
          else
            { merged = lift joined; };
      sealed = {
        unmintable = {
          ctor = id;
          reason = "the derivation `${id}' of `${nameOf base}' states no minted identity (pass `mint' to `deriveType')";
        };
      };
      # A caller's mint keeps its meaning; with none the derivation is identified per component.
      # `__sealed` is TOTAL on both arms: a caller's mint claims an identity over the whole
      # derivation, so it states no sealed component, and gen-types' `idOf` reads it directly.
      callerMint = spec ? mint || !(types ? mkIdentity && types ? typeEq);
      mint = spec.mint or sealed;
      identify =
        if callerMint then
          r:
          r
          // {
            __mint = mint;
            __sealed = { };
          }
        else
          identified "deriveType" [ base ] (tags: {
            inherit id key;
            base = head tags;
          }) [ ];
      sub = gen.substructure or null;
    in
    if defect != null then
      throw "gen-merge: ${named}: the base ${defect}"
    else if !(builtins.isString id) then
      throw "gen-merge: ${named} states no string `id'; a derivation's merge identity is the string it names"
    else if notMetadata != [ ] then
      throw "gen-merge: ${named} as `${id}': `fields' sets ${
        concatStringsSep ", " (map (n: "`${n}'") notMetadata)
      }, which ${
        if length notMetadata == 1 then "is" else "are"
      } not metadata; a type whose behaviour or relation differs is a new type (`mkOptionType'), not a derivation"
    else if holdsType key then
      throw "gen-merge: ${named} as `${id}': its `key' holds an option type, which Nix `==' cannot compare totally; key a derivation by plain data"
    else
      defineType (
        identify (
          builtins.removeAttrs gen cut
          // delta
          // {
            name = spec.name or delta.name or gen.name or "raw";
            # The base AS PASSED: the join asks it, and a foreign one answers through the boundary's arm.
            # The base AS READ (`read`): the phrase renders it, so a foreign base is described as the
            # import boundary reads it, within the budget, and never by its own `description`.
            __derivation = {
              inherit base id key;
              # null when this derivation states its phrase. A base derivation stating none is read
              # through to what IT reads, so a chain of them costs the renderer one unit, not one per
              # layer, and keeps its base's phrase however deep it is.
              read =
                if spec ? description || delta ? description then
                  null
                else if gen ? __derivation && (gen.__derivation.read or null) != null then
                  gen.__derivation.read
                else
                  gen;
            };
            typeMergeRel = relation;
          }
          // (
            let
              base' = if gen ? description then interface.carriedPhrase gen else { };
            in
            if spec ? description then
              base' // { inherit (spec) description; }
            else if delta ? description then
              builtins.removeAttrs base' [ "description" ]
            # Nothing stated: the export renders the base's phrase through `__derivation` within its
            # budget. Stating the base's `description` here closes a cycle through the derivation on
            # its own value (`d = deriveType (nullOr (oneOf [ str (listOf d) ])) …`).
            else
              { }
          )
          // (if gen ? recarry then { recarry = c: lift (gen.recarry c); } else { })
          // (if gen ? withArgs then { withArgs = a: lift (gen.withArgs a); } else { })
          // (
            if sub == null then
              { }
            else
              {
                substructure = sub // {
                  rebuild =
                    m:
                    let
                      r = sub.rebuild m;
                    in
                    if r == null then null else lift r;
                };
              }
          )
        )
      );

  # Merge two ELEMENT types — the element stratum's name for `core.mergeTypes` (lib/modules.nix),
  # which is guarded on both halves and stated there. It is the SAME binding the DECLARATION stratum
  # consults when one option is declared twice, which is what makes "these two types do not merge"
  # one answer in this library rather than two that can drift apart. It is that binding's DESCENT
  # (`mergeTypesWithin`): a relation is entered past the pre-flight, which walked every element pair
  # it can meet (`lib/modules.nix` `relationMerge`), so it is not asked again at each level.
  mergeElemTypes = core.mergeTypesWithin;

  # A CONTAINER'S RELATION, shared by every type parameterised by one element. Two containers merge
  # iff their elements merge, and the result is this container rebuilt over the merged element.
  #
  # ★ ROW-FREE, AND THAT IS WHAT MAKES IT GEN'S OWN. The partner arrives as a TYPE, not as a functor
  # payload both sides must agree on the shape of, so a partner that spells its parameter some other
  # way is still a legible operand — its element is read through the boundary's import environment,
  # which is the one place that knows any spelling but this one.
  #
  # ★ ONE CARVE-OUT, against a RAW FOREIGN partner that states a relation and whose payload is just
  # the element, or is the payload of the richer constructor this container embeds in (`attrsOf` in
  # `attrsWith`, `interface.embeddings`): the partner's own relation decides the pair
  # (`interface.joinCarriedInStatedRelation`), so the merged type is that partner's record and not a
  # gen one, whichever declaration came first. Every other pair is row-free as above. The test for a
  # gen partner sits here, not in the binding, so a gen × gen pair builds nothing for it.
  elementRel =
    name: rebuild: element: other:
    if !(isAttrs other) || (keyOf other) != name then
      { refused = "`${name}' and `${nameOf other}'"; }
    else
      let
        partnerElem = interface.importedOffered "element" other;
        # the partner's stated element (its own payload, or under the construction this one embeds in)
        stated =
          if partnerElem != null then partnerElem else interface.embeddedOffered name "element" other;
        # THE MEET: the element pair through the meeting merge. Where it meets, the partner's relation is
        # asked only about the PARAMETERS (its own element against itself), never a gen element as the decider
        metFirst = if other ? carries || stated == null then null else mergeElemTypes element stated;
        joinOver = if metFirst != null then stated else element;
        # a partner whose payload is its element alone states no parameters to agree on: it is rebuilt
        # over the met element by its own constructor, and its relation is not asked
        foreignJoin =
          if other ? carries then
            null
          else if metFirst != null && partnerElem != null then
            interface.rebuiltOverAt "element" metFirst other
          else
            interface.joinCarriedInStatedRelation {
              inherit name;
              role = "element";
              carried = joinOver;
              self = rebuild joinOver;
            } other;
        # The element pair's own reason, where it states one, rides the refusal: the option is named
        # at the top, and the cause sits one level down.
        elementRefusal =
          partner:
          let
            cause = core.mergeTypesReasonWithin element partner;
          in
          {
            refused = "`${name}' over `${nameOf element}' and `${name}' over `${nameOf partner}', whose element types do not merge${
              if cause == null then "" else ": ${cause}"
            }";
            # the element pair's refusal decides without vetoing (`nullaryRel`), so the container's does too
            vetoes = !(element ? typeMergeRel) || ((element.typeMergeRel partner).vetoes or true);
          };
      in
      if foreignJoin != null then
        let
          # the met element, or the join's own element met with both
          metElem =
            if stated == null then
              null
            else
              let
                joined = interface.carriedAt "element" foreignJoin;
              in
              if metFirst != null then
                metFirst
              else if joined != null then
                interface.meetOf joined [
                  element
                  stated
                ]
              else
                null;
          over = interface.rebuiltOverAt "element" metElem foreignJoin;
        in
        # THE MEET: the container is the partner's constructor over the met element
        if metElem == null then
          {
            merged = foreignJoin;
            meets = true;
          }
        else
          {
            merged = if over != null then over else rebuild metElem;
            meets = true;
            twinRefuses = element ? typeMergeRel && ((element.typeMergeRel stated).twinRefuses or false);
          }
      else if partnerElem == null then
        let
          # A partner stated under the construction this one embeds in DOES state its element, beside
          # parameters gen does not carry; its join refused above, so the refusal names that element.
          embeddedElem = interface.embeddedOffered name "element" other;
        in
        if embeddedElem == null then
          { refused = "`${name}' and a partner that states no element type of its own"; }
        else if mergeElemTypes element embeddedElem == null then
          elementRefusal embeddedElem
        else
          {
            refused = "`${name}' over `${nameOf element}' and a partner over `${nameOf embeddedElem}' whose own relation does not join this one's parameters";
          }
      else
        let
          merged = mergeElemTypes element partnerElem;
        in
        if merged == null then
          elementRefusal partnerElem
        else
          {
            merged = rebuild merged;
            # the element pair's join the twin refuses, carried up as `vetoes` is (read by a foreign engine's ask)
            twinRefuses = element ? typeMergeRel && ((element.typeMergeRel partnerElem).twinRefuses or false);
          };

  # An element's substructure, whichever vocabulary it speaks. A gen type answers from its own
  # record; a foreign one is read through the import environment; a bare parametric constructor (a
  # gen-types `enum`/`struct`/`union` reaching the namespace unapplied) is not a record at all and
  # gets a leaf's answers, which are the true ones for it.
  subOf = element: interface.importedSubstructure element;
  # Whether an element has a substructure of its own to substitute into — asked at the boundary,
  # because the answer depends on which vocabulary the element states it in.
  carriesSub = interface.importedRebuilds;

  # ── THE SPLIT: a container's element positions, stated ONCE (den-hoag-n6dh7 item 5) ────────────
  # `split : loc -> defs -> [ { step; loc; defs; type; } ]` — the per-element definitions the
  # container's fold computes, each with its POSITION segments (`step`: `[ k ]` for an attribute
  # container, `[ d i ]` for `listOf`, `[ ]` for `nullOr` and `either`), the `loc` its element is
  # folded at, and the element type. The container's own value fold reads it, and so does the
  # nested-tree key walk, so the positions a walk keys and the positions a fold reads are one
  # binding's answer, never two copies that can drift. Each element folds through the engine's
  # CALLED fold, as every container's did before the split existed.
  foldElement = e: mergeDefs e.loc e.type e.defs;
  # The same element through the engine's THREADED twin (den-hoag-n6dh7 item 5): the evaluation's
  # accessor `ev` goes with it, its position extended by the element's `step`, so the tree a nesting
  # element reads is the one at that position. It is the called fold's call with `ev` added.
  threadElement =
    ev: e: mergeDefsThreaded (ev // { position = ev.position ++ e.step; }) e.loc e.type e.defs;
  # An EXACT container's element (`attrsOf`, `listOf`): marked with its own position, so a container
  # there that the key walk made a container node is read off it (`mergeDefsThreaded`). The mark
  # names one position, so a container below that adds a step clears it.
  threadExact =
    ev: e:
    let
      position = ev.position ++ e.step;
    in
    mergeDefsThreaded (
      ev
      // {
        inherit position;
        exactAt = position;
      }
    ) e.loc e.type e.defs;
  # The thread an exact container's elements take, decided ONCE, when the type is built: the mark
  # only where the element may fold as such a node (`interface.mayFoldNested`), so any other
  # element's fold allocates nothing for it.
  exactThread = element: if interface.mayFoldNested element then threadExact else threadElement;

  # The base module arguments a submodule's own evaluation WRITES OVER whatever a caller supplies.
  # `config`, `options` and `prefix` are injected by the engine itself at BOTH strata —
  # `lib/modules.nix` `declArgs` (declaration) and `baseArgs` (value) — and in both the caller's set is
  # on the LEFT of `//`, so the engine's key wins. The engine refuses those three keys itself at both
  # bindings; `withArgs` refuses them at the moment the caller states them, which is the earlier door.
  # `name` is not one: the engine states it as a `_module.args` definition (`positionArgsAt`),
  # which a caller's `name` outranks, as nixpkgs `submoduleWith`'s `specialArgs.name` does. It was
  # reserved here (den-hoag-jyiji) while `submodule` injected it over the caller's value; that arm is
  # superseded (den-hoag-fpxsd), since the caller's value is now the one used.
  # `ci/tests-error.nix` `engine-reserved-args` holds the two spellings to one answer per key.
  submoduleReservedArgs = {
    config = null;
    options = null;
    prefix = null;
  };

  # submodule — recurse into a nested evalModuleTree over the submodule module + all defs; binds the
  # per-key `name` (spec §1 item 3). One nested fixpoint per merge (spec §1 item 4).
  #
  # ★ THE CALLER'S BASE MODULE ARGS RIDE ON THE TYPE, NOT ON THE CONSTRUCTOR. `isModuleValue` admits
  # any attrset, so a constructor form — `submodule { modules = …; specialArgs = …; }` — is
  # indistinguishable from a config-shorthand module that happens to set `modules`, and the misread
  # is SILENT. The inlet is therefore a method on the built type, `(submodule mods).withArgs { … }`,
  # which no module value can be mistaken for. `evalModuleTree` already takes `specialArgs ? { }`, so
  # this EXPOSES a channel one level down rather than adding one.
  #
  # ★ THE ARGS ARE A PLAIN DESCRIPTOR ATTRIBUTE AND NOT A SECOND CARRIED ROLE, and that is forced:
  # `interface.roleOf` throws when `carries` names more than one role, because the foreign protocol
  # has exactly one payload slot. `exportType` ends `t // { … }` — a pass-through — so an ordinary
  # attribute crosses the boundary untouched and a gen partner's is readable from the relation.
  #
  # ★★ EVERY REBUILD RE-ENTERS `mkSubmodule`, WHICH IS WHY THERE IS ONE. Three expressions in this
  # record rebuild the type — `recarry`, `substructure.rebuild`, and the relation's union — and one
  # that re-entered the args-less published constructor would drop the caller's args silently.
  # `substructure.rebuild` is the one that looks like an edge case and is not: a foreign engine calls
  # `substSubModules` on EVERY option whose type has a module set (nixpkgs `fixupOptionType`),
  # including a single declaration, and gen's own containers delegate their rebuild to their
  # element's — so `attrsOf ((submodule mods).withArgs { … })` would lose the args without ever
  # crossing the boundary.
  mkSubmodule =
    args: modOrMods:
    let
      mods = if isList modOrMods then modOrMods else [ modOrMods ];
      # A submodule reads its definitions as nixpkgs `types.submodule` does: `mergeDefs` hands them
      # through `defsAsModules true` to a nested `evalModuleTree`, so an attrset def is CONFIG and a
      # function or path def is a MODULE, and the domain is `isModuleValue`'s and not "any value":
      # nixpkgs `submoduleWith`'s `isAttrs x || isFunction x || path.check x`, as at `deferredModule`.
      # Bound once: the fold's domain check below reads this same binding.
      admits = isModuleValue;
      # THE NESTED TREE, STATED AS DATA (den-hoag-n6dh7 item 1): the module set and arguments this
      # type's nested evaluation takes, so an evaluation can mint the tree as a node of its own
      # instead of calling it. Each field is today's call's, field for field: `mergeDefs` below
      # (`entry` is one definition read as `defsAsModules true` reads it), `whenEmpty` (`empty`), and the
      # `{ carried; inherited; }` pair the CALLED form evaluates in (`calledMode`): the public
      # `evalModuleTree`'s, `{ carried = true; inherited = false; }`.
      nests = {
        modules = mods;
        specialArgs = args;
        check = null;
        coreShortCircuit = false;
        entry = d: head (defsAsModules true [ d ]);
        empty = {
          prefix = [ ];
          specialArgs = args;
          check = null;
        };
        calledMode = {
          carried = true;
          inherited = false;
        };
      };
      # The CALLED fold refuses by name (den-hoag-n6dh7 item 1): the tree is a child of the one
      # evaluation that holds it, read through `threaded` below.
      called = loc: _: throw (calledNestingRefusal "submodule" "mergeDefs" loc);
      freeform =
        ((core.evalModuleTreeNested {
          modules = mods ++ [ namePlaceholder ];
          inherit (nests.empty) prefix specialArgs check;
        }).type.unroledNested
        ).freeformType or null;
    in
    defineType (
      # The module set is ONE sealed component, the list itself: its elements keep the caller's slots,
      # so one function module handed to two constructions compares equal on every evaluator. A slot
      # per module (`imap0`) is a fresh thunk per module, which upstream Nix and Determinate compare by
      # slot and Lix by the forced closure (den-hoag-1fo91).
      identified "submodule" [ ] (_: { specialArgs = args; })
        [
          {
            path = [ "modules" ];
            value = mods;
          }
        ]
        {
          name = "submodule";
          unroledNested = if freeform == null then { } else { freeformType = freeform; };
          shorthandOnlyDefinesConfig = true;
          # What a caller supplied through `withArgs`, stated in gen's own words. Empty for a submodule
          # nobody added to, which is what makes the union below total.
          specialArgs = args;
          # THE INLET. Refusal lives HERE — one place, where the caller states the key — rather than at
          # the eval sites, where the loss would already have happened and the name would be gone.
          withArgs =
            a:
            let
              reserved = filter (k: submoduleReservedArgs ? ${k}) (attrNames a);
            in
            if reserved != [ ] then
              throw (
                "gen-merge: `withArgs' cannot supply the base module argument"
                + (if length reserved == 1 then " " else "s ")
                + concatStringsSep ", " (map (k: "`${k}'") reserved)
                + "; a submodule's own evaluation injects over whatever a caller supplies there, so the "
                + "value would be discarded rather than used"
              )
            else
              mkSubmodule (args // a) mods;
          inherit admits nests;
          # With no surviving definition the value is the module set evaluated over NO definitions, as
          # nixpkgs `submoduleWith`'s `emptyValue.value = base.config`: `base` is evaluated at no prefix
          # with the documentation placeholder as `name` (`namePlaceholder`), so its defaults read as they
          # would there and an undefined sub-option refuses by name. That evaluation is the child with an
          # empty seed, read through the threaded fold; called, it refuses (den-hoag-n6dh7 item 1).
          whenEmpty.value = throw (calledNestingRefusal "submodule" "whenEmpty" null);
          # What this type is parameterised BY. A submodule carries a MODULE SET, which is why its
          # relation unions rather than merges: an option declared as a submodule in two modules ends up
          # declaring the union of what they declare. On a nullary relation the second declaration would
          # be discarded silently.
          carries.moduleSet = mods;
          recarry = c: mkSubmodule args c.moduleSet;
          typeMergeRel =
            other:
            if !(isAttrs other) || (keyOf other) != "submodule" then
              { refused = "`submodule' and `${nameOf other}'"; }
            # The one datum two `submodule' declarations must agree on beside the name: whether an
            # attribute-set definition is config (this one) or a module (the tree-as-a-type), nixpkgs'
            # `shorthandOnlyDefinesConfig'. The reason names it, since the names agree.
            else if (other.shorthandOnlyDefinesConfig or true) != true then
              {
                refused = "`submodule' reading an attribute-set definition as config, and a `submodule' reading every definition as a module";
              }
            else
              let
                partnerMods = interface.importedOffered "moduleSet" other;
                # A partner's base module args are read off the descriptor attribute directly, for the
                # reason stated above: it is an ordinary attribute and survives export.
                #
                # ★ SCOPED TO GEN'S OWN MERGE PATH — `lib/modules.nix`'s `mergeTypes`, which is what the
                # declaration stratum consults when one option is declared twice. A FOREIGN engine merges
                # two declarations through `functor.binOp` (`lib/interface.nix:665-675`) instead, and
                # that arm recarries BOTH operands off the LEFT type, so it compares this type's args
                # with themselves: no conflict can be seen there and the left declaration's args win
                # silently. That path is not reachable with a gen partner anyway — `importedCarried`
                # requires a payload stating the module set ALONE, and a foreign `submoduleWith` states
                # its own parameters beside it, so the arm below hands that pair to the partner's
                # relation (`interface.joinInStatedRelation`), which reads both payloads whole.
                partnerArgs = other.specialArgs or { };
                # Each shared key is decided on the two declarations' OWN slots (`slotsDiffer`):
                # `zipAttrsWith` collects each set's attribute cell itself, so two declarations
                # passing one bound value (one nixpkgs `lib`, one function) agree after forcing only
                # its WHNF on every evaluator, where comparing two selections walked the whole value
                # on Nix and Determinate. A key only one declaration states never conflicts.
                slots = builtins.zipAttrsWith (_: vs: vs) [
                  args
                  partnerArgs
                ];
                conflicting = filter (k: slotsDiffer slots.${k}) (attrNames slots);
              in
              if partnerMods == null then
                let
                  joined = interface.joinInStatedRelation {
                    name = "submodule";
                    payload = interface.moduleSetPayload {
                      modules = mods;
                      specialArgs = args;
                      shorthandOnlyDefinesConfig = true;
                    };
                  } other;
                in
                if joined == null then
                  {
                    refused = "`submodule' and a partner whose module set is stated beside parameters this one does not carry, under no relation of its own";
                  }
                else
                  { merged = joined; }
              # The module sets UNION, so the args must too — and two declarations that disagree about
              # what a base module argument IS are a conflict this library names rather than resolves by
              # declaration order.
              else if conflicting != [ ] then
                {
                  refused =
                    "two `submodule' declarations stating different values for the base module argument"
                    + (if length conflicting == 1 then " " else "s ")
                    + concatStringsSep ", " (map (k: "`${k}'") conflicting);
                }
              # AUTHORED ORDER: the declaration planes ask the LATER declaration's relation about the
              # earlier one (`lib/modules.nix` `declaredPair`), so the partner's modules come first,
              # the union nixpkgs builds. Pinned by
              # `decl-merge.test-submodule-redeclaration-unions-in-authored-order`.
              else
                { merged = mkSubmodule (args // partnerArgs) (partnerMods ++ mods); };
          substructure = {
            # What a consumer learns from this type with NO value in hand, the twin of `mergeDefs`:
            #   declares = prefix: (evalModuleTree { inherit prefix; } modules).options
            # Reads `.options` off the same nested fixpoint the fold builds, with no defs supplied, so
            # the two halves cannot disagree about what a submodule declares and no instance-authored
            # value is forced.
            declares =
              prefix:
              (evalModuleTreeNested {
                modules = mods ++ [ namePlaceholder ];
                inherit prefix;
                specialArgs = args;
                check = null;
              }).options;
            modules = mods;
            # Rebuild this type over the module set a consumer supplies. REPLACES `mods` — it does NOT
            # append: a foreign module system builds the replacement as this type's OWN modules
            # (relocated) plus any sibling declarations, so concatenating would re-include `mods` a
            # second time, double-evaluating the base module (a readOnly config value — e.g.
            # gen-schema's `den.schema._kindNames` — then throws "defined 2 times").
            rebuild = m: mkSubmodule args m;
          };
          # A definition outside `admits` is refused here, naming the option and the file, before the
          # module reader would refuse it without either (`refusingOutside`).
          #
          # `threaded` is the same fold reading the tree through the evaluation's accessor instead of
          # evaluating it here (den-hoag-n6dh7 item 1, α's sibling): the site names this tree's `nests`,
          # the fold's `loc` and its `defs`. It tests no `undeclared`, as the called form does not: the
          # child's own evaluation, in `nests.calledMode`, is what refuses a finding there.
          mergeDefs = {
            __functor = _: called;
            threaded =
              ev:
              refusingOutside "submodule" admits (
                loc: defs:
                (ev.child {
                  inherit (ev) position;
                  inherit nests loc defs;
                }).config
              );
          };
        }
    );

  # The published constructor — signature UNCHANGED, and args-less by construction. A caller adds
  # base module args to the TYPE it returns, never to this.
  submodule = mkSubmodule { };

  # listOf — concat all list defs in order (byte-mode drops the order pass; spec §7), each element
  # merged through the element type (a submodule element becomes an instance; a leaf is verified).
  listOf =
    element:
    let
      # `mergeDefs` walks each definition with `imap0`, so a definition that is not a list is one
      # this type cannot consume — the domain, stated where the type is built and bound once: the
      # fold's domain check reads this same binding and refuses the definition by name.
      admits = isList;
      split =
        loc: defs:
        concatLists (
          imap0 (
            d: def:
            concatLists (
              imap0 (
                i: v:
                optional (isDefinedValue v) {
                  step = [
                    d
                    i
                  ];
                  # nixpkgs `listOf`'s segment, rendered from the same `d` and `i` as the step:
                  # the 1-based definition ordinal and the 1-based index within it, before the drop.
                  loc = loc ++ [ "[definition ${toString (d + 1)}-entry ${toString (i + 1)}]" ];
                  defs = [
                    {
                      inherit (def) file;
                      value = v;
                    }
                  ];
                  type = element;
                }
              ) def.value
            )
          ) defs
        );
      called = refusingOutside "listOf" admits (loc: defs: map foldElement (split loc defs));
      thread = exactThread element;
    in
    defineType (
      identified "listOf" [ element ] head [ ] {
        name = "listOf";
        inherit admits;
        whenEmpty.value = [ ];
        carries.element = element;
        recarry = c: listOf c.element;
        typeMergeRel = elementRel "listOf" listOf element;
        # Descend to the element type under the positional placeholder segment. A container's module
        # set IS its element's, and substituting one rebuilds the container over the substituted
        # element.
        substructure = {
          # The spine's step, stated as data (`interface.forwardStep`): the segment the container adds
          # on its way to `carries.element`. The walk follows it within its fuel and refuses by name at
          # exhaustion. A constant, so stating it allocates no thunk per container.
          forward = "*";
          modules = interface.spineModules interface.importedTypeWalkFuel element;
          declares =
            prefix: interface.spineDeclares interface.importedTypeWalkFuel element (prefix ++ [ "*" ]);
          rebuild = m: listOf (if carriesSub element then (subOf element).rebuild m else element);
        };
        # A position whose every definition was discharged is DROPPED, as nixpkgs' `listOf` drops it.
        # The index is taken BEFORE the drop, as nixpkgs indexes inside its `filter`, so a survivor's
        # loc (and a submodule element's `name`) is its source position whatever an earlier sibling's
        # condition says.
        #
        # ★ THE STEP IS `[ d i ]`, NOT THE LOC. `loc` indexes within ONE definition, so two definitions
        # of one element each both place an element at `"0"`; a position keyed on it would name the two
        # elements once. The step adds the definition's ordinal `d` among the position's definitions.
        inherit split;
        # `threaded` folds the same elements through the engine's threaded twin (den-hoag-n6dh7 item 5).
        mergeDefs = {
          __functor = _: called;
          threaded = ev: refusingOutside "listOf" admits (loc: defs: map (thread ev) (split loc defs));
        };
      }
    );

  # attrsOf / lazyAttrsOf — per-key merge through the element type. They differ where nixpkgs' do: a
  # key whose every definition was discharged is DROPPED by `attrsOf` and KEPT by `lazyAttrsOf` (at
  # the element's empty value), so `attrsOf`'s key set forces each key's definitions to WHNF.
  #
  # `defsByKey` groups the definitions by key ONCE (`zipAttrsWith`, nixpkgs' `zipAttrs` grouping), so
  # each key is a lookup, never a scan of the definitions per key; each key's list keeps definition
  # order. Building it forces each definition's value to WHNF, and no element value.
  # `attrsOf`/`lazyAttrsOf` (both folds and the split) and `anything` read it.
  defsByKey =
    defs:
    builtins.zipAttrsWith (_: vs: vs) (
      map (
        d:
        let
          inherit (d) file;
        in
        builtins.mapAttrs (_: value: { inherit file value; }) d.value
      ) defs
    );

  attrsOfWith =
    tyName: element:
    let
      # `mergeDefs` takes the key union across the definitions and indexes each by key, so a
      # definition that is not an attrset is one this type cannot consume. Bound once: the fold's
      # domain check reads this same binding and refuses the definition by name.
      admits = isAttrs;
      at = loc: k: ds: {
        step = [ k ];
        loc = loc ++ [ k ];
        defs = ds;
        type = element;
      };
      # Selected ONCE, when the type is built, and not per call. `attrsOf` keeps only a key some
      # definition still defines after discharge (its key set forces each definition to WHNF);
      # `lazyAttrsOf` keeps every key. Both read `defsByKey`.
      split =
        if tyName == "attrsOf" then
          loc: defs:
          let
            byKey = defsByKey defs;
          in
          concatMap (
            k:
            let
              ds = byKey.${k};
            in
            optional (isDefinedBy ds) (at loc k ds)
          ) (attrNames byKey)
        else
          loc: defs:
          let
            byKey = defsByKey defs;
          in
          map (k: at loc k byKey.${k}) (attrNames byKey);
      # Both containers' THREADED fold reads the split (den-hoag-n6dh7 item 5): the lazy one's key
      # set is every key, so its values stay unforced until read, as its called fold's are.
      #
      # The lazy fold MARKS its elements `under` (S1 arm (v), den-hoag-9d80v), once per fold call: an
      # element whose position the key walk made a container node is read off that node rather than
      # folded inline (`mergeDefsThreaded`). An element that nests directly is never a container
      # node, so that fold sets no mark (decided once, when the type is built). A container node
      # exists only under an accessor that states `containerNodes` (a gen evaluation's key walk);
      # under the bridge each element folds inline, one root evaluation per nested tree.
      marks = tyName == "lazyAttrsOf" && !(interface.isNesting element);
      thread = if tyName == "attrsOf" then exactThread element else threadElement;
      threaded =
        ev:
        refusingOutside tyName admits (
          loc: defs:
          let
            ev' = if marks && ev.containerNodes then ev // { under = true; } else ev;
          in
          listToAttrs (
            map (e: {
              name = head e.step;
              value = thread ev' e;
            }) (split loc defs)
          )
        );
      # The CALLED fold, selected once when the type is built (below).
      called = refusingOutside tyName admits (
        if tyName == "attrsOf" then
          loc: defs:
          listToAttrs (
            map (e: {
              name = head e.step;
              value = foldElement e;
            }) (split loc defs)
          )
        else
          loc: defs: builtins.mapAttrs (k: mergeDefs (loc ++ [ k ]) element) (defsByKey defs)
      );
    in
    defineType (
      identified tyName [ element ] head [ ] {
        name = tyName;
        inherit admits;
        whenEmpty.value = { };
        carries.element = element;
        recarry = c: attrsOfWith tyName c.element;
        # gen-merge keeps `attrsOf`/`lazyAttrsOf` as distinct type NAMES where nixpkgs unifies both
        # under one constructor discriminated by a payload field. Distinct names are the conservative
        # direction: the two never merge with each other. Each is a POINT of the unified foreign
        # constructor's payload, so it is published under that constructor and joins a same-named
        # foreign partner in that partner's relation (`interface.embeddings`, through `elementRel`). The
        # rebuild keeps THIS container's name, so the distinction survives substitution.
        typeMergeRel = elementRel tyName (attrsOfWith tyName) element;
        # Descend to the element under the per-key placeholder segment, so an `attrsOf (submodule …)`
        # registry exposes its INSTANCE option surface to an introspecting consumer.
        substructure = {
          forward = "<name>";
          modules = interface.spineModules interface.importedTypeWalkFuel element;
          declares =
            prefix: interface.spineDeclares interface.importedTypeWalkFuel element (prefix ++ [ "<name>" ]);
          rebuild = m: attrsOfWith tyName (if carriesSub element then (subOf element).rebuild m else element);
        };
        inherit split;
        # `attrsOf`'s fold is the split's elements, each folded through the element type and placed at
        # its key.
        #
        # ★ `lazyAttrsOf`'S FOLD IS THE SPLIT'S TWIN, NOT ITS READER, and that is measured, not chosen:
        # it is the hub bench's `wideFreeform` hot path, whose thunk band and allocation bound have no
        # headroom, and reading the split there costs a record per key (measured at 92dec6e + this
        # split: thunks 1.096 -> 1.166 over the 1.096 band, alloc 0.805 -> 0.856 over 0.806, rc 6).
        # So its text is the fold it was, selected once at construction, and it agrees with the split
        # by a cell (`ci/tests/nesting-declaration.nix`, `lazy-fold-is-the-split's`) rather than by
        # sharing a binding. A nesting element never reaches this fold once the threaded half lands:
        # its option folds through the threaded twin, which reads the split.
        mergeDefs = {
          __functor = _: called;
          inherit threaded;
        };
      }
    );

  attrsOf = attrsOfWith "attrsOf";
  lazyAttrsOf = attrsOfWith "lazyAttrsOf";

  # attrs — the NULLARY container: an attribute set whose KEYS are its whole content, with no element
  # type to descend into. The injected leaf library answers "is this value an attribute set", which is
  # a predicate over ONE value; a module system asks two further questions a predicate cannot state —
  # what zero definitions are worth, and how several of them combine. Those are properties of a merge
  # STRATEGY, and every other container in this file already answers them here.
  #
  # ★ THE NAME COLLIDES, AND THE COLLISION IS DECLARED IN TWO PLACES BECAUSE IT IS TWO COLLISIONS.
  # The EXPORT collision — this name is already in the leaf library's export environment — is admitted
  # by the `attrs` allowlist entry at `lib/default.nix`, which keeps the shadowed predicate reachable.
  # The TYPE-MERGE collision is new at this name and is not the same fact: unlike `listOf`/`attrsOf`,
  # whose two spellings disagree in their NAMES and so never meet as merge operands, both spellings
  # here are literally `attrs`. That is what the stated relation below answers.
  attrs =
    let
      # The domain stays the predicate's. What this type does with a definition OUTSIDE that domain
      # is stated by its fold because the engine does not state it: the post-fold check reads
      # `verify`, and a structural type carries `admits`, so the engine never consults `admits` on
      # the option-fold path. Bound once, for `admits` and for the fold's domain check alike.
      admits = isAttrs;
    in
    defineType {
      name = "attrs";
      inherit admits;
      whenEmpty.value = { };
      # STATED, NOT INHERITED, AND TWO-LEVEL. The default nullary relation matches on `.name` alone,
      # which is right for a name this library alone mints. This is not one of those, so a name-only
      # relation would answer `merged` to any same-named partner and silently adopt a fold that is not
      # this one's. The second level asks the DISCRIMINATING FACT — did the partner bring a fold of its
      # own? — through `mergeDefs`, the same presence test the engine's own dispatch asks.
      #
      # ★ THREE ANSWERS, AND THE THIRD IS WHY THERE ARE NOT TWO. Collapsing the name mismatch and the
      # foldless same-name case into one `else` reports "a partner named `attrs'" about a partner named
      # `string', and reaches the refusal shape this file's discipline forbids — the same name on both
      # sides of the pair, which tells the reader nothing they did not already have.
      typeMergeRel =
        other:
        if !(isAttrs other) || (keyOf other) != "attrs" then
          { refused = "`attrs' and `${nameOf other}'"; }
        else if other ? mergeDefs then
          { merged = attrs; }
        else
          { refused = "`attrs' and a partner named `attrs' that states no fold of its own"; };
      # THE FOLD IS TOTAL OVER ITS INPUT IN BOTH DIRECTIONS, and each refusal is a catchable throw
      # naming the option, this type, and the files that wrote the definitions at fault.
      #
      # ★ THE DOMAIN CHECK RUNS BEFORE THE FOLD, matching `either`'s fold below — and it has to run
      # there rather than after. The engine's `verify` dispatch reads the FOLDED result, so a definition
      # this type cannot consume would reach `//` first and the interpreter would answer with a raw
      # type error naming neither the option nor the file, an abort no caller can turn into a
      # diagnostic. The check is `refusingOutside`, the one every structural container here uses.
      #
      # ★ A SURVIVING SAME-KEY DISAGREEMENT IS AN UNRESOLVED AMBIGUITY, NOT AN OVERRIDE (ADR-0029). By
      # the time this fold runs the priority pass has already resolved every INTENDED override, so two
      # definitions setting one key to different values is a disagreement nobody expressed, and letting
      # fold order drop one side is the silent-loss shape this project refuses. Definitions that set a
      # key to EQUAL values lose nothing, so that key serves the value nixpkgs' `//` fold serves
      # (den-hoag-t1j4z, ADR-0039). Equality is `slotsDiffer`, the definers' own value slots under `==`.
      # The function text is for two functions only, the pair `==` cannot show to agree; a function
      # against a non-function is shown to disagree, and reads as different values.
      #
      # ★ DECIDED PER KEY, WHERE THE KEY IS READ. The key set is the union's, forced as before; each
      # shared key's comparison sits inside its own value, so reading one key never forces another's
      # `==` — the strictness nixpkgs does not have stays confined to the key that is read.
      mergeDefs = refusingOutside "attrs" admits (
        loc: defs:
        let
          merged = foldl' (res: d: res // d.value) { } defs;
          filesAt =
            k: concatStringsSep ", " (map (d: toString (d.file or "<def>")) (filter (d: d.value ? ${k}) defs));
          refusal =
            k: vs:
            let
              cells = map (v: [ v ]) vs;
              other = head (head (filter (c: c != head cells) cells));
            in
            if prelude.isFunction (head vs) && prelude.isFunction other then
              "gen-merge: option `${showOption loc}' has `attrs' definitions that set `${k}' to a function, and Nix compares functions only by identity, so these cannot be shown to agree (${filesAt k})"
            else
              "gen-merge: option `${showOption loc}' has `attrs' definitions that set `${k}' to different values (${filesAt k})";
        in
        if length defs < 2 then merged else core.unionAgreeing refusal defs
      );
    };

  # deferredModule (spec §1 item 7) — collect defs into ONE module (via imports), located; NEVER
  # forced by the composition plane. Output is a plain, import-usable module value (nixpkgs-faithful:
  # a deferred module's fold produces `{ imports = [ … ]; }`), handed opaque to the terminal.
  deferredModule =
    let
      # A type carrying no domain at all accepts every definition, which is right only for a type
      # whose fold really does accept any value. This one's does not: `mergeDefs` wraps each def into
      # an `imports` list, and the engine's `callM` (lib/modules.nix) can apply only a path, a string
      # naming an absolute path, a function, a `__functor` attrset, or a plain attrset. Any other
      # value carried into `imports` unexamined would be refused by whoever imports it — accepted
      # HERE and failing somewhere else, with no option path and no definition file. So the fold
      # refuses it here, by name, through the same binding it states as `admits`.
      #
      # The domain is nixpkgs `deferredModuleWith`'s `isAttrs x || isFunction x || path.check x`,
      # whose `path` predicate admits a STRING beginning with `/` as well as a path; `callM` imports
      # both.
      admits = isModuleValue;
    in
    defineType {
      name = "deferredModule";
      inherit admits;
      # ── the module set is EMPTY, and empty is not absent ─────────────────────────────────────────
      # `null` and `[ ]` are two different facts, and a single `null` cannot carry both: `null` says
      # "this type has no sub-module concept at all" (a leaf's answer), `[ ]` says "this type has a
      # module set and there is nothing in it". Reported as `null`, this type's "has nothing to
      # declare" was indistinguishable from a leaf's "declares nothing" — the missing distinction is
      # the design choice, so the encoding states it. gen-merge ships no
      # `deferredModuleWith`/`staticModules`, which is exactly WHY the set is empty by construction
      # rather than by omission, and why reporting it is a statement of fact and not a stub.
      #
      # The three answers are stated together because a consumer reads them together: a foreign module
      # system branches on whether the module set is null and, on every other type, REPLACES the
      # option's type with the rebuild. So a non-null module set with a leaf's null rebuild would hand
      # every mounted option a null type — the encoding and the rebuild are one decision, not two.
      substructure = {
        declares = _prefix: { };
        modules = [ ];
        # Rebuilding over the empty set is this same type. Over a NON-EMPTY one there is nothing to
        # build: without a static-module parameter the modules could only be dropped, and a rebuild
        # that silently discards what it was handed is the wrong value with no diagnostic. Refuse by
        # name instead.
        rebuild =
          m:
          if m == [ ] then
            deferredModule
          else
            throw (
              "gen-merge: `deferredModule' cannot be rebuilt over a module set of "
              + toString (length m)
              + "; it carries no static modules and dropping them would lose the declarations silently"
            );
      };
      # Every same-named partner, gen's own included, is joined in its stated relation over this type's
      # embedding (`interface.joinCarriedInStatedRelation`), so a foreign partner's static modules
      # survive the join rather than being dropped by a nullary answer of `self`.
      typeMergeRel =
        other:
        let
          sameName = isAttrs other && (keyOf other) == "deferredModule";
          joined =
            if sameName then
              interface.joinCarriedInStatedRelation {
                name = "deferredModule";
                role = null;
                carried = null;
                self = deferredModule;
              } other
            else
              null;
        in
        if joined != null then
          { merged = joined; }
        else if !sameName then
          { refused = "`deferredModule' and `${nameOf other}'"; }
        else
          {
            refused = "`deferredModule' and a same-named partner that states no relation this type embeds in";
          };
      mergeDefs = refusingOutside "deferredModule" admits (
        loc: defs: {
          imports = map (
            d: setDefaultModuleLocation "${toString (d.file or "<def>")}, via option ${showOption loc}" d.value
          ) defs;
        }
      );
    };

  # Membership predicate for union dispatch. gen-types leaf checkers expose `verify` (v → null|err);
  # gen-merge structural types expose `admits` (v → bool). Prefer `verify` FIRST — a gen-types
  # `check` is curried (not v → bool), so it must never be applied here — and fall through to the
  # import environment for a FOREIGN element, which states its domain in the foreign protocol's
  # words and nowhere else.
  #
  # A STRUCTURAL TYPE OWES ITS OWN ANSWER HERE, and "accepts anything" is not one: it is right for a
  # type whose fold really does accept any value (`raw`, `anything`), and a standing lie for one
  # whose fold does not. Left on it inside a union it is worse than imprecise — the union's domain is
  # a disjunction over its members, so ONE member answering "yes" to everything makes the whole union
  # unable to refuse anything, and the definition the member cannot consume reaches the interpreter
  # instead (`either`, below).
  #
  # A `check` a foreign wrapper rewrote over a gen member is asked too (den-hoag-4ifgb): nixpkgs'
  # union reads its members' `check`, so a member it refines away is not chosen.
  # The ownership test is gen-types' `rewritesCheck`, restated inline for cost, negated: a call is an
  # environment on every member asked. The construction door holds this spelling to the protocol
  # (`lib/default.nix`).
  isValid =
    t: v:
    if t ? verify then
      t.verify v == null
      && (!(t ? _checkWitness && t ? check) || t.check == t._checkWitness || interface.admitsCarried t v)
    else if t ? admits then
      t.admits v
      && (!(t ? _checkWitness && t ? check) || t.check == t._checkWitness || interface.admitsCarried t v)
    else
      let
        foreign = interface.importedAdmits t;
      in
      if foreign == null then true else foreign v;

  # nullOr / option — a MERGE-aware nullable (NOT a gen-types verify-only `option`, which would drop
  # a wrapped merge-type's behaviour, e.g. a ref field's coercion). Every definition null serves
  # null; none null merges through the element type (leaf verify or ref/submodule merge, via
  # mergeDefs); null beside a value is refused by name, as nixpkgs' `nullOr` refuses it.
  nullOr =
    element:
    let
      # One element position, adding no step; none when every definition is null. A set holding null
      # BESIDE a value has no element to merge through, as nixpkgs' `nullOr` reports a head error for
      # it: the position's member is `null` (the fold's refusal, as `either`'s is), and it carries the
      # definitions whole so the refusal names every file.
      split =
        loc: defs:
        let
          nulls = length (filter (d: d.value == null) defs);
        in
        optional (nulls != length defs) {
          step = [ ];
          inherit loc defs;
          type = if nulls == 0 then element else null;
        };
      foldWith =
        foldE: loc: defs:
        let
          elements = split loc defs;
          e = head elements;
        in
        if elements == [ ] then
          null
        else if e.type == null then
          throw "gen-merge: option `${showOption loc}' is defined both null and not null (${
            concatStringsSep ", " (map (d: toString (d.file or "<def>")) defs)
          })"
        else
          foldE e;
      called = foldWith foldElement;
    in
    defineType (
      identified "nullOr" [ element ] head [ ] {
        name = "nullOr";
        # A nullable option nobody defined IS null. Distinct from the containers only in which empty
        # value it names.
        whenEmpty.value = null;
        carries.element = element;
        recarry = c: nullOr c.element;
        typeMergeRel = elementRel "nullOr" nullOr element;
        # Pass straight through to the element, adding NO path segment. A nullable introduces no path
        # level — `nullOr (submodule …)` declares exactly what the submodule declares, at the same
        # location — which is why this differs from `attrsOf`'s `<name>` and `listOf`'s `*`. A nullable
        # declares exactly what its element declares, so it carries exactly its element's module set too.
        substructure = {
          # the step adds no segment
          forward = null;
          modules = interface.spineModules interface.importedTypeWalkFuel element;
          declares = interface.spineDeclares interface.importedTypeWalkFuel element;
          rebuild = m: nullOr (if carriesSub element then (subOf element).rebuild m else element);
        };
        admits = v: v == null || isValid element v;
        inherit split;
        # One fold over its element's, called or threaded (den-hoag-n6dh7 item 5), and the HEAD
        # JUDGEMENT beside it (den-hoag-e6m9d): its own split's answer, so a union holding it asks
        # what this fold would do with the definitions whole. All null is taken (the fold serves
        # null), null beside a value is refused, and a set with no null is the element's to judge.
        mergeDefs = {
          __functor = _: called;
          threaded = ev: foldWith (threadElement ev);
          headJudge =
            loc: defs:
            let
              elements = split loc defs;
            in
            if elements == [ ] then
              null
            else if (head elements).type == null then
              "`nullOr' takes null beside a value (${
                concatStringsSep ", " (map (d: toString (d.file or "<def>")) defs)
              })"
            else
              interface.importedHeadJudge element loc defs;
        };
      }
    );
  option = nullOr;

  # `either a b`'s own relation over a partner that offers its member pair: both members merge
  # pairwise or the pair refuses. Bound at file level, not inside `either`, so it costs a gen × gen
  # pair no thunk per construction or per call.
  eitherMemberwise =
    a: b: other:
    let
      alts = interface.importedOffered "alternatives" other;
    in
    if alts == null || !(isList alts) || length alts != 2 then
      { refused = "`either' and a partner that states no member pair"; }
    else
      let
        left = mergeElemTypes a (head alts);
        right = mergeElemTypes b (elemAt alts 1);
      in
      if left == null || right == null then
        { refused = "`either' and `either', whose members do not merge pairwise"; }
      else
        { merged = either left right; };

  # either A B — recursion-safe lazy union: merge through the member that accepts EVERY definition,
  # or refuse by name (byte-mode best-effort; the surface's only use is aspectOrFn where A's domain
  # is total).
  either =
    a: b:
    let
      # THE MEMBER CHOICE, stated ONCE (den-hoag-n6dh7 item 2): the member that accepts every
      # definition, `null` when neither does (the fold's refusal). With no definitions there is
      # nothing to place and nothing to refuse, and the member decides only which empty value the
      # fold goes on to ask for.
      #
      # A member accepts when every definition passes its `isValid` and its HEAD JUDGEMENT takes
      # them whole (`interface.importedHeadJudge`), as nixpkgs' `either` takes `t1` only when `t1`'s
      # whole merge reports no `headError`. Asked pointwise only, `either a b` admits `{ 1, "s" }`
      # over `int` and `str` and is chosen, then refuses inside, and a later member that takes the
      # set whole is never asked. `oneOf` folds LEFT, so every `oneOf` of three or more members has
      # such a member first. The judgement is the member's own published answer (`either`'s and
      # `nullOr`'s `mergeDefs.headJudge`, which a derivation and a refinement carry with the fold),
      # or a foreign member's own `merge.v2` `headError`, so no constructor is recognised by name
      # (den-hoag-e6m9d). The pointwise conjunct stays for a refined member (nixpkgs' `addCheck`
      # keeps the record's fold), whose `headError` is its base's or else the added check's.
      choose =
        loc: defs:
        let
          accepts = t: all (d: isValid t d.value) defs && interface.importedHeadJudge t loc defs == null;
        in
        if defs == [ ] then
          b
        else if accepts a then
          a
        else if accepts b then
          b
        else
          null;
      # One member position, adding no step: the definitions whole, under the member `choose` picks.
      split = loc: defs: [
        {
          step = [ ];
          inherit loc defs;
          type = choose loc defs;
        }
      ];
      foldWith =
        foldE: loc: defs:
        let
          e = head (split loc defs);
        in
        if e.type == null then
          throw "gen-merge: option `${showOption loc}' has definitions no single `either' member accepts (${refusal loc defs})"
        else
          foldE e;
      # Why neither member takes the definitions, member by member: the head judgement this union
      # publishes when it refuses, and the text its own fold throws. A member publishing a head
      # judgement that refuses answers with the judgement's own text, so the refusal descends
      # through every nested union to the LEAF members and the definitions each could not take; no
      # list is empty, since a member rejecting nothing whose judgement takes the set would have
      # been chosen. Between them the leaves name every member and every definition the author has
      # to reconcile, which is more than the one pair the interpreter would have collided on. A
      # foreign member's own `headError` is read last, after the definitions it rejects one by one.
      # Bound inside the refusal, so a union that is never refused pays nothing for it.
      refusal =
        loc: defs:
        let
          member =
            t:
            let
              judged = interface.importedHeadJudge t loc defs;
              rejects = filter (d: !(isValid t d.value)) defs;
            in
            if t ? mergeDefs.headJudge && judged != null then
              judged
            else if rejects != [ ] then
              "`${nameOf t}' rejects ${concatStringsSep ", " (map (d: toString (d.file or "<def>")) rejects)}"
            else
              "`${nameOf t}' refuses them whole: ${judged}";
        in
        "${member a}; ${member b}";
      called = foldWith foldElement;
    in
    defineType (
      identified "either" [ a b ] (ids: ids) [ ] {
        name = "either";
        # The members are carried POSITIONALLY, not as a set — `either str int` and `either int str`
        # are distinct types, and two `either`s merge iff both members merge pairwise.
        carries.alternatives = [
          a
          b
        ];
        recarry = c: either (head c.alternatives) (elemAt c.alternatives 1);
        # ★ ONE CARVE-OUT, against a RAW FOREIGN partner (nixpkgs' `either`, whose relation is in its
        # `typeMerge` and not its functor): the partner rebuilt from its published functor decides
        # (`interface.joinInRebuiltPartner`), as `elementRel`'s carve-out does for a container. The
        # test for a gen partner sits here, so a gen × gen pair builds nothing for it.
        typeMergeRel =
          other:
          if !(isAttrs other) || (keyOf other) != "either" then
            { refused = "`either' and `${nameOf other}'"; }
          else if other ? carries then
            eitherMemberwise a b other
          else
            let
              foreignJoin = interface.joinInRebuiltPartner {
                role = "alternatives";
                self = either a b;
              } other;
            in
            if foreignJoin != null then
              {
                merged = foreignJoin;
                meets = true;
              }
            else
              eitherMemberwise a b other;
        substructure = {
          # A union's members introduce no path level, so it declares nothing of its own — stated
          # rather than inherited, because the pair lives in `carries` and this does not read it.
          declares = _prefix: { };
          modules = null;
          rebuild = _m: null;
        };
        admits = v: isValid a v || isValid b v;
        # A UNION'S FOLD IS TOTAL: every definition is merged through a member that accepts it, or the
        # merge refuses by name. Choosing the member from the FIRST definition's shape and then merging
        # ALL of them through it hands a definition that member cannot consume straight to the
        # interpreter, which answers with a raw type error naming neither the option nor the file that
        # wrote the definition — and that abort escapes `tryEval`, so no caller can turn it into a
        # diagnostic either. The predicate is the members' own, the same one `admits` above is the
        # disjunction of; what is resolved ONCE over the whole definition set, rather than per
        # definition against a member already chosen, is WHICH member — and that leaves no branch that
        # can hand on a definition its member rejects. Nothing is filtered: a set no member takes whole
        # has no merge to perform, and the refusal is the answer. A homogeneous set is unchanged — the
        # member selected from its first definition is the member that accepts them all.
        #
        # THE MEMBERS' ANSWERS ARE THIS RULE'S PRECONDITION, which is why the structural types above
        # state their domains: a member that accepts every definition by default would be picked for a
        # set it cannot merge and the refusal could never fire. A member that genuinely accepts
        # anything (`raw`, `anything`, and a consumer type declaring so on purpose) still does, and is
        # still chosen first.
        inherit choose split;
        # One fold over its chosen member's, called or threaded (den-hoag-n6dh7 item 5), and the HEAD
        # JUDGEMENT beside it (den-hoag-e6m9d): its own choice, so a union holding this one in first
        # position asks it as nixpkgs' `either` asks a member for its `headError`.
        mergeDefs = {
          __functor = _: called;
          threaded = ev: foldWith (threadElement ev);
          headJudge = loc: defs: if choose loc defs != null then null else refusal loc defs;
        };
      }
    );

  # oneOf [t1 t2 …] — n-ary either, nested to the LEFT as nixpkgs' `foldl' either` nests it, so
  # `oneOf [ a b c ]` IS `either (either a b) c`: its `nestedTypes`, its docs phrase and its merge
  # with a nixpkgs `oneOf` are nixpkgs'. Members are still tried first to last.
  oneOf =
    ts:
    if ts == [ ] then throw "gen-merge: oneOf: empty type list" else foldl' either (head ts) (tail ts);

  # raw — opaque single value; it brings no fold of its own, so the engine's leaf fold (one winner,
  # or equal winners) is what folds it, and the boundary publishes that same fold outward.
  raw = defineType {
    name = "raw";
  };

  # anything — recursive value merge (lists concat, attrsets per-key recurse, else the ENGINE'S LEAF
  # FOLD; an attrset carrying `__mint` is carried whole by that same fold). Used by non-strict instance
  # freeform + niche raw-ish spots. Its attrset arm is nixpkgs' `(attrsOf anything).merge`: each key's
  # definitions take the engine's own spine, so a property marker at a nested key is discharged there,
  # and the key set is strict (den-hoag-15wnx). It is not the full nixpkgs `types.anything`
  # module-composition of function values.
  #
  # ★★★ THE NON-STRUCTURAL ARM IS `mergeLeaf`, NOT A SELECTION. It used to be `prelude.last vals`:
  # two UNEQUAL equal-priority definitions returned one of them and destroyed the other with no
  # diagnostic on any channel, where nixpkgs' `anything.merge` reaches `mergeEqualOption` and THROWS
  # (measured at the pinned rev: `"x"`/`"y"` returns a value here and refuses there). This is the
  # value-plane twin of the freeform selection `den-hoag-5r1a7` removed one file over, and the same
  # argument settles it — except that "merge" DEGENERATES on two scalars: equal ones merge to that
  # value, unequal ones have nothing to merge, so the arm collapses exactly onto `mergeEqualOption`'s
  # own semantics. That relation already lives in this engine as `mergeLeaf` — it is what `raw` folds
  # by, and what every no-`.merge` leaf folds by — so the arm CONSULTS it rather than restating it,
  # and the two neighbouring answers to one question cannot drift apart.
  #
  # `loc` and `file` are therefore threaded through the recursion where the old fold dropped both at
  # the door. A refusal names the FULL path — `mergeLeaf` reports through `showOption loc` — so a
  # conflict under a nested key names that key rather than the option root, which is the same
  # `loc ++ [ k ]` descent nixpkgs' `(attrsOf anything).merge` makes.
  mergeAnythingDefs =
    loc: defs:
    if defs == [ ] then
      throw "gen-merge: anything: no definitions"
    else if all (d: isList d.value) defs then
      concatLists (map (d: d.value) defs)
    else if all (d: isAttrs d.value) defs then
      # ★★ A VALUE CARRYING `__mint` IS CARRIED WHOLE, NEVER REBUILT. `__mint` is the one mark a
      # substrate constructor writes (ADR-0016 ruling 5): the value is a CONSTRUCTION, and its identity
      # is either a digest or a decision over the reified value itself under `==` (ADR-0034). The
      # rebuild below keeps the first and destroys the second — `listToAttrs` lands every closure in a
      # fresh Value cell, and upstream Nix and Determinate equate a function only by that cell while
      # Lix compares the forced object — so a rebuilt construction stopped equalling itself on two
      # evaluators of three. When EVERY definition carries the mark this arm is exactly `raw`'s fold,
      # and it CONSULTS `mergeLeaf` rather than restating it: one definition is carried as it is,
      # several are carried if they are all `==` to the first and refused by name at `loc` otherwise.
      # A mixed list (some marked, some plain) still takes the rebuild. The head is tested first so a
      # plain value pays one attribute test per attrset node; every definition is already forced to
      # WHNF by the arm above, so `? __mint` forces nothing new. Reading the mark decides the merge
      # SHAPE of an untyped slot, never an identity regime, which stays the constructor's.
      #
      # ★ THE FOLD'S STATED COSTS, which are `mergeLeaf`'s own and not this arm's invention:
      #   · TWINS ARE REFUSED. Two INDEPENDENT constructions of one identity (one digest, distinct
      #     closures) are `==`-unequal, so defined twice they refuse the whole value where the
      #     rebuild gave one. Two definitions of ONE value still fold to it. Since gen-merge's own
      #     composites carry `__mint` (den-hoag-6orb8 U2), this reaches them too: two constructions of
      #     `listOf int` defined in one slot are refused by name, where the rebuild admitted them.
      #   · A hand-written `__mint` on a freshly built CYCLIC value, defined twice, sends `==` round
      #     the cycle and overflows the stack uncatchably — the residue `mergeLeaf` already states for
      #     a leaf, extended here to whole attrsets.
      #   · Values carrying NO `__mint` are still rebuilt, so their compared limbs still do not survive
      #     transport (a nixpkgs composite, an `mkOptionType` record, or `{ f = g; }`).
      if (head defs).value ? __mint && all (d: d.value ? __mint) defs then
        mergeLeaf loc defs
      else
        let
          byKey = defsByKey defs;
        in
        listToAttrs (
          concatMap (
            k:
            let
              ds = byKey.${k};
            in
            # A key some definition marks (`mkIf`, `mkMerge`, `mkOverride`, `mkOrder`) takes the
            # engine's spine (discharge, then `filterOverrides`, then `sortProperties`) before the fold
            # recurses, and it is kept only if a definition survives discharge: nixpkgs'
            # `(attrsOf anything).merge`, whose key set forces every definition to WHNF. A key no
            # definition marks recurses directly, because the spine is the identity on it; that
            # restates `attrsOf`'s split rather than reading it, and the reason is measured
            # (den-hoag-15wnx): read through `attrsOf anything` the fold cost 334 thunks per key
            # against nixpkgs' 270, and this arm costs 102.
            if builtins.any (d: d.value ? _type) ds then
              optional (isDefinedBy ds) {
                name = k;
                value = mergeDefs (loc ++ [ k ]) anything ds;
              }
            else
              [
                {
                  name = k;
                  value = mergeAnythingDefs (loc ++ [ k ]) ds;
                }
              ]
          ) (attrNames byKey)
        )
    else
      mergeLeaf loc defs;
  anything = defineType {
    name = "anything";
    mergeDefs = mergeAnythingDefs;
  };
in
{
  inherit
    mkOption
    mkOptionType
    # The two halves of a type's construction, published in `types` (not at the top level):
    # `mkType` is the gen record alone (what the boundary is handed, and what a C-2 reading is taken
    # on), `defineType` is that record expressed in the foreign protocol as well (what every
    # constructor above builds, and the library's single crossing site).
    mkType
    defineType
    # A type derived from a completed one, re-completed rather than overridden (den-hoag-5kic). Also
    # published at the library's top level, as the same value.
    deriveType
    submodule
    listOf
    attrs
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
}
