# interface.nix — the nixpkgs `optionType` PROTOCOL BOUNDARY, and the only unit that utters it.
#
# ★ CARDELLI'S WORD, ACQUIRED AT THE PRIMARY. A linkset is "a collection of named judgments plus an
# INTERFACE" (`used/markdown/cardelli-1997-program-fragments-linking.md:1013`), and that interface —
# his E0 — is "the external interface of the entire linkset" (`:755`): the object that stands at a
# fragment collection's boundary and says what the collection offers outward and requires inward.
# That is what this unit is for gen-merge's type vocabulary. Definition 5-1 (`:1022-1024`) names the
# two halves it holds — `imports(L)`, THE IMPORT ENVIRONMENT, and `exports(L)`, THE EXPORT
# ENVIRONMENT — and the identifiers below are his: `exportType` is "the type exported by the
# fragment" (`:803`), `importType` is "the type of the f import" (`:805`), and `exportFields` is the
# list of names a fragment offers (`:781`, the "import list"/"export list" pair).
#
# ★ COMPOUND IDENTIFIERS THROUGHOUT, and that is a hazard note rather than a style rule: `import` is
# a Nix BUILTIN, so a bare `import` binding shadows it for the rest of the scope. The bare words
# appear only as attribute KEYS, never as bindings.
#
# ── WHAT THIS IS NOT ──────────────────────────────────────────────────────────────────────────────
# Both neighbours below carry claims that are TRUE of them and FALSE here, which is exactly how a
# name gets reused into a lie.
#   · NOT gen-bind's `crossing.mkAdapter`. That answers WHERE AND WHEN a substrate-resolved VALUE may
#     enter an evaluation gen does not own — offered positions as (Channel, Time) pairs over
#     { Formals, ArgEnv } x { Substrate, TargetInvoked }. This answers HOW A TYPE DESCRIPTOR IS
#     EXPRESSED in a foreign type protocol. Placement versus representation, and the word `adapter`
#     is left where it already means the first of those.
#   · NOT the three-part framework interface (ADR-0027). A framework binds AGAINST gen's interface
#     with a vocabulary map, a gen-link lens and two witness-pattern declarations; nixpkgs supplies
#     none of the three, and gen-merge REPLACES its `lib.evalModules` rather than mapping onto it.
#     This sits BENEATH the framework interface, not as an instance of it.
#
# ── WHAT "CEREMONY" WOULD LOOK LIKE HERE ──────────────────────────────────────────────────────────
# The commission that licensed this construct licensed it conditionally: try the boundary, and if it
# turns out to be ceremony and unnecessary complexity, collapse it back into gen-merge. A condition
# nobody can read is not a condition, so the four shapes that WOULD be ceremony are stated here
# concretely, each with a reading someone can take without a matter of taste. Any one of them holding
# is the trigger.
#
#   C-1  THE UNIT ONLY FORWARDS. A field would be FORWARDED if it were copied across under the same
#        meaning and the same name — no translation, just relocation. Count the classes below: if a
#        FORWARDED class ever appears, or if DERIVED falls to or below FOREIGN CONSTANT, the unit
#        has stopped translating and is a second name for the same record.
#   C-2  A FIELD SET WITH NO TRANSLATION. A derived foreign field satisfied by reading a gen field OF
#        THE SAME NAME is a rename wearing a function call. The predicate is mechanical because the
#        gen record is deliberately named apart: does anything below read `t.<a foreign field name>`?
#        Under a gen record built to the substrate vocabulary no such field exists — and if one does,
#        the substrate vocabulary was not built, which is the finding.
#   C-3  THE BOUNDARY IS CROSSED ONE DIRECTION ONLY. `importType` absent, or present and unreachable
#        from the engine's own type merge. A translation that only ever runs outward is a stamping
#        pass, and a stamping pass belongs where the stamp is applied.
#   C-4  THE ENGINE STILL SPEAKS THE FOREIGN PROTOCOL — it reads foreign-protocol fields off types
#        that never cross. Behavioural, not a count: hand the engine's `mergeTypes` two gen-native
#        types carrying no foreign-protocol field and it must return a merged type.
#
# ★ WHAT DOES NOT FIRE IT, because a small translation and a translation that translates nothing are
# different things: that this unit is small; that few types cross today; that two of the fourteen
# fields are constants of the foreign protocol with no counterpart on this side. Constants are not
# forwarding — they are the part of a foreign interface that has no source here, and naming them is
# how the boundary stays total.
{
  prelude,
  showOption,
}:
let
  inherit (prelude)
    attrNames
    concatStringsSep
    elemAt
    filter
    head
    isAttrs
    isFunction
    isList
    length
    all
    map
    ;

  # ── THE EXPORT ENVIRONMENT'S NAMES ──────────────────────────────────────────────────────────────
  # The fourteen names nixpkgs' module system reads off every option type. They are the foreign
  # protocol's, not this library's, and they are private data of this unit: a name from this list
  # appearing anywhere above it is the boundary leaking.
  exportFields = [
    "_type"
    "name"
    "description"
    "descriptionClass"
    "deprecationMessage"
    "check"
    "merge"
    "emptyValue"
    "getSubOptions"
    "getSubModules"
    "substSubModules"
    "typeMerge"
    "nestedTypes"
    "functor"
  ];

  # ── THE PARTITION, AS DATA RATHER THAN AS A COMMENT ─────────────────────────────────────────────
  # Which class each of the fourteen falls in, published so C-1 can be READ instead of argued. A
  # comment stating this would drift from the code the first time a field moved; a value cannot,
  # because the suite quantifies over it — the three classes must be disjoint and their union must be
  # exactly `exportFields`, so a field silently added, dropped or double-classified fails a cell
  # rather than passing unnoticed.
  #
  # DERIVED means a real translation FROM A DIFFERENTLY-NAMED gen datum; the name on the right is
  # that datum, and `check` has two sources because a value predicate and a domain predicate are two
  # different gen facts that answer the same foreign question. FOREIGN CONSTANT means no counterpart
  # exists on this side — not "forwarded", which is the thing C-1 fires on: a constant is the part of
  # a foreign interface that has no source here, and naming it is how the boundary stays total.
  # NAME-CARRIED means carried or defaulted from the name, translating nothing — which is why those
  # two are ALLOWED to be the same word on both sides and the DERIVED ten are not.
  exportClasses = {
    derived = {
      check = "verify | admits";
      merge = "mergeDefs";
      emptyValue = "whenEmpty";
      nestedTypes = "carries";
      deprecationMessage = "deprecated";
      getSubOptions = "substructure";
      getSubModules = "substructure";
      substSubModules = "substructure";
      typeMerge = "typeMergeRel";
      functor = "typeMergeRel";
    };
    foreignConstant = [
      "descriptionClass"
      "_type"
    ];
    nameCarried = [
      "name"
      "description"
    ];
  };

  # ── THE FOREIGN PROTOCOL'S SPELLING OF WHAT A TYPE CARRIES ──────────────────────────────────────
  # A gen type says what it wraps in ROLES: `element` for the one-parameter containers, `alternatives`
  # for a union's members, `moduleSet` for a submodule's modules. The foreign protocol says the same
  # thing TWICE and not always the same way — once in a functor payload (the row two types must agree
  # on before they may merge) and once in the `nestedTypes` introspection alias — and for a union the
  # two disagree with each other: the payload carries a positional list under the container's own key
  # while the alias names the members. Holding both spellings here is the reason this table exists;
  # a role with no entry is a finding rather than a default, so the map is total by refusal.
  roleSpelling = {
    element = {
      payloadKey = "elemType";
      nested = v: { elemType = v; };
    };
    alternatives = {
      payloadKey = "elemType";
      nested = v: {
        left = head v;
        right = elemAt v 1;
      };
    };
    moduleSet = {
      payloadKey = "modules";
      nested = _v: { };
    };
  };

  roleOf =
    name: carries:
    let
      roles = attrNames carries;
    in
    if length roles != 1 then
      throw (
        "gen-merge: the type `${name}' declares ${toString (length roles)} carried roles ("
        + concatStringsSep ", " (map (r: "`${r}'") roles)
        + "); a type carries exactly one, because the foreign protocol has exactly one payload slot"
      )
    else if !(roleSpelling ? ${head roles}) then
      throw (
        "gen-merge: the type `${name}' carries the role `${head roles}', which this boundary has no "
        + "foreign spelling for. Add its payload key and introspection shape, or carry a known role"
      )
    else
      head roles;

  # ── THE IMPORT ENVIRONMENT ──────────────────────────────────────────────────────────────────────
  # gen-merge meets foreign option types BY CONSTRUCTION and in two directions at once: a gen type
  # mounted in a real `lib.evalModules` can face a same-named foreign type declared for the same
  # option, and the engine itself runs unmodified foreign types when a consumer injects them. Every
  # read of a foreign record goes through this half, so the engine and the vocabulary above never
  # have to know how the other side spells anything.

  # Did this type bring a FOLD OF ITS OWN, and if so what is it? The marker is consulted because the
  # export half publishes a leaf fold for every type that lacks one: past that point the presence of
  # a fold no longer answers "is this the type's own?", and the marker records the answer at the only
  # point that knew it. Absent marker reads as `false` — right for a genuinely foreign type, which
  # owns whatever fold it published.
  importedFold = t: if t ? merge && !(t._protoLeafMerge or false) then t.merge else null;

  # What value does this type supply when nothing defined it? `{ }` is "it declares none" and is a
  # different fact from `{ value = null; }`, which is a declared null.
  importedEmpty = t: if (t.emptyValue or { }) ? value then { inherit (t.emptyValue) value; } else { };

  importedDeprecation = t: t.deprecationMessage or null;

  # The value predicate, as a gen-shaped one. A gen leaf's own `check` is CURRIED and must never be
  # applied as `v -> bool`, which is why `verify` is preferred rather than merely tried first.
  importedAdmits =
    t:
    if t ? verify then
      (v: t.verify v == null)
    else if t ? check then
      t.check
    else
      null;

  # What this type wraps AT A GIVEN ROLE, whichever spelling it uses to say so. A gen type answers
  # from its own `carries`; a foreign one answers from its functor payload, which is the only place
  # the foreign protocol states a parameter it is willing to merge on.
  #
  # ★★ A FOREIGN PAYLOAD IS READ ONLY WHERE IT IS READ WHOLE, and this is the guard that keeps a
  # merge from truncating one. That payload is a ROW, and a row may state MORE than the one
  # parameter this side has a place for: nixpkgs' submodule carries `class`, `specialArgs`,
  # `shorthandOnlyDefinesConfig` and a description beside its modules, and its attribute container
  # carries laziness and a placeholder beside its element. Lifting just the key this side knows would
  # build a gen type out of a partner it did not understand and drop the rest with no diagnostic — so
  # a payload naming anything beyond the role's own key answers "nothing to merge on" instead. The
  # answer for a foreign container whose payload IS just the element is unchanged, which is what
  # keeps the two engines' one-parameter containers mutually legible.
  importedCarried =
    role: t:
    if t ? carries then
      t.carries.${role} or null
    else
      let
        payload = (t.functor or { }).payload or null;
        key = roleSpelling.${role}.payloadKey;
      in
      if payload == null || attrNames payload != [ key ] then null else payload.${key};

  # EVERY TYPE THIS ONE WRAPS, flattened, whichever vocabulary states it — a role may carry one type
  # or a positional list of them, and the foreign side says the same thing in its introspection alias.
  # For a walker that only wants to reach the wrapped types (the portable-subset lint's `functionTo`
  # scan is the consumer) this is the whole question, and asking it here is what keeps the alias's
  # name out of the walker.
  importedWrapped =
    t:
    let
      roles =
        if !(isAttrs t) then
          { }
        else if t ? carries then
          t.carries
        else
          t.nestedTypes or { };
    in
    prelude.concatMap (v: if isList v then v else [ v ]) (prelude.attrValues roles);

  # Does this element have a substructure of its own to substitute INTO? Presence, not truthiness — a
  # container rebuilding over a module set passes the set to its element, and an element with nothing
  # to substitute into rebuilds unchanged rather than aborting on a missing attribute. A bare
  # parametric constructor is not a record at all and has none, which is the true answer for it.
  importedRebuilds = t: isAttrs t && (t ? substructure || t ? substSubModules);

  # The three sub-protocol answers, as gen's `substructure`. A type that answers none of them is a
  # leaf and gets a leaf's three answers — it declares nothing, it has NO module-set concept (which
  # is what `null` says, and the only thing it says), and it has nothing to rebuild.
  importedSubstructure =
    t:
    if t ? substructure then
      t.substructure
    else
      {
        declares = t.getSubOptions or (_prefix: { });
        modules = t.getSubModules or null;
        rebuild = t.substSubModules or (_m: null);
      };

  # THE FOREIGN-PROTOCOL TYPE MERGE, which is where the engine reaches this half. A foreign partner
  # has no gen relation and never will, so the question "do these two merge?" is asked in the
  # protocol's own terms: the first type's `typeMerge` applied to the second's functor.
  importedMerge = a: b: if a ? typeMerge && b ? functor then a.typeMerge b.functor else null;

  # A partner type RECOVERED from its own functor. This is the whole reason gen's relation can stay
  # row-free: nixpkgs hands the second operand as a functor — a payload row both sides must agree on
  # — but `f.type` is by construction a function of `f`'s OWN payload, so reconstructing the partner
  # from its own functor is well-typed whatever shape that payload has, foreign or ours. The row is
  # consumed here and a TYPE is what leaves.
  importedPartner =
    f:
    if !(isAttrs f) || !(f ? type) || f.type == null then
      null
    else
      let
        payload = f.payload or null;
      in
      if payload == null then
        (if isFunction f.type then null else f.type)
      else if isFunction f.type then
        f.type payload
      else
        null;

  # importType — the inbound arm as one translation, for a foreign record entering this library
  # whole: a consumer's `mkOptionType` descriptor, or a leaf vocabulary injected in place of gen's.
  # PARTIAL, and its refusal is NAMED rather than `null`, the same shape the type-merge relation
  # uses: a caller that must report says what it could not import.
  #
  # ★ NO `typeMergeRel` IS SYNTHESISED, deliberately. A record arriving from the foreign side
  # carries the foreign answer to "do these merge?" and the engine keeps a foreign arm for exactly
  # that partner. A relation invented here would answer the question twice, and the two answers
  # could disagree.
  # ★★ THE SUB-PROTOCOL IS A REQUIRED FORMAL OF A WRAPPING TYPE, AND THE REFUSAL BELONGS HERE BECAUSE
  # THE RECORD IS WRITTEN IN THE FOREIGN PROTOCOL'S WORDS. A leaf's three answers — declares nothing,
  # no module-set concept, nothing to rebuild — are wrong for every type that wraps another, and a
  # wrapping type left on them reports "declares nothing" indistinguishably from a type that genuinely
  # declares nothing, so a consumer reflecting a declared surface off it fails CLOSED and silently.
  # The gen side states the same rule in its own words, at its own constructor; this arm exists
  # because a `mkOptionType` author wrote `substSubModules`, not `rebuild`, and a refusal that named
  # the field they did not write in a vocabulary they did not use would send them looking for the
  # wrong thing.
  #
  # THE DOMAIN IS WHAT THE RECORD SAYS IT CARRIES, read off the descriptor: an element type (either
  # spelling) or a module set that exists. It is deliberately NOT the functor payload — a payload is
  # what a type is willing to MERGE on, and a descriptor may carry an element without offering one.
  subProtocol = [
    "getSubOptions"
    "getSubModules"
    "substSubModules"
  ];
  carrierRefusal =
    t:
    let
      name = t.name or "raw";
      carriesElemType = t ? elemType || (t.nestedTypes or { }) ? elemType;
      carriesModuleSet = (t.getSubModules or null) != null;
      missing = filter (f: !(t ? ${f})) subProtocol;
    in
    # `||` short-circuits, and the order is load-bearing: a container's module set IS its element's,
    # so reading it to decide the domain would force the element type at construction.
    if !(carriesElemType || carriesModuleSet) || missing == [ ] then
      null
    else
      "gen-merge: the structural type `${name}' carries "
      + (if carriesElemType then "an element type" else "a module set")
      + " but does not supply "
      + concatStringsSep ", " (map (f: "`${f}'") missing)
      + "; a structural type may not inherit a leaf's protocol answer";

  importType =
    t:
    if !(isAttrs t) then
      {
        refused = "gen-merge: cannot import an option type from a ${builtins.typeOf t}; the boundary translates records, not values";
      }
    else if !(t ? name) && !(t ? verify) && all (f: !(t ? ${f})) exportFields then
      {
        refused = "gen-merge: cannot import `${concatStringsSep ", " (attrNames t)}' as an option type; it answers neither this library's vocabulary nor any field of the foreign protocol";
      }
    else if carrierRefusal t != null then
      { refused = carrierRefusal t; }
    else
      {
        imported =
          let
            name = t.name or "raw";
            fold = importedFold t;
            admits = importedAdmits t;
            deprecated = importedDeprecation t;
            payload = (t.functor or { }).payload or null;
            # The role a foreign payload is stating. `elemType` is the protocol's key for BOTH a
            # single wrapped type and a union's positional member list, and the two are told apart
            # by the only thing that distinguishes them: a member list is a LIST, a wrapped type is
            # a record.
            role =
              if payload == null then
                null
              else if payload ? modules then
                "moduleSet"
              else if payload ? elemType then
                (if isList payload.elemType then "alternatives" else "element")
              else
                null;
          in
          # WHAT THE FOREIGN PROTOCOL DID NOT SAY SURVIVES UNTOUCHED. Only the protocol's own names
          # are consumed here; a descriptor's other fields are the author's and are none of this
          # boundary's business, so they cross unread rather than being enumerated and lost.
          builtins.removeAttrs t (exportFields ++ [ "_protoLeafMerge" ])
          // {
            inherit name;
            whenEmpty = importedEmpty t;
            substructure = importedSubstructure t;
          }
          // (if t ? verify then { inherit (t) verify; } else { })
          // (if admits == null || t ? verify then { } else { inherit admits; })
          // (if fold == null then { } else { mergeDefs = fold; })
          // (if deprecated == null then { } else { inherit deprecated; })
          // (if t ? description then { inherit (t) description; } else { })
          // (
            if role == null then { } else { carries.${role} = payload.${roleSpelling.${role}.payloadKey}; }
          );
      };

  # ── THE EXPORT ENVIRONMENT ──────────────────────────────────────────────────────────────────────

  # The fold a type with none of its own publishes outward: one definition wins, or all definitions
  # agree, or the conflict is named. It is the foreign protocol's `mergeEqualOption` and it is
  # byte-identical to the engine's own leaf fold on the same definitions, which is what lets a type
  # carrying no fold cross without acquiring behaviour it did not have.
  leafFold =
    loc: defs:
    if defs == [ ] then
      throw "gen-merge: the option `${showOption loc}' has no definitions"
    else if length defs == 1 then
      (head defs).value
    else
      let
        first = (head defs).value;
      in
      if all (d: d.value == first) defs then
        first
      else
        throw "gen-merge: the option `${showOption loc}' has conflicting definitions";

  # exportType — a gen type EXPRESSED in the foreign protocol.
  #
  # ── THE PARTITION, AND IT IS TOTAL OVER THE FOURTEEN ────────────────────────────────────────────
  # DERIVED (10) — a real translation from a differently-named gen datum:
  #   check <- verify | admits · merge <- mergeDefs · emptyValue <- whenEmpty ·
  #   nestedTypes <- carries · deprecationMessage <- deprecated ·
  #   getSubOptions / getSubModules / substSubModules <- substructure ·
  #   typeMerge + functor <- typeMergeRel
  # FOREIGN CONSTANT (2) — no counterpart exists on this side, and that is the point:
  #   descriptionClass = null · _type = "option-type"
  # NAME-CARRIED (2) — carried or defaulted from the name, translating nothing:
  #   name · description
  # A field fitting none of the three is a finding, not a fourth class.
  #
  # ★ THE RESULT EXTENDS THE GEN RECORD RATHER THAN REPLACING IT, and that is forced rather than
  # convenient: the SAME value has to serve both engines — a consumer writes `types.listOf types.str`
  # from the published namespace and hands it to this library's own fold as readily as to a foreign
  # one. So what crosses is the gen record PLUS its foreign expression, and every protocol field is
  # derived here even where the record it extends happens to have crossed before.
  #
  # ★ A RELATION IS REQUIRED, not defaulted. A default invented at the boundary would be a merge rule
  # nobody in the vocabulary chose, answering for types whose author never said whether they merge.
  # The vocabulary states the relation, including its own default, and a record without one is
  # refused here by name.
  exportType =
    t:
    let
      name = t.name or "raw";
      sub = t.substructure or null;
      role = if t ? carries then roleOf name t.carries else null;
      spelling = if role == null then null else roleSpelling.${role};
      carried = if role == null then null else t.carries.${role};

      payload = if role == null then null else { ${spelling.payloadKey} = carried; };
      # Rebuild this type over a payload in the protocol's spelling — the inverse of the line above,
      # and the only inversion needed, because the role is fixed by the type rather than guessed.
      recarried = p: t.recarry { ${role} = p.${spelling.payloadKey}; };

      # `typeMerge` and `functor` are ONE derivation from ONE gen datum. The relation is row-free —
      # it takes the other TYPE — so the outbound half recovers a type from whatever functor arrives
      # and the inbound half publishes a functor a foreign engine can recover THIS type from.
      functor = {
        inherit name payload;
        type = if role == null then exported else (p: exportType (recarried p));
        binOp =
          if role == null then
            (_a: _b: null)
          else
            (
              a: b:
              let
                answer = (recarried a).typeMergeRel (recarried b);
              in
              if !(answer ? merged) || !(answer.merged ? carries) then
                null
              else
                { ${spelling.payloadKey} = answer.merged.carries.${role}; }
            );
      };

      exported = t // {
        _type = "option-type";
        descriptionClass = null;
        inherit name functor;
        description = t.description or name;
        deprecationMessage = t.deprecated or null;
        check =
          if t ? verify then
            (v: t.verify v == null)
          else if t ? admits then
            t.admits
          else
            (_: true);
        merge = if t ? mergeDefs then t.mergeDefs else leafFold;
        emptyValue = t.whenEmpty or { };
        nestedTypes = if role == null then { } else spelling.nested carried;
        getSubOptions = if sub == null then (_prefix: { }) else sub.declares;
        getSubModules = if sub == null then null else sub.modules;
        substSubModules = if sub == null then (_m: null) else sub.rebuild;
        typeMerge =
          f:
          let
            partner = importedPartner f;
          in
          if partner == null then null else (t.typeMergeRel partner).merged or null;

        # Not a fifteenth protocol field: gen's own record of whether the fold published above is
        # the type's or this boundary's. It exists BECAUSE the boundary exists — the export half
        # publishes a fold for every type, so past this point presence cannot answer the question —
        # and it is derived from the gen record's own `mergeDefs`, never defaulted true, because a
        # `true` marker outliving a real fold drops that fold silently. The engine no longer needs
        # it on the gen path, which reads `mergeDefs` directly; it is read on the FOREIGN path,
        # where a completed record stripped of its gen half would otherwise re-enter the core's own
        # fold through the type. The field retires with the completion, not with the engine's read.
        _protoLeafMerge = !(t ? mergeDefs);
      };
    in
    if !(t ? typeMergeRel) then
      throw (
        "gen-merge: the type `${name}' cannot be exported: it declares no type-merge relation, so "
        + "the foreign protocol's `typeMerge'/`functor' pair has no gen datum to be derived from. "
        + "Build it through the vocabulary's own constructor, which states the relation"
      )
    else
      exported;

  # refuseMount — the foreign protocol answered entirely by REFUSAL, for a value that is a nesting
  # seam rather than an option type.
  #
  # A missing attribute is a decision no one wrote down: handed to a real `lib.evalModules`, such a
  # value dies INSIDE the consumer on a missing attribute, an interpreter error naming a foreign line
  # and uncatchable by the caller. Completing the protocol would be the wrong repair — the boundary
  # is the eval and what crosses it is plain data, so a mountable nesting seam is crossing work, not
  # a gap in a type. Every field is therefore disposed of explicitly, and the three that are ANSWERED
  # are answered truthfully: such a value is not deprecated, supplies no value when the option
  # nesting it goes undefined, and wraps no element type. `_type` is deliberately absent — a consumer
  # that ASKS whether this is an option type reads it through `or null` and gets a correct `false`,
  # and a throwing tombstone would turn the one working negative answer into an abort.
  #
  # ★ THE FOLD IS ANSWERED, NOT REFUSED, and that is a fourth truthful answer rather than a crack in
  # the refusal. Such a value really does combine definitions that way — it is a nesting seam, and
  # the seam is a shipped capability — so refusing the field would delete a working answer to make a
  # point. It opens no mount either: the field a foreign engine forces FIRST is the module-set read,
  # which refuses before any fold is reached. The caller states it in gen's word and it is spelled in
  # the foreign protocol's here, which is the same trade every other field on this side makes.
  refuseMount =
    {
      name,
      reason,
      fold,
    }:
    let
      refuse =
        field: throw "gen-merge: `${name}' is not an option type and does not answer `${field}'; ${reason}";
    in
    {
      merge = fold;
      deprecationMessage = null;
      emptyValue = { };
      nestedTypes = { };

      check = refuse "check";
      description = refuse "description";
      descriptionClass = refuse "descriptionClass";
      functor = refuse "functor";
      getSubModules = refuse "getSubModules";
      getSubOptions = refuse "getSubOptions";
      substSubModules = refuse "substSubModules";
      typeMerge = refuse "typeMerge";
    };
in
{
  inherit
    exportClasses
    exportFields
    exportType
    importType
    importedAdmits
    importedCarried
    importedDeprecation
    importedEmpty
    importedFold
    importedMerge
    importedPartner
    importedRebuilds
    importedSubstructure
    importedWrapped
    refuseMount
    ;
}
