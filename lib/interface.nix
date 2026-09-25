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
  showConflict,
  mergeDescriptorDefault,
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
      typeMerge = "typeMergeRel | retainedRelation";
      functor = "typeMergeRel | retainedRelation";
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
  #
  # A foreign fold is the foreign engine's CHECKED merge: where the type states its domain as a
  # foreign `check` (and no `verify`, which marks a gen leaf whose `check` is curried and which the
  # spine already applies), every definition passes that `check` before the fold sees it — nixpkgs
  # `mergeDefinitions`' `checkedAndMerged`. The check wraps the descriptor's OWN fold, whichever
  # spelling states it, and reaches `leafFold` only for a descriptor that states none.
  #
  # A type whose `merge` carries `v2` is checked by the v2 PROTOCOL instead, as nixpkgs checks it:
  # its `check` is refused unless it is the coherent one the constructor shipped, and the verdict is
  # the `headError` its own merge computes, never the record's `check` (`v2Fold`). A submodule-bearing
  # v2 type keeps the checked fold, and an ad-hoc `check` on one is refused by name too: nixpkgs
  # rebuilds such a type at declaration (`substSubModules`), which erases the override silently, and a
  # silent erasure is the one answer this side does not reproduce (`adHocFold`).
  importedFold =
    t:
    if t._protoLeafMerge or false then
      null
    else if isV2 t && !(t.check.isV2MergeCoherent or false) then
      adHocFold t
    else if isV2 t && (t.getSubModules or null) == null then
      v2Fold t
    else if checksDefs t then
      checkedFold t (importedRawFold t)
    else
      importedRawFold t;

  # The same type's UNCHECKED fold: the foreign engine's raw `merge`, which nixpkgs calls with no
  # check, no coherence guard and no `headError` wherever it merges outside `mergeDefinitions` — the
  # freeformType site. `checkedFold` wraps it; `v2Fold` reads the same `merge` value's `v2` half.
  importedRawFold =
    t:
    if t._protoLeafMerge or false then
      null
    else if checksDefs t || isV2 t then
      t.merge or t.mergeDefs or leafFold
    else if t ? merge then
      t.merge
    else
      null;

  isV2 = t: (t.merge or { }) ? v2;
  checksDefs = t: t ? check && !(t ? verify);
  describe = t: if builtins.isString (t.description or null) then t.description else nameOf t;

  adHocFold =
    t: loc: _defs:
    throw "gen-merge: the option `${showOption loc}' has a type `${describe t}' that uses an ad-hoc `type // { check = ...; }' override, which ${
      if (t.getSubModules or null) == null then
        "the v2 merge protocol refuses"
      else
        "the foreign engine erases without a word when it rebuilds a submodule-bearing type"
    }; state the check with `addCheck' instead";

  # nixpkgs reads a v2 merge's answer through a CLOSED pattern, so an answer missing `headError` or
  # carrying anything beyond the three fields aborts there; it aborts here the same way.
  v2Result =
    {
      headError,
      value,
      valueMeta,
    }@r:
    r;

  v2Fold =
    t: loc: defs:
    let
      r = v2Result (t.merge.v2 { inherit loc defs; });
    in
    if r.headError != null then
      throw "gen-merge: a definition for option `${showOption loc}' is not of type `${describe t}'. TypeError: ${r.headError.message}"
    else
      r.value;

  checkedFold =
    t: fold: loc: defs:
    let
      bad = filter (d: !(t.check d.value)) defs;
    in
    if bad == [ ] then
      fold loc defs
    else
      throw "gen-merge: a definition for option `${showOption loc}' is not of type `${describe t}', in ${
        concatStringsSep ", " (map (d: "`${d.file}'") bad)
      }";

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

  # WHERE A TYPE DECLARES ITS ELEMENT, as the prefix it hands the element's declaration answer when
  # asked at `prefix`. The type is rebuilt over a probe element whose declaration answer IS the
  # prefix it was asked at, so the type's own `declares` states the path segment it adds: `attrsOf`
  # answers `prefix ++ [ "<name>" ]`, `listOf` `prefix ++ [ "*" ]`, a nullable `prefix` itself. No
  # name is consulted, so a wrapper this unit has never heard of answers for itself. `null` when the
  # type carries no single element or cannot be rebuilt over another in either vocabulary.
  #
  # A foreign payload stating MORE than the element (nixpkgs' attribute container carries laziness
  # and a placeholder beside it) is handed back to its own constructor WHOLE, with only the element
  # swapped. That reads no parameter this side has no place for — nothing is merged or dropped — so
  # `importedCarried`'s read-whole guard is not crossed: the answer is a location, not a type.
  importedElementPrefix =
    t: prefix:
    let
      probe = {
        substructure = {
          declares = p: p;
          modules = null;
          rebuild = _m: null;
        };
        getSubOptions = p: p;
      };
      key = roleSpelling.element.payloadKey;
      f = t.functor or { };
      payload = f.payload or null;
      rebuilt =
        if t ? carries then
          (if t.carries ? element && t ? recarry then t.recarry { element = probe; } else null)
        else if
          isAttrs payload && payload ? ${key} && !(isList payload.${key}) && isFunction (f.type or null)
        then
          f.type (payload // { ${key} = probe; })
        else
          null;
    in
    if rebuilt == null then null else (importedSubstructure rebuilt).declares prefix;

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

  # ── AN OPERAND'S NAME, AS A REFUSAL SAYS IT ─────────────────────────────────────────────────────
  # The one reader every refusal in this library names a merge operand through — gen's relations
  # (./types.nix), the parametric-leaf refusals (./default.nix), the declaration plane's reasons
  # (./modules.nix) and `foreignRel` below — and it lives here because this is the lowest unit all of
  # them reach. Total over anything that can arrive as a merge operand, whichever vocabulary built it.
  #
  # ★ TOTAL MEANS THE NAME IS READ, NEVER COERCED. An operand whose `.name` is not a string would
  # otherwise be interpolated, and a coercion error is not a throw: `tryEval` does not contain it, so
  # the refusal it belongs to would abort uncatchably instead of being reported. For such an operand
  # the discriminating fact is what its name IS.
  nameOf =
    t:
    if !(isAttrs t) then
      "<not a type>"
    else if !(t ? name) then
      "<unnamed>"
    else if builtins.isString t.name then
      t.name
    else
      "<a name of type ${builtins.typeOf t.name}>";

  # ── THE NAME THAT GOVERNED ──────────────────────────────────────────────────────────────────────
  # The foreign protocol keys a redeclaration on the FUNCTOR name, not the type name (`protoTypeMerge'
  # below, and the derived `typeMerge' in `exportType'). A type derived from another keeps its base's
  # `name', the value vocabulary its messages speak, and distinguishes only its functor. So a refusal
  # naming the pair by type name alone reads "`int' and `int'" in exactly the case the functor names
  # decided, which looks like a self-contradiction. Where both operands state a functor name and the
  # two differ, this answers them, read through `nameOf'; otherwise `null' and the refusal is
  # unchanged. A `nonMountable' operand's `functor' is itself a refusal (`refuseMount'), so it is not
  # read.
  functorNamesOf =
    a: b:
    let
      functorOf =
        x:
        if isAttrs x && !(x ? nonMountable) && isAttrs (x.functor or null) && x.functor ? name then
          x.functor
        else
          null;
      fa = functorOf a;
      fb = functorOf b;
    in
    if fa == null || fb == null || fa.name == fb.name then
      null
    else
      {
        first = nameOf fa;
        second = nameOf fb;
      };

  # ── THE DECIDABILITY PRE-CHECK THE FOREIGN MERGE IS GUARDED BY ──────────────────────────────────
  # A foreign `typeMerge` recurses through its own structure and bounds nothing: `types.json` is
  # self-referential, so `json.typeMerge json.functor` unfolds forever and dies with
  # `stack overflow; max-call-depth exceeded` — an interpreter error, NOT a `throw`, which escapes
  # `builtins.tryEval` and kills the evaluation rather than refusing. gen cannot bound a call once it
  # is inside foreign code, so the only available construction is to decline to make it: ask whether
  # the structure bottoms out BEFORE handing it over, and answer `null` — this binding's documented
  # "not mergeable" — when it does not.
  #
  # The walk is `lib/lint.nix`'s shipped `scanType` over the same accessor, deliberately: same
  # `importedWrapped`, same fuel shape, same named refusal at exhaustion. `importedWrapped` is the
  # boundary's own question ("what types does this one wrap"), answering `carries` for a gen record
  # and `nestedTypes` for a foreign one, so the walk asks in gen's vocabulary and not in nixpkgs'
  # spelling. It terminates by construction at `fuel` — a visited-set cycle guard is not available
  # here, because Nix has no reference equality and `==` on two distinct self-referential values
  # diverges the same way.
  #
  # ★ THE PRICE, STATED: a FINITE type nested `importedTypeWalkFuel` or more containers deep is
  # refused where an unguarded merge would have answered. The deepest real family measured in
  # nixpkgs' own vocabulary is 2, so the constant carries 16x headroom; raising it is a one-constant
  # change and this is the only site that states it.
  importedTypeWalkFuel = 32;

  importedDecidable =
    let
      go =
        fuel: t:
        if !(isAttrs t) then
          true
        else if fuel <= 0 then
          false
        else
          all (go (fuel - 1)) (importedWrapped t);
    in
    go importedTypeWalkFuel;

  # THE FOREIGN-PROTOCOL TYPE MERGE, which is where the engine reaches this half. A foreign partner
  # has no gen relation and never will, so the question "do these two merge?" is asked in the
  # protocol's own terms: the first type's `typeMerge` applied to the second's functor.
  #
  # BOTH operands are scanned, though only `a.typeMerge` drives the recursion and scanning `a` alone
  # is sufficient on every pair measured. It is one more bounded walk on a path that is already
  # deciding a merge, and it closes the second-operand question BY CONSTRUCTION rather than by a
  # census that would need re-running on every nixpkgs bump.
  importedMerge =
    a: b:
    if a ? typeMerge && b ? functor && importedDecidable a && importedDecidable b then
      joinKeepingOperands a b (a.typeMerge b.functor)
    else
      null;

  # ── THE WITNESS: A FOREIGN JOIN MAY NOT DROP WHAT AN OPERAND STATES ─────────────────────────────
  # A foreign `typeMerge` can answer a type that no longer states an operand's own check: nixpkgs'
  # `addCheck` is `elemType // { check = …; }`, so `ints.between`, `port` and `u8` keep `int`'s
  # functor and every join of them rebuilds bare `int` (nixpkgs' own docstring calls this "broken
  # behavior see #396021"). Passing that answer on is a silent drop, which ADR-0025 item 1 forbids.
  # So a foreign join is taken only where it keeps each operand's stated NAME at every depth the
  # operand wraps a type; otherwise the pair refuses.
  #
  # ★ REFUSE IS THE ONE ARM SOUND UNDER BOTH READINGS OF A REDECLARATION. Read as a join, `port ∥ int
  # → int` is an upper bound; read as a meet, it drops `port`'s check. Which reading a redeclaration
  # means is LEFT OPEN here, not settled: refusing is wrong under neither, and it keeps the standing
  # parity convention that gen-merge departs from nixpkgs by refusing (a README yardstick, not an ADR;
  # ADR-0025 item 1 alone would admit any value over the silent drop). A later ruling for the join reading re-admits subsumption pairs by relaxing this witness
  # alone. The witness compares the relation's ANSWER with each operand's own name, never one operand
  # with the other, so it keys no identity (ADR-0034 is scoped to IDENTITY).
  #
  # ★ THE WALK IS BY ROLE, KEYED ON THE OPERAND. A role the operand states and the join lacks is a
  # drop; a role the join GAINS is not, because an upper bound may wrap more than either operand.
  # nixpkgs has exactly two constructors whose wrapped-role set depends on data — `submoduleWith`
  # (`freeformType`, present only when stated) and `attrTag` (one role per tag) — and a union of
  # either grows. Positions are compared only within one role. Both records are first read in ONE
  # spelling, the foreign `nestedTypes` keys, through `roleSpelling.<role>.nested`: a gen `listOf`
  # states `element` where a foreign one states `elemType`, and without the normalisation that
  # legitimate mixed pair reads as a drop. A module set holds modules, not types, and spells as
  # nothing. The walk is fuel-bounded like `importedDecidable`, and exhaustion counts as a drop.
  #
  # ★ THE OPERAND IS READ IN THE JOIN'S VOCABULARY. A join this boundary built is a gen record, and a
  # gen record's roles are its `carries`, which is all its exported `nestedTypes` is derived from. A
  # foreign descriptor can state roles no payload carries across: `gen-schema`'s `refined`
  # keeps its base's `nestedTypes` under a `null` payload, `gen-aspects`' `aspectsRoot` states
  # `elemType` beside a payload that is the element itself. Read raw against such a join, a type
  # redeclared as ITSELF lacks a role only because the join could not spell it, and refuses. So
  # where the join is a gen record and the operand is not, the operand is read as the import
  # environment reads it; a record the import refuses stays raw. The residue, stated: a gen join
  # over a role no gen record can carry is judged at the relation that built it (`refined` asks
  # `mergeTypes` for its base), never here.
  joinRenames =
    let
      roles =
        x:
        if x ? carries then
          prelude.foldl' (acc: r: acc // roleSpelling.${r}.nested x.carries.${r}) { } (attrNames x.carries)
        else
          # `attrTag`'s `nestedTypes` is `tags` itself — OPTION RECORDS, one per tag, not types. An
          # option record carries no `.name` (`_type = "option"` only), so comparing it directly at
          # the next `go` call sees `null == null` and stops without reaching the type each tag
          # actually wraps. Read at its `.type` first; every other foreign `nestedTypes` site in
          # nixpkgs' `lib/types.nix` already carries types (`elemType`, `left`/`right`,
          # `freeformType`), so this is a no-op there.
          prelude.mapAttrs (_: v: if isAttrs v && (v._type or null) == "option" then v.type else v) (
            x.nestedTypes or { }
          );
      asList = v: if isList v then v else [ v ];
      inJoinSpelling =
        j: o:
        if isAttrs j && j ? typeMergeRel && isAttrs o && !(o ? typeMergeRel) then
          (importType o).imported or o
        else
          o;
      go =
        fuel: j: o':
        let
          o = inJoinSpelling j o';
        in
        if !(isAttrs j) || !(isAttrs o) then
          false
        else if fuel <= 0 then
          true
        else if (j.name or null) != (o.name or null) then
          true
        else
          let
            rj = roles j;
            ro = roles o;
          in
          prelude.any (
            r:
            !(rj ? ${r})
            || (
              let
                wj = asList rj.${r};
                wo = asList ro.${r};
              in
              length wj != length wo
              || prelude.any (i: go (fuel - 1) (elemAt wj i) (elemAt wo i)) (prelude.genList (i: i) (length wo))
            )
          ) (attrNames ro);
    in
    go importedTypeWalkFuel;

  # The witness's refusal as a REASON, for `mergeTypesReason`: it names the join, so an author sees
  # which type their relation answered and why that answer was not taken.
  #
  # ★ "NEITHER" IS SAID ONLY WHEN NEITHER OPERAND'S CHECK SURVIVED. `joinRenames j a` and
  # `joinRenames j b` are asked SEPARATELY, because a join that keeps one operand's name (`int ∥ port
  # → int`) drops only the other — "states neither declaration's own check" is false there, the join
  # states `int`'s. Only a fold step whose join renames past BOTH operands (`between ∥ between →
  # int`, `listOf int ∥ listOf port` at the wrapped role) truly states neither.
  importedMergeReason =
    a: b:
    let
      j = if a ? typeMerge && b ? functor then a.typeMerge b.functor else null;
      dropsA = j != null && joinRenames j a;
      dropsB = j != null && joinRenames j b;
      dropped =
        if dropsA && dropsB then
          "neither declaration's own check"
        else if dropsA then
          "the check `${nameOf b}' declares but not the check `${nameOf a}' declares"
        else
          "the check `${nameOf a}' declares but not the check `${nameOf b}' declares";
    in
    if dropsA || dropsB then
      "`${nameOf a}' and `${nameOf b}', which their own relation joins to `${nameOf j}', a type that states ${dropped}"
    else
      null;

  # ★ A PAIR THAT IS ONE REIFIED VALUE KEEPS THE OPERAND — ADR-0034's sealed limb, which compares "the
  # reified value itself" under Nix `==`: `port ∥ port` from one shared `types.port` answers `port`,
  # check intact. The clause is live on the `importedMerge` path only. On `foreignRel` the caller's raw
  # record meets the engine's imported partner and pointer identity does not survive the import, so a
  # shared imported twin refuses (README, Known byte-mode boundaries).
  joinKeepingOperands =
    a: b: j:
    if j == null then
      null
    else if !(joinRenames j a) && !(joinRenames j b) then
      j
    else if a == b then
      a
    else
      null;

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
  # ★ A `typeMergeRel' IS SYNTHESISED FOR A RECORD THAT STATED ONE, AND ONLY FOR THOSE. `foreignRel'
  # expresses the AUTHOR's own relation in gen's named-refusal shape; nothing is invented, which is
  # the whole difference from the nullary default. A record stating none still gets none — it carries
  # the foreign answer to "do these merge?" and the engine keeps a foreign arm for exactly that
  # partner, and a relation invented for it here would answer the question twice, with two answers
  # that could disagree.
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
      name = nameOf t;
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

  # The role a foreign payload is stating, or null when it states none. `elemType` is the protocol's
  # key for BOTH a single wrapped type and a union's positional member list, and the two are told
  # apart by the only thing that distinguishes them: a member list is a LIST, a wrapped type is a
  # record.
  #
  # ★ ONE DEFINITION, read twice — by the import below to populate `carries`, and by the refusal
  # above it to decide whether the payload was read AT ALL. A second copy of this decision would let
  # the boundary learn a spelling and go on refusing it, which is the drift the refusal exists to
  # prevent.
  payloadRole =
    payload:
    if payload == null then
      null
    else if payload ? modules then
      "moduleSet"
    else if payload ? elemType then
      (if isList payload.elemType then "alternatives" else "element")
    else
      null;

  # functorRefusal — a merge relation the author STATED and this boundary cannot read.
  #
  # A `functor` is the foreign protocol's way of saying what two types must agree on before they
  # merge: a parameter, and a `binOp` that decides whether two of them reconcile. `functor` is an
  # export field, so it comes off with the rest of the protocol's names — and only the PAYLOAD is
  # translated, only in the spellings above. A parameter this side cannot read is therefore dropped
  # together with the `binOp` that judged it, and the type falls back to the vocabulary's nullary
  # relation: merge any two of this NAME, blind to the parameter. That is STRICTLY MORE PERMISSIVE
  # than what the author wrote, it is reached without a throw, a red cell or a warning, and it is
  # exactly the unenumerated silent exception ADR-0025 §1 forbids — every operation returns a value
  # or a NAMED refusal. So it is named.
  #
  # ★★ THE PREDICATE IS THE INFORMATION-LOSING CASE, NOT THE BARE PAYLOAD, and both conjuncts are
  # load-bearing. The foreign relation and the nullary one COINCIDE when there is nothing to
  # discriminate on: `defaultTypeMerge` over a functor stating neither `payload` nor `wrapped` is
  # name equality, and so is `nullaryRel`. A caller supplying a functor for protocol completeness
  # alone — the shape a metadata decoration wants, and the shape every nullary foreign leaf already
  # arrives in — therefore loses NOTHING and is not refused. Drop the parameter conjunct and every
  # nixpkgs-shaped descriptor in the ecosystem is refused for nothing; drop the `binOp` conjunct and
  # the refusal fires where no relation was ever stated to be lost.
  functorRefusal =
    t:
    let
      name = nameOf t;
      f = t.functor or null;
      payload = if f == null then null else f.payload or null;
      # BOTH slots the foreign protocol states a parameter in. `wrapped` is the older spelling and
      # this side reads neither it nor an unrecognised payload, so a functor using it loses its
      # parameter the same way — the refusal is over what was STATED, not over which slot said it.
      statesParameter = payload != null || (f != null && (f.wrapped or null) != null);
    in
    # ★★ A STATED `binOp' IS NO LONGER LOST, SO THE REFUSAL NO LONGER FIRES FOR IT. The paragraph
    # above is the reason this check existed: the relation came off with the protocol's names and the
    # type fell back to the nullary one. `importType' now RETAINS the pair and installs the author's
    # own relation, so there is nothing to lose and nothing to name. What survives is the case the
    # refusal is still true of — a functor that states the relation SLOT and leaves it empty, where
    # there is a parameter to discriminate on and nothing stated to discriminate with.
    if
      f == null
      || !(f ? binOp)
      || !statesParameter
      || payloadRole payload != null
      || (f.binOp or null) != null
    then
      null
    else
      "gen-merge: the option type `${name}' supplies a `functor' this boundary cannot read: its "
      + "parameter is stated as neither `payload.elemType' nor `payload.modules', so the parameter "
      + "and the `binOp' that discriminates on it are discarded and `${name}' merges on its NAME "
      + "ALONE — accepting two operands its own `binOp' refuses. State the parameter as "
      + "`functor.payload.elemType' (or `.modules'), or drop the `functor' if merging on the name "
      + "alone is what this type means";

  # protoTypeMerge — the foreign protocol's OWN generic type-merge combinator, transcribed.
  #
  # A caller states its merge relation as a `functor': a parameter, and a `binOp' that decides
  # whether two of them reconcile. The `typeMerge' ACCESSOR is not a second statement of that
  # relation — it is DERIVED from it, and the foreign `mkOptionType' is what derives it. A descriptor
  # written against this boundary directly therefore arrives with the relation and without the
  # accessor, and supplying the derivation here is what makes the two spellings mean the same thing
  # instead of one of them silently meaning less.
  #
  # ★★ IT IS NOT A PER-NAME TABLE, and that is what makes transcribing it closed rather than a
  # standing debt. Read at the primary — nixpkgs `lib/types.nix', `defaultTypeMerge' — it dispatches
  # on functor NAME EQUALITY, then calls the caller's own `binOp' and `type'. It carries no knowledge
  # of any particular type, so this boundary can supply the protocol's default without learning the
  # vocabulary it is defaulting for.
  #
  # ★ ONE DELIBERATE DIVERGENCE, stated rather than transcribed silently: where the two functors
  # disagree on whether there is a payload at all, nixpkgs `assert's the symmetry and this returns
  # `null'. An abort a consumer survives only by having wrapped the force in `tryEval (deepSeq …)' is
  # exactly the shape `refuseMount' below exists to convert into a value the algebra can act on.
  protoTypeMerge =
    f: f':
    if f.name != (f'.name or null) then
      null
    else if (f.payload or null) == null then
      (if (f'.payload or null) == null then f.type else null)
    else if (f'.payload or null) == null then
      null
    else
      let
        mergedPayload = f.binOp f.payload f'.payload;
      in
      if mergedPayload == null then null else f.type mergedPayload;

  # The caller's stated relation, however they stated it: their derived accessor where they had one,
  # the protocol's own default over their `functor' where they did not.
  callerTypeMerge = t: t.typeMerge or (protoTypeMerge t.functor);

  # ★★ THE PREDICATE IS THE RELATION THE CALLER STATED, NEVER THE ACCESSOR DERIVED FROM IT. Keying on
  # `typeMerge' asks "did some other library's `mkOptionType' build this record", which is a fact
  # about the descriptor's provenance and not about what its author said. Keying on `functor.binOp'
  # asks the question this boundary is actually deciding.
  statesRelation = t: ((t.functor or { }).binOp or null) != null;

  # ★★ WHAT THE PROTOCOL'S OWN DEFAULT READS OFF A FUNCTOR, AS ONE DEFINITION READ TWICE — by the
  # retention in `importType' to decide what may be retained, and by the refusal beside it to name
  # what may not. `protoTypeMerge' reads `name' and `type' off the caller's functor directly and
  # APPLIES `type' to a merged payload; a functor retained without them is one this boundary
  # republishes and then cannot apply, and the gap surfaces as a bare interpreter abort at a merge
  # site far from the record that caused it. A second copy of this decision would let the two arms
  # drift and re-open exactly that gap, which is why `payloadRole' above is written the same way.
  relationGaps =
    f:
    if f == null || (f.binOp or null) == null then
      [ ]
    else
      (if f ? name then [ ] else [ "name" ])
      ++ (if f ? type && ((f.payload or null) == null || isFunction f.type) then [ ] else [ "type" ]);

  # relationRefusal — a relation STATED and unusable. It is the COMPLEMENT of `functorRefusal' over
  # the same records: the two partition "supplies a functor" on `binOp', the other answering for a
  # relation slot left empty beside a parameter this boundary cannot read, this one for a relation
  # stated with a functor that cannot answer for it. Neither can fire for the same record.
  relationRefusal =
    t:
    let
      gaps = relationGaps (t.functor or null);
    in
    if gaps == [ ] then
      null
    else
      "gen-merge: the option type `${nameOf t}' states a merge relation in `functor.binOp' "
      + "but its `functor' does not answer "
      + concatStringsSep ", " (map (g: "`${g}'") gaps)
      + "; the relation is retained verbatim and applied by the protocol's own default, which reads "
      + "them off it. Supply them, or drop `functor.binOp' if merging on the name alone is what this "
      + "type means";

  # foreignRel — the caller's stated relation, expressed as gen's own row-free relation so the engine
  # reads the AUTHOR's answer rather than the vocabulary's nullary one. The refusal names the
  # discriminating fact: it is the author's own `functor' that declined to reconcile the pair, not
  # this boundary's inability to read it. An author's answer is held to the same witness as an
  # inherited one, and a join the witness declines is named as that, not as a declined reconciliation.
  foreignRel =
    t: other:
    let
      f = if isAttrs other then other.functor or null else null;
      joined = if f == null then null else callerTypeMerge t f;
      answer = joinKeepingOperands t other joined;
      tName = nameOf t;
      otherName = nameOf other;
      functorNames = functorNamesOf t other;
      pair = "`${tName}' and `${otherName}'";
      # Same asymmetry `importedMergeReason` names above: `t` and `other` are asked separately, and
      # "neither" is said only when the join renamed past both.
      dropsT = joined != null && joinRenames joined t;
      dropsOther = joined != null && isAttrs other && joinRenames joined other;
      dropped =
        if dropsT && dropsOther then
          "neither declaration's own check"
        else if dropsT then
          "the check `${otherName}' declares but not the check `${tName}' declares"
        else
          "the check `${tName}' declares but not the check `${otherName}' declares";
    in
    if answer == null && joined != null then
      {
        refused = "${pair}, which the first type's own `functor' joins to `${nameOf joined}', a type that states ${dropped}";
      }
    else if answer == null && functorNames != null then
      {
        refused = "${pair}, which the first type's own `functor' (named `${functorNames.first}') does not reconcile with the second's (named `${functorNames.second}')";
      }
    else if answer == null then
      { refused = "${pair}, which the first type's own `functor' does not reconcile"; }
    else
      { merged = answer; };

  # importDescriptor — a `mkOptionType` DESCRIPTOR, imported with the constructor's default fold, as
  # nixpkgs' `mkOptionType` takes `merge ? mergeDefaultOption`. The default is the CONSTRUCTOR'S, not
  # the protocol's (a finished record always states `merge`), so it is applied here and not in
  # `importType`, which also serves `importLeaf` and the engine's `ownFold`. It applies where
  # nixpkgs' would, to a descriptor stating the one required formal, `name`; without that guard a
  # record answering neither vocabulary would gain a fold and stop being refused. A descriptor
  # stating a fold in either vocabulary is imported as written, and so is one stating `verify` — a
  # gen leaf, whose no-fold default stays the engine's `mergeLeaf` (den-hoag-sezf R-4).
  #
  # ★ The guard is decided HERE, before `importType` is entered, and not passed to it as a thunk.
  # Forcing the descriptor inside `importType` would put this frame under every level of a chain of
  # descriptors built from descriptors (gen-schema's `refined` over a refined base), one call deeper
  # per level: measured, gen-schema's 1500-deep refinement chain then overflowed `max-call-depth`
  # where it stood refused by name.
  importDescriptor =
    d:
    if isAttrs d && d ? name && !(d ? merge) && !(d ? mergeDefs) && !(d ? verify) then
      importType (d // { merge = mergeDescriptorDefault; })
    else
      importType d;

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
    else if functorRefusal t != null then
      { refused = functorRefusal t; }
    else if relationRefusal t != null then
      { refused = relationRefusal t; }
    else
      {
        imported =
          let
            name = t.name or "raw";
            fold = importedFold t;
            # Where the fold is CHECKED, the unchecked one it guards rides ON it, for the one site that
            # merges without checking (the freeformType); a caller replacing `mergeDefs` whole replaces
            # both at once, as with `mergeDefs.reported`.
            checked = isV2 t || checksDefs t;
            admits = importedAdmits t;
            deprecated = importedDeprecation t;
            payload = (t.functor or { }).payload or null;
            role = payloadRole payload;
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
          // (
            if fold == null then
              { }
            else if checked then
              {
                mergeDefs = {
                  __functor = _: fold;
                  unchecked = importedRawFold t;
                };
              }
            else
              { mergeDefs = fold; }
          )
          // (if deprecated == null then { } else { inherit deprecated; })
          // (if t ? description then { inherit (t) description; } else { })
          // (if role == null then { } else { carries.${role} = payload.${roleSpelling.${role}.payloadKey}; })
          # ★★ THE AUTHOR'S RELATION IS RETAINED UNDER A GEN NAME, NOT UNDER THE PROTOCOL'S. What the
          # author stated about how this type merges is not the protocol's to take back — stripped
          # with the rest, the record has no relation and the vocabulary supplies its nullary one,
          # which is strictly more permissive than what was written. But retaining it under
          # `functor'/`typeMerge' would leave the export half reading a gen field of a DERIVED
          # FIELD'S OWN NAME, which is the one thing C-2 says the boundary never does. Retained under
          # a gen name, the export derives from a differently-named datum like every other field, and
          # PRESENCE OF THIS FIELD is what says the relation came from an author across the boundary —
          # structural provenance rather than a naming coincidence (ADR-0034's shape, at the boundary
          # instead of the mint). The two members travel as ONE datum because a record carrying one
          # without the other is a state that cannot occur.
          // (
            if statesRelation t then
              {
                typeMergeRel = foreignRel t;
                retainedRelation = {
                  # Verbatim, and its NAME governs: what the author called this type is the merge
                  # identity the foreign engine keys on.
                  inherit (t) functor;
                  # Theirs where they derived one, the protocol's own default over their `functor'
                  # where they did not — resolved HERE, so nothing downstream re-asks the question.
                  typeMerge = callerTypeMerge t;
                };
              }
            else
              { }
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
      if all (d: d.value == first) defs then first else throw (showConflict loc defs);

  # isOptionType — the DUAL of the `_type = "option-type"` stamp `exportType` applies below, asked
  # here rather than spelled at the asking site. The engine needs it at the declaration boundary,
  # where a bare type standing in an option-DECLARATION position is a caller mistake to be refused by
  # name rather than recursed into (`declPlaneMisuseTag`, ./modules.nix). The tag is a FOREIGN
  # CONSTANT with no counterpart on gen's side, so it is uttered in this unit and nowhere else —
  # `ci/tests/interface.nix`'s `test-the-option-type-tag-is-uttered-in-exactly-one-unit` asserts the
  # exact file list, and a second file naming the literal fails it by name.
  isOptionType = v: isAttrs v && (v._type or null) == "option-type";

  # exportType — a gen type EXPRESSED in the foreign protocol.
  #
  # ── THE PARTITION, AND IT IS TOTAL OVER THE FOURTEEN ────────────────────────────────────────────
  # DERIVED (10) — a real translation from a differently-named gen datum:
  #   check <- verify | admits · merge <- mergeDefs · emptyValue <- whenEmpty ·
  #   nestedTypes <- carries · deprecationMessage <- deprecated ·
  #   getSubOptions / getSubModules / substSubModules <- substructure ·
  #   typeMerge + functor <- typeMergeRel | retainedRelation
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
  # derived here — EXCEPT the relation pair of a record that crossed STATING one, which is retained
  # under a gen name and republished. This sentence's own clause about a record that "happens to have
  # crossed before" was written when there was no such case; now there is exactly one.
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
      role = if t ? carries then roleOf (nameOf t) t.carries else null;
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
        inherit name;
        # ★★ THE CALLER'S FUNCTOR IS REPUBLISHED WITH ITS NAME INTACT, AND THAT NAME GOVERNS. The
        # derivation above is what a type with no stated relation is published as; overwriting a
        # stated one with it is name-only identity re-imposed at a KEYING site with the
        # distinguishing content available (ADR-0034), and it is what makes a refinement merge with
        # the base it exists to be distinguished FROM. Preserving it fails closed instead.
        # It is read off `retainedRelation', a differently-named gen datum, exactly as every other
        # derived field is read off one — see the retention site in `importType' for why.
        functor = t.retainedRelation.functor or functor;
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
        # Derived from the gen datum only where there is no stated relation to derive it FROM.
        # Where the caller stated one, theirs is what the foreign engine must see — deriving over it
        # would shadow the relation the two clauses above went to the trouble of retaining.
        #
        # ★★ THE FUNCTOR NAMES MUST AGREE FIRST, AND THAT CLAUSE CANNOT MOVE INTO THE RELATION. The
        # relation is row-free — `importedPartner' consumes the row and a TYPE is what leaves — so by
        # construction the relation never sees the arriving functor's NAME, and the vocabulary's
        # nullary default falls back to comparing the partner TYPE's name instead. The two coincide
        # for every type this library builds (the functor above is minted from `name'), which is why
        # substituting one for the other is invisible from inside. They DIVERGE for the case this
        # protocol exists to serve: a consumer that DERIVES a type from one of ours keeps the base's
        # `name' — the value vocabulary its error messages still speak — and distinguishes only the
        # FUNCTOR, which is the axis a redeclaration is keyed on. Compared on the type name, such a
        # type merges with its own base and the derivation is silently dropped; a refined `int'
        # redeclared as a bare `int' answers `int' with the refinement gone, which is the fail-OPEN
        # answer every named refusal in this file exists to prevent.
        # This is the SAME first clause `protoTypeMerge' already states for the retained arm, and the
        # retention site above says it in words: what the author called this type is the merge
        # identity the foreign engine keys on. One law, now read on both arms.
        typeMerge =
          t.retainedRelation.typeMerge or (
            f:
            let
              partner = importedPartner f;
            in
            if (f.name or null) != functor.name then
              null
            else if partner == null then
              null
            else
              (t.typeMergeRel partner).merged or null
          );

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
        "gen-merge: the type `${nameOf t}' cannot be exported: it declares no type-merge relation, so "
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
  # are answered truthfully: such a value is not deprecated, supplies the caller's `whenEmpty` when
  # the option nesting it goes undefined, and wraps no element type. `_type` is deliberately absent —
  # a consumer that ASKS whether this is an option type reads it through `or null` and gets a correct
  # `false`, and a throwing tombstone would turn the one working negative answer into an abort.
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
      whenEmpty,
    }:
    let
      refuse =
        field: throw "gen-merge: `${name}' is not an option type and does not answer `${field}'; ${reason}";
    in
    {
      merge = fold;
      deprecationMessage = null;
      emptyValue = whenEmpty;
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
    importDescriptor
    importType
    importedAdmits
    importedCarried
    importedDecidable
    importedDeprecation
    importedElementPrefix
    importedEmpty
    importedFold
    importedMerge
    importedRawFold
    importedMergeReason
    joinRenames
    nameOf
    functorNamesOf
    importedPartner
    importedRebuilds
    importedSubstructure
    importedTypeWalkFuel
    importedWrapped
    isOptionType
    refuseMount
    ;
}
