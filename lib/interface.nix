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
  # The nested tree's door and gen's own containers (den-hoag-n6dh7 items 5, 7), each read lazily:
  # the engine above supplies both, closing a loop this unit otherwise keeps a chain.
  nestedTreeAt,
  mergeDefsThreaded,
  constructors,
  # gen-types' library, for the check-witness protocol it owns (`witnessRecord`, `rewritesCheck`):
  # this unit builds and reads the witness through it and defines neither (den-hoag-ydro3).
  types,
}:
let
  inherit (prelude)
    attrNames
    concatStringsSep
    elemAt
    filter
    head
    isAttrs
    isList
    length
    all
    map
    ;
  # The two readers are the BUILTINS, stated rather than taken from gen-prelude: gen-prelude's
  # `isFunction`/`functionArgs` became nixpkgs' functor-aware readers (den-hoag-7gp66 P2-OQ15 arm
  # (i)), and every site here keeps the meaning it had, a functor read as an attrset. Adopting
  # nixpkgs' functor-aware parity is gen-merge's own P2 unit's change, with its cells.
  inherit (builtins) isFunction;
  inherit (types) rewritesCheck witnessRecord;

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
      nestedTypes = "carries | unroledNested";
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

  # ── THE COMPARISON SUBJECT OF A VALUE THAT CAN CARRY A TYPE RECORD (den-hoag-bfc0k) ────────────
  # An exported record is CYCLIC — `exportType` publishes `functor.type` as the record itself — and
  # Nix `==` walks an attrset in symbol-interning order, so a bare `==` between two distinct records
  # recurses until the evaluator aborts, uncatchably, whenever `functor` is interned before the first
  # attribute on which they differ. The subject puts each record's CLOSURES first: the fields of
  # `exportFields` that the record holds as functions, one attrset per record, ahead of the value
  # itself. List `==` decides index 0 before index 1, and `==` on two functions never enters either
  # closure, so two constructions — which differ in a closure, every `exportType` call deriving its
  # own `typeMerge` — answer `false` before the back-edge can be reached. The prefix selects from the
  # value, keeping every slot: one `==` over a subject that CONTAINS the reified value (ADR-0034's
  # compared limb), never a projection in its place. It is a redundant conjunct for every value
  # whose listed fields evaluate, and for no other (below).
  #
  # `records` are the type records sitting at positions the caller's grammar declares — `[ v ]` when
  # `v` is one. The field set is read off `exportFields`, so the protocol's names stay in this unit.
  #
  # ★ ENUMERATED EXCEPTION TO TOTALITY (ADR-0025 item 1). The `==` can still abort, depending on
  # interning order, where the prefix is EQUAL and the value then reaches a back-edge before a
  # difference: (1) a GRAFT — every closure slot shared and another attribute holding distinct
  # cyclic data, which only a hand `//` of such data onto one construction produces; (2) a record at
  # a position `records` does not name, which caller content open to any shape can hold. (2) is not
  # a contrived position: it is ORDINARY MODULE CONTENT — a module in a component whose grammar
  # fixes no record position (declared `records = [ ]`), or a facet's `module`, that declares an
  # option typed by a per-call `mkOptionType`. Two such components abort in the order that interns
  # `functor` first, and in every order when the type carries a back-edge under `description`.
  # Closing either needs an evaluator-observable value identity (a visited set), which pure Nix does
  # not expose; a walk that collected every record would force content the slot shortcut skips and
  # so change which values compare equal.
  #
  # ★ ENUMERATED VALUE MOVE (not an abort). The prefix forces each listed field to WHNF before the
  # value is compared, so a record whose listed field throws propagates that throw where a bare `==`
  # would have decided on another attribute first: two declarations `g` and `g // { typeMerge =
  # throw …; }` merged on the name before `mkOptionType`'s relation compared through this subject,
  # and are now the throw, in both orders.
  #
  # A member of `records` that is not an attrset carries no closures and contributes `{ }`: a grammar
  # position declared to hold a type can hold a caller's string or lambda (`type = "str"`, the NixOS
  # spelling), and `intersectAttrs` over it is an evaluator type error that `tryEval` does not catch
  # (den-hoag-6b5ia). Such a value has no back-edge, so the `==` over `v` decides it.
  closuresOf =
    r:
    if !(isAttrs r) then
      { }
    else
      builtins.intersectAttrs (builtins.listToAttrs (
        map (n: {
          name = n;
          value = null;
        }) (builtins.filter (n: r ? ${n} && isFunction r.${n}) exportFields)
      )) r;
  closuresFirst = records: v: [
    (map closuresOf records)
    v
  ];

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
    # gen-types' `rewritesCheck`, restated inline for cost: a call here is an environment on every
    # leaf fold. The construction door holds this spelling to the protocol (`lib/default.nix`).
    if t ? _checkWitness && t ? check && t.check != t._checkWitness then
      carriedFold t (t.mergeDefs or leafFold)
    else if t._protoLeafMerge or false then
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
    if rewritesCheck t then
      t.mergeDefs.unchecked or t.mergeDefs or leafFold
    else if t._protoLeafMerge or false then
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

  # ── A CHECK A FOREIGN WRAPPER STATED OVER A GEN RECORD (den-hoag-4ifgb) ─────────────────────────
  # On this side a type's domain is a gen datum (`verify` | `admits`) and the published `check` is
  # derived from it; nixpkgs refines a domain on the descriptor (`addCheck t p`, `t // { check }`),
  # so a gen record so wrapped states its domain twice and the two disagree. `exportType` binds its
  # `check` once and publishes it beside `_checkWitness`, which holds the same value, so a rewritten
  # `check` is detected BY CONSTRUCTION, never by comparing functions. The protocol is gen-types':
  # `witnessedCheck` builds the pair and `rewritesCheck` is the test (den-hoag-ydro3, owner-ruled
  # arm (ii)), and this unit defines neither. The published `check` is a
  # functor RECORD, as nixpkgs publishes its own v2 checks (`{ __functor; isV2MergeCoherent; }`, the
  # same device for the same question: was this `check` rewritten by `// { check }`?), and the
  # witness is that same record, so `==` meets one set of bindings and answers by the pointers of
  # its slots, allocating nothing per test: the test is paid on every fold, so it may cost nothing
  # per fold (hub perf-bench's `wideFreeform` and `deepSubmodule` alloc ratchets). A rewritten
  # `check` is a function (`addCheck`'s `x: t.check x && p x`) or another record's, and compares
  # unequal. A record with no witness (a `nonMountable` tree, a foreign descriptor) is not asked,
  # so the tree's refusing `check` is never forced here; a check rewritten over the bare tree is
  # therefore not detected, and nixpkgs erases it there too (the enumerated residue, README "The
  # prices, stated"). A record re-bound by selection (`t // { inherit (t) check; }`) keeps the same
  # record and reads as its own on every evaluator. Four per-fold sites restate the test inline for
  # cost (`importedFold`, `modules.nix` `ownFold` and `threadedAs`, `types.nix` `isValid`), and the
  # library's construction door holds their spelling to this test (`lib/default.nix`).

  # Whether a record's published `check` reads a `nonMountable` record's, which refuses when forced.
  # A union's `check` reads its members and a nullable's its element, in gen's vocabulary and in
  # nixpkgs'; a container's (`listOf`, `attrsOf`, `submodule`) reads only the value's shape (nixpkgs
  # 7a0f122: `isList`, `isAttrs`), so it never reaches what it holds. Keyed on the name, as a stock
  # record is recognised (`importedRehomeAt`), and bounded by the walk's fuel.
  checkReadsTree =
    let
      go =
        fuel: t:
        isAttrs t
        && (
          t ? nonMountable
          || (
            fuel > 0
            && (
              if nameOf t == "either" then
                (
                  let
                    members = importedCarried "alternatives" t;
                  in
                  isList members && prelude.any (go (fuel - 1)) members
                )
              else if nameOf t == "nullOr" then
                go (fuel - 1) (importedCarried "element" t)
              else
                false
            )
          )
        );
    in
    go importedTypeWalkFuel;

  # The fold a record with a rewritten `check` folds by: `fold` under that check, as nixpkgs'
  # `checkDefsForError` applies it (the same verdict), or, where the check reads a nested tree's
  # foreign face and so cannot be evaluated in this eval, a refusal by name. Dropping it silently is
  # the one answer this side does not give (ADR-0025 item 1).
  carriedFold =
    t: fold:
    if checkReadsTree t then (loc: _defs: throw (rewrittenCheckRefusal t loc)) else checkedFold t fold;
  rewrittenCheckRefusal =
    t: loc:
    "gen-merge: the option `${showOption loc}' has a type `${nameOf t}' whose `check' a foreign wrapper rewrote (`addCheck', or `// { check = ...; }') over a member holding a nested module tree; the rewritten check reads that tree's foreign face, which is not an option type, so it cannot be evaluated here and is refused rather than dropped. State the check on a member that holds no tree, or inside the submodule";

  # Whether a value is inside a record's rewritten `check` as well as its gen domain: the member
  # choice of a union asks both (`types.isValid`). A check that cannot be evaluated is not asked,
  # and the member's fold refuses it by name (`carriedFold`).
  admitsCarried = t: v: !(rewritesCheck t) || checkReadsTree t || t.check v;

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
  # from its own `carries`; a foreign one from the carrying spellings `statedRoles` reads, the one
  # source the import fills `carries` from. Never from its functor payload: a payload is what a type
  # offers to MERGE on (`importedOffered` below), not what it carries.
  importedCarried =
    role: t: if t ? carries then t.carries.${role} or null else (statedRoles t).${role} or null;

  # What this type OFFERS TO MERGE ON at a given role: the parameter of the relation it merges by.
  # A gen type's relation is derived from its `carries`, so it offers what it carries; a type that
  # crossed STATING its own relation offers that relation's payload, which is not what it carries
  # (a refinement carries its base's element and offers nothing); a foreign one offers its functor
  # payload. A payload is read WHOLE and in its role's own shape, or it offers nothing.
  importedOffered =
    role: t:
    let
      payload =
        if t ? retainedRelation then
          t.retainedRelation.functor.payload or null
        else if t ? carries then
          null
        else
          (t.functor or { }).payload or null;
      key = roleSpelling.${role}.payloadKey;
    in
    if t ? carries && !(t ? retainedRelation) then
      t.carries.${role} or null
    else if payload == null || attrNames payload != [ key ] || payloadRole payload != role then
      null
    else
      payload.${key};

  # WHERE A TYPE DECLARES ITS ELEMENT, as the prefix it hands the element's declaration answer when
  # asked at `prefix`. The type is rebuilt over a probe element whose declaration answer IS the
  # prefix it was asked at, so the type's own `declares` states the path segment it adds: `attrsOf`
  # answers `prefix ++ [ "<name>" ]`, `listOf` `prefix ++ [ "*" ]`, a nullable `prefix` itself. No
  # name is consulted, so a wrapper this unit has never heard of answers for itself. `null` when the
  # type carries no single element or states no rebuild.
  #
  # ★ ONLY A GEN RECORD'S `recarry` REBUILDS IT. A raw foreign record states no rebuild, and its
  # functor payload is what it offers to MERGE on: handing that back to its constructor with the
  # element swapped would read the payload to learn where the record carries, which the payload does
  # not say (`importedCarried`). Such a record answers `null`, a position it does not state.
  #
  # THE PROBE IS NOT A TYPE RECORD: it has no `_type`, `name`, `check` or `merge`. A `recarry` that
  # reads its element when it is BUILT (rather than when it merges) throws here, and the warm read
  # that asked throws with it where cold serves. None of gen's element carriers does. The cost is
  # one type rebuild and one `declares` call per ask, paid by the identity walk once per declared
  # container position (per entry inside a registry element); a leaf never reaches it.
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
      rebuilt =
        if t ? carries && t.carries ? element && t ? recarry then t.recarry { element = probe; } else null;
    in
    if rebuilt == null then null else (importedSubstructure rebuilt).declares prefix;

  # WHETHER A FOREIGN TYPE HOLDS ITS MODULE SET AT ITS OWN POSITION, read off the declaration it hands
  # back when asked at `prefix`. `getSubModules` says which module set a type is built from, not where
  # its instances sit: nixpkgs' `listOf`/`attrsOf`/`attrListOf`/`functionTo` forward their element's
  # set, and `coercedTo` its final type's. The foreign protocol stamps every option record it builds
  # with its `loc`, so the placement is stated by the declaration stratum itself: the set sits at
  # `prefix` iff some option of `decl` is located at `prefix` followed by its own path in `decl`. A
  # container's options sit one placeholder segment below (`*`, `<name>`, `<function body>`) and none
  # qualifies. An option record stating no `loc` states no placement. `any`, not the first leaf: a
  # freeform submodule's `_freeformOptions` sits below its placeholder beside options that sit at
  # `prefix`.
  importedHeldAt =
    prefix: decl:
    let
      go =
        rel: d:
        if isAttrs d && (d._type or null) == "option" then
          (d.loc or null) == prefix ++ rel
        else
          isAttrs d && prelude.any (k: go (rel ++ [ k ]) d.${k}) (attrNames d);
    in
    go [ ] decl;

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
        else if evaluatesOwnRoles t then
          { }
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
        # A field read only in its protocol's shape: a `getSubOptions` that cannot be called states
        # no declaration, and calling it would abort where the fold never reads it. Callable is a
        # lambda or a functor set, as the foreign protocol's own reader calls it.
        declares =
          let
            g = t.getSubOptions or null;
          in
          if isFunction g || (isAttrs g && g ? __functor) then g else (_prefix: { });
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
        else if evaluatesOwnRoles t then
          true
        else
          all (go (fuel - 1)) (importedWrapped t);
    in
    go importedTypeWalkFuel;

  # ── A RECORD WHOSE `nestedTypes` IS AN OUTPUT OF ITS OWN EVALUATION (den-hoag-a0c4z) ─────────────
  # nixpkgs' `submoduleWith` states `nestedTypes = optionalAttrs (freeformType != null) { … }` with
  # `freeformType = base._module.freeformType`, `base` the type's own module set evaluated with NO
  # definitions. Any read of that field, even `? elemType` or `== { }`, is a checked `evalModules` of
  # a set complete only once the definitions and the other declarations join it, and nixpkgs never
  # takes it: the read refuses "option does not exist" where nixpkgs yields the value. So no walk
  # reads it. The record's one role stays the module set, read off `getSubModules` (`readRoles`), and
  # what `nestedTypes` states crosses as `unroledNested`, an unforced thunk (`importType`).
  #
  # ★ THE RIDER'S ONE EXCEPTION (ADR-0014, owner-ruled 2026-10-01): the record is recognised by its
  # payload stating `modules` (the parameter set it MERGES on is a module set, so its roles are a
  # function of that set) AND by stating its module set in a carrying spelling (`getSubModules`), for
  # LAZINESS ONLY. What it carries is never read off the payload. `getSubModules` is read only once
  # the payload test holds: a container forwards it to its element, and is never asked. A gen record
  # (`carries`) and a seam (`nonMountable`, whose `functor` refuses) never pay the read.
  #
  # ★ THE STATED RESIDUE: a record stating both and ALSO a static role in `nestedTypes` is served as
  # a module set with that role unread (no test that leaves `nestedTypes` unread can separate it);
  # one whose payload states no `modules`, or which states no `getSubModules`, is not recognised and
  # keeps the operand-alone evaluation and its refusal.
  evaluatesOwnRoles =
    t:
    !(t ? carries)
    && !(t ? nonMountable)
    && ((t.functor or { }).payload or null) ? modules
    && (t.getSubModules or null) != null;

  # ── NESTING-NESS, AND THE TWO PREDICATES THAT READ IT (den-hoag-n6dh7 item 1, item 5) ─────────
  # A NESTING TYPE is one whose value is a nested module tree: it states that tree as data (`nests`,
  # the module set and arguments its nested evaluation takes) and folds through the evaluation's
  # accessor (`mergeDefs.threaded`, the sibling of its called fold). ONE binding, and every reader of
  # "is this a nesting type" reads it. A record carrying `nests` WITHOUT the sibling is not one,
  # whatever it copied: gen-schema's `refined` over a submodule keeps `nests` and loses the sibling,
  # and its fold is the copied exported `merge`. Presence only, so it forces nothing.
  isNesting = t: t ? nests && t ? mergeDefs.threaded;

  # MAY this type nest? The dispatch and key-walk predicate: a type that is nesting, or wraps one
  # at any depth, through what it declares it wraps (`declaredWrapped`, the one reading the import
  # refusal's walk takes too, so the two predicates never disagree on what a record wraps). Bounded by the
  # same fuel as `importedDecidable`, and `true` AT EXHAUSTION: a wrong `true` costs a walk over
  # types that carry no nesting (each falls back to its own fold), where a wrong `false` would send a
  # nesting option down the called path, whose nesting element refuses. Of the two, `true` is the
  # answer whose failure is visible. It is NOT the import refusal's predicate (`declaresNesting`,
  # below), which answers the same question with the opposite posture at exhaustion.
  canNest =
    let
      go =
        fuel: t:
        if !(isAttrs t) then
          false
        else if isNesting t then
          true
        else
          let
            wrapped = declaredWrapped t;
          in
          wrapped != [ ] && (fuel <= 0 || prelude.any (go (fuel - 1)) wrapped);
    in
    go importedTypeWalkFuel;

  # What a record DECLARES it wraps, read by the readers that already exist and never a new copy:
  # its roles in either vocabulary (`importedWrapped`: `carries`, else every `nestedTypes` value, so
  # `coercedTo`'s `finalType` counts), and, where it states none there, the element or members the
  # carrying spellings state (`statedRoles`, which there reaches only a top-level `elemType`). Never
  # its functor payload: a payload is what a type offers to MERGE on (`payloadOffered` below), not
  # what it carries. A `nonMountable` record wraps no type.
  declaredWrapped =
    t:
    # No binding on the common path: `canNest` asks this of every option the engine folds, so one
    # there is paid per instance. A record with `carries` or a non-empty `nestedTypes` answers
    # `importedWrapped` whole. Past that, the one carrying spelling `statedRoles` can still reach is
    # a top-level `elemType`, so only a record stating one pays for the reading.
    if t ? carries || t ? nonMountable || (!(evaluatesOwnRoles t) && { } != (t.nestedTypes or { })) then
      importedWrapped t
    else if t ? elemType then
      [ (statedRoles t).element ]
    else
      [ ];

  # What a record's functor payload OFFERS to merge on as an element or members; `[ ]` for a record
  # with `carries` or a `nonMountable` one. Read only where `declaredWrapped` is empty, and only to
  # JUDGE the offer: the walk below refuses a record offering a type that declares a gen nesting type
  # while stating none (OQ1 arm (ii-a), *defaulted, reversible*), and never takes the offer as a
  # declaration.
  payloadOffered =
    t:
    let
      payload = (t.functor or { }).payload or null;
      role = payloadRole payload;
    in
    if t ? carries || t ? nonMountable then
      [ ]
    else if role == "element" then
      [ payload.elemType ]
    else if role == "alternatives" then
      payload.elemType
    else
      [ ];

  # ★ THE DECLARED OPT-OUT (S2, RULED (i) with the escape hatch, den-hoag-n6dh7 2026-09-27; the
  # pattern is ADR-0023's "declared opt-out as the interim"). An author states the answer the walk
  # below cannot reach by setting `declaresNesting = false` on the foreign type — the container or
  # the self-referential element, either one. It is taken at its word: that type answers `false`
  # with no walk and no fuel. THE PRICE, stated beside it: a marked type that DOES forward to a gen
  # nesting type becomes a silent standalone evaluation through the exported `merge` (OQ11 (d)'s
  # stated price, now taken by name). Only `false` is a door; any other value is refused by name
  # (a declared `true` is not an opt-in, *defaulted, reversible*). ONE text, read by `importType`
  # at construction and by the walk wherever it meets the field.
  declaresNestingMarkerRefusal =
    t:
    if !(t ? declaresNesting) || t.declaresNesting == false then
      null
    else
      "gen-merge: the option type `${nameOf t}' states `declaresNesting' as "
      + (if t.declaresNesting == true then "`true'" else "a ${builtins.typeOf t.declaresNesting}")
      + "; the field is a declared opt-out and takes only `false'. A type that wraps a gen nesting "
      + "type states it by carrying that type as its element, not by this field";

  # DOES this type declare a gen nesting type as an element? The IMPORT REFUSAL's predicate (OQ11
  # (d)): a foreign container outside the recognised six that declares one cannot thread the
  # evaluation to a nested tree. Transitive over what each type declares, presence only, bounded by
  # `importedTypeWalkFuel`. The marker above is read on every type BEFORE the walk descends.
  #
  # ★ AT EXHAUSTION IT REFUSES BY NAME (S2, RULED (i)). Whether a cyclic type graph reaches a nesting
  # type is only semi-decidable, and Nix has no reference equality to find the cycle: nixpkgs'
  # `types.json` shape (`valueType = nullOr (oneOf [ str (attrsOf valueType) (listOf valueType) ])`)
  # cannot be told from a deep one. THE PRICE, stated: a recursive or fuel-deep element under an
  # unrecognised container (`uniq`, `coercedTo`, `functionTo`, …) is refused even where it would not
  # nest. The refusal names the remedy — the same three the README and AGENTS.md sections carry.
  # Depth-first with `any`, so the first exhausted path refuses and a cyclic type costs one walk of
  # the fuel, never the whole unfolded tree.
  #
  # ★ A RECORD THAT DECLARES NOTHING BUT WHOSE PAYLOAD OFFERS A NESTING ELEMENT IS REFUSED BY NAME
  # (`nestingOfferRefusal`, OQ1 arm (ii-a), *defaulted, reversible*). Its payload answers only what it
  # merges on (the 2026-09-25 ruling), so it declares nothing; its own fold would then evaluate the
  # nested tree standalone, and nothing in the record says so.
  declaresNestingAt =
    door: loc: root:
    let
      go =
        fuel: t:
        let
          marker = declaresNestingMarkerRefusal t;
          wrapped = declaredWrapped t;
        in
        if !(isAttrs t) then
          false
        else if t ? declaresNesting then
          (if marker == null then false else throw marker)
        else if isNesting t then
          true
        else if wrapped == [ ] then
          # presence first, inline: the walk ends at every leaf here, and the judging is paid only
          # where a payload offers an element at all
          (
            if
              ((t.functor or { }).payload or null) ? elemType && prelude.any (go (fuel - 1)) (payloadOffered t)
            then
              throw (nestingOfferRefusal door loc t)
            else
              false
          )
        else if fuel <= 0 then
          throw (
            "gen-merge: cannot decide whether the option type `${nameOf root}' declares a gen nesting "
            + "type as an element: its type structure nests deeper than the walk's fuel ("
            + toString importedTypeWalkFuel
            + "), as a self-referential element does. Wrap the element in a recognised container "
            + "(attrsOf, lazyAttrsOf, listOf, nullOr, either, oneOf), declare no gen nesting element, "
            + "or state the answer with `declaresNesting = false' on the type"
          )
        else
          prelude.any (go (fuel - 1)) wrapped;
    in
    go importedTypeWalkFuel root;
  declaresNesting = declaresNestingAt null null;

  # ── RE-HOMING: A STOCK FOREIGN CONTAINER, RECOGNISED (F2 elaboration, RULED "take (i)") ───────
  # Which of gen's own containers a foreign record IS, as `{ container; element; }` (or `{ container
  # = "either"; alternatives; }`), or `null` when it is none of the six. RECOGNISED on the functor,
  # the relation the record merges by; its element or members read from the carrying spellings
  # (`statedRoles`), never from the payload, and a record stating none is not recognised. Keyed on the functor NAME
  # and the payload's KEY SET, as nixpkgs spells them: `attrsOf` and `lazyAttrsOf` are one
  # `attrsWith` discriminated by `lazy`, and `oneOf` is `either`s nested to the LEFT (nixpkgs folds
  # it with `foldl'`). A non-default `placeholder` is unrecognised, because gen's container has none
  # and would silently change what introspection reports (*defaulted, reversible*). The constructors
  # live above this unit, so this answers the recognition and the rebuild over gen's own
  # constructor happens where they are in scope.
  #
  # ★ THE STATED PRICE (owner, 2026-09-25, den-hoag-n6dh7): a stock container whose `merge` was
  # overridden (`attrsOf t // { merge = …; }`) cannot be told from the stock one — Nix cannot compare
  # functions — and is re-homed silently, losing the override. The byte-mode parity suite is the
  # divergence check.
  #
  # ★ A RECOGNISED RECORD WHOSE PAYLOAD OFFERS A DIFFERENT ELEMENT THAN IT STATES IS REFUSED BY NAME
  # (`rehomeDisagreementRefusal`, OQ2 arm (b), *defaulted, reversible*): it would carry one type and
  # merge on another, whether or not it is then re-homed, so it is refused before `canNest` is asked
  # (asking `canNest` first would let a record stating `str` over a nesting payload fold standalone,
  # silently). A stock record states one value in both places (`rehomeAgreed`).
  importedRehomeAt =
    door: loc: t:
    let
      f = t.functor or { };
      payload = f.payload or null;
      keys = if isAttrs payload then attrNames payload else [ ];
      name = f.name or null;
    in
    # `roles` is bound only past the functor-name test: a door asks this of every foreign record
    # stating an element, so a binding ahead of it is paid per instance
    if
      !(isAttrs t)
      || t ? carries
      || t ? nonMountable
      || !(name == "attrsWith" || name == "listOf" || name == "nullOr" || name == "either")
    then
      null
    else
      let
        roles = statedRoles t;
      in
      if
        name == "attrsWith"
        &&
          keys == [
            "elemType"
            "lazy"
            "placeholder"
          ]
        && payload.placeholder == "name"
        && roles ? element
      then
        rehomeAgreed door loc t {
          container = if payload.lazy then "lazyAttrsOf" else "attrsOf";
          inherit (roles) element;
        }
      else if (name == "listOf" || name == "nullOr") && keys == [ "elemType" ] && roles ? element then
        rehomeAgreed door loc t {
          container = name;
          inherit (roles) element;
        }
      else if name == "either" && keys == [ "elemType" ] && roles ? alternatives then
        rehomeAgreed door loc t {
          container = "either";
          inherit (roles) alternatives;
        }
      else
        null;
  importedRehome = importedRehomeAt null null;

  # A recognition `r` of `t`, or the disagreement refusal where its payload offers another element
  # than the carrying spelling states. Two elements are the same type when their `check` and `merge`
  # are the same closures: a stock record states one value in both places, so the two are
  # pointer-equal there, and two separate constructions differ. Only those two slots are compared,
  # never the records whole: `==` on two distinct type records forces every attribute, and a
  # self-referential `description` (nixpkgs' `types.json` shape) then recurses uncatchably; a
  # compared record's `type` would be forced as well. `closuresOf` is not used here: it filters the
  # export fields by `isFunction`, which forces that same `description`. A `nonMountable` record's
  # `check` is a refusal when forced (`refuseMount`), so where either side is one only `merge` is
  # compared: the tree answers its fold, and one tree offered and stated is still one closure.
  rehomeAgreed =
    door: loc: t: r:
    let
      slots =
        x:
        builtins.intersectAttrs {
          check = null;
          merge = null;
        } x;
      mergeSlot = x: builtins.intersectAttrs { merge = null; } x;
      same =
        a: b:
        isAttrs a
        && isAttrs b
        && (
          if a ? nonMountable || b ? nonMountable then mergeSlot a == mergeSlot b else slots a == slots b
        );
      offered = t.functor.payload.elemType;
    in
    if
      (
        if r ? alternatives then
          isList offered
          && length offered == 2
          && same (elemAt offered 0) (elemAt r.alternatives 0)
          && same (elemAt offered 1) (elemAt r.alternatives 1)
        else
          same offered r.element
      )
    then
      r
    else
      throw (rehomeDisagreementRefusal door loc t);

  # The re-homing disagreement's text (OQ2 arm (b)): the record, both statements, and the way out.
  rehomeDisagreementRefusal =
    door: loc: t:
    "${doorAt door loc}the option type `${nameOf t}' states "
    + (if (statedRoles t) ? alternatives then "its members" else "its element")
    + " in a carrying spelling and offers a different one to merge on in its functor payload's "
    + "`elemType'; it would carry one type and merge on another, so no reading of it is the type it "
    + "states. State the same type in both";

  # A refusal's opening: the door and the option where the caller named them (7gp66 R6), as
  # `nestingImportRefusal` opens; bare where it asked the interface directly.
  doorAt =
    door: loc:
    if door == null then
      "gen-merge: "
    else
      "gen-merge: `${door}'${if loc == null then "" else " at option `${showOption loc}'"}: ";

  # ── HOMING: WHAT A TYPE BOUND TO A POSITION FOLDS AS (den-hoag-n6dh7 item 5; gate C9) ──────────
  # The type itself when it is gen's own — it states `carries`, is a nesting type, or is a checker
  # stating `verify` — and gen's own container when it is one of the six stock foreign containers
  # (`importedRehome` above) and MAY nest (a stock container over no nesting element keeps its own
  # fold: re-homing buys a tree to thread to and nothing else, *defaulted, reversible*), rebuilt over
  # gen's constructor with its elements homed in turn, lazily,
  # so a self-referential stock type is unfolded only as deep as a fold reaches. Otherwise the type
  # itself — UNLESS IT DECLARES A GEN NESTING ELEMENT. Then the container outside the six is
  # rebuilt through its own `substSubModules` so the evaluation threads to the nested tree
  # (`threadedForeign`, den-hoag-f8mgj arm (T)), and where that rebuild does not state the element it
  # is THE IMPORT REFUSAL (OQ11 (d)), by name, before any fold is taken. `door` names what the caller
  # invoked (7gp66 R6): `evalModuleTree` at the engine's sites, which also carry the option's `loc`,
  # and `mkOptionType` at `importType`, which keeps the refusal (`importType`).
  #
  # ★ THE STATED PRICE OF OQ11 (d) (owner, 2026-09-25, den-hoag-n6dh7): a foreign container that
  # forwards to a gen nesting type it does NOT declare is unobservable, and becomes a silent
  # standalone evaluation through the bridge (`bridge`, below). So does a type carrying the declared
  # opt-out `declaresNesting = false`, by name.
  homedAt =
    door: loc: t:
    if
      !(isAttrs t)
      || t ? verify
      || t ? carries
      || t ? __threadedForeign
      || isNesting t
      || !(statesWrapped t)
    then
      t
    else
      let
        r = importedRehomeAt door loc t;
      in
      if r != null && canNest t then
        (
          let
            rebuilt =
              if r.container == "either" then
                constructors.either (homedAt door loc (elemAt r.alternatives 0)) (
                  homedAt door loc (elemAt r.alternatives 1)
                )
              else
                constructors.${r.container} (homedAt door loc r.element);
          in
          # ★ THE RECORD'S OWN `check` RIDES ON THE REBUILD (den-hoag-4ifgb M-B): a functor rebuilds
          # the container and its element, and a refinement `{ x : F e | p x }` is not part of the
          # functor, so `addCheck` over a stock container is rebuilt away unless carried. A foreign
          # record has no witness, so a rewritten check cannot be told from the stock one; the
          # record's check is carried on every re-home, where it can be evaluated here, and gen's
          # own fold applies it as a rewritten check (`carriedFold`). A stock `either`/`nullOr`
          # whose members reach the bare tree states a check that cannot be evaluated here and
          # cannot be detected, so it is rebuilt without it: the enumerated residue, README "The
          # prices, stated".
          if checkReadsTree t then rebuilt else rebuilt // { inherit (t) check; }
        )
      else if declaresNestingAt door loc t then
        threadedForeign door loc t
      else
        t;

  # ── AN UNRECOGNISED CONTAINER THREADS THROUGH ITS OWN REBUILD (den-hoag-f8mgj, owner-ruled arm (T)) ─
  # A foreign container outside the six, declaring a gen nesting element, is rebuilt by its own
  # `substSubModules`, handed a marker in place of a module list. Every stock container's rebuild
  # calls its element's `substSubModules`, and a gen element answers the marker with itself
  # (`exportType`, and the tree's `refuseMount`); the marker's function returns that element with its
  # `merge` replaced, so the container keeps its own merge and check (`coercedTo` keeps its
  # `coerceFunc`). Two rebuilds:
  #   capture  — the element's merge RECORDS each site (loc, defs), so the container's own merge is
  #              the split: the key walk reads which element positions exist and what defs each gets.
  #   threaded — the element's merge is the engine's threaded twin at position ++ (eloc - loc).
  # With no accessor (called) it refuses as the import refusal does. A rebuild that does not STATE
  # the marked element (in `nestedTypes` or a top-level `elemType`) is refused by name, as F2 α
  # requires: a container that drops its argument would otherwise reach the nested tree through the
  # bridge, a silent standalone evaluation.
  #
  # ★ THE BOUNDARY (ADR-0014, ADR-0023): a FOREIGN closure, the container's own `merge` and `check`,
  # runs inside gen's evaluation with a gen-threaded element fold under it. No foreign engine
  # evaluates the tree: the channel is entered only from `homedAt` in gen's own evaluation, the
  # marker is never handed out, and the bridge is not reached.
  #
  # ★ THE STATED PRICES: `unique`'s message is lost on rebuild (nixpkgs' own rebuild drops it too);
  # the tree's tombstone answers `substSubModules` inside this channel, and an element handed into a
  # rebuild answers `check` in gen's words and `getSubModules` with `null` where it may nest
  # (`genFace`); the container's merge runs three times per option (the split, the steps read, the
  # threaded fold) against nixpkgs' once. The domain is a container whose rebuild forwards its
  # argument and whose merge does not inspect element values; the first half is refused by name
  # above, and the second has no predicate here.
  threadedForeign =
    door: loc0: t:
    let
      via =
        f:
        let
          r = t.substSubModules { __genThreadElement = e: f e // { __genThreadMark = true; }; };
          stated =
            if isAttrs r then
              prelude.attrValues (r.nestedTypes or { }) ++ (if r ? elemType then [ r.elemType ] else [ ])
            else
              [ ];
        in
        if isAttrs r && r ? merge && builtins.any (e: isAttrs e && e ? __genThreadMark) stated then
          r
        else
          throw (nestingImportRefusal door loc0 t);
      # the element as the container's closure reads it: gen's own check, and no module set for an
      # element that may nest (a nesting seam's exported face refuses both, at any depth)
      genFace =
        e:
        e
        // {
          check =
            if e ? verify then
              (v: e.verify v == null)
            else if e ? admits then
              e.admits
            else
              e.check;
          getSubModules = if canNest e then null else e.getSubModules;
        };
      stepOf = loc: eloc: builtins.genList (i: elemAt eloc (length loc + i)) (length eloc - length loc);
      capture = via (
        e:
        genFace e
        // {
          merge = eloc: edefs: {
            __genTSite = {
              loc = eloc;
              defs = edefs;
              type = e;
            };
          };
        }
      );
      sitesOf =
        v:
        if isAttrs v then
          (if v ? __genTSite then [ v.__genTSite ] else prelude.concatMap sitesOf (prelude.attrValues v))
        else if isList v then
          prelude.concatMap sitesOf v
        else
          [ ];
      # ★ THE RECORD'S OWN `check` RIDES ON THE THREADED FOLD, as on the six's re-home (4ifgb M-B):
      # `addCheck` is `t // { check; merge; }` and keeps the base container's `substSubModules`, so
      # the rebuild returns the STOCK container and a refinement is not part of it. It is carried as
      # a checked fold around the whole threaded fold, not as a copied field, because a v2 container
      # (`coercedTo`, `attrsWith`) folds by `merge.v2` and never reads the record's `check`. Where
      # that check reads the element's foreign face and the element holds a nested tree (`unique`'s
      # check is its element's, `coercedTo`'s calls `finalType.check`), it cannot be evaluated here.
      # A stock `unique` is decided there: its check IS its element's, which the element's own
      # threaded fold already answers in gen's words. A detected rewrite over `unique` is refused by
      # name with `carriedFold`'s words. A `coercedTo` cannot be decided (its stock check is a fresh
      # record), and is refused with the import refusal: the interim, as before this construction,
      # while that reading is the owner's (OQ17-R).
      nt = t.nestedTypes or { };
      checkElem =
        if nameOf t == "unique" then
          nt.elemType or null
        else if nameOf t == "coercedTo" then
          nt.finalType or null
        else
          null;
      readsTree = checkElem != null && checkReadsTree checkElem;
      # Over the bare tree the slots cannot be compared (that forces the tombstone's `check`), so
      # the force decides: the stock slot IS the tombstone's and refuses, a rewrite's does not.
      # Elsewhere the slots compare by pointer, and only as records: `==` on a lambda is
      # evaluator-dependent, so a lambda slot (a rewrite on the element) is never stock. A
      # refinement on the bare-tree element itself is therefore read as a rewrite over `unique`.
      stockUnique =
        nameOf t == "unique"
        && (
          if checkElem ? nonMountable then
            !(builtins.tryEval t.check).success
          else
            isAttrs checkElem.check
            &&
              builtins.intersectAttrs { check = null; } t == builtins.intersectAttrs { check = null; } checkElem
        );
      # the verdict names the container, never its `description`, which reads the element's and so
      # the tree's refusing one
      checkedThreaded =
        fold:
        if !readsTree then
          checkedFold {
            inherit (t) check;
            description = nameOf t;
          } fold
        else if stockUnique then
          fold
        else if nameOf t == "unique" then
          (loc: _defs: throw (rewrittenCheckRefusal t loc))
        else
          (loc: _defs: throw (nestingImportRefusal door loc t));
      # A refinement on the ELEMENT is carried as the engine's threaded site carries it
      # (`modules.nix` `threadedAs`). The element the rebuild hands back is the record its
      # `substSubModules` closes over, from before the refinement, so the declared element is found
      # by its witness, the one record a rewrite keeps.
      declared = prelude.attrValues nt ++ (if t ? elemType then [ t.elemType ] else [ ]);
      carriedElement =
        e: fold:
        let
          rewritten = filter (
            d: isAttrs d && d ? _checkWitness && d._checkWitness == e._checkWitness && rewritesCheck d
          ) declared;
        in
        if e ? _checkWitness && rewritten != [ ] then carriedFold (head rewritten) fold else fold;
    in
    t
    // {
      __threadedForeign = true;
      split =
        loc: defs:
        map (s: {
          step = stepOf loc s.loc;
          inherit (s) loc defs type;
        }) (sitesOf ((importedFold capture) loc defs));
      mergeDefs = {
        __functor =
          _: loc: _defs:
          throw (nestingImportRefusal door loc t);
        threaded =
          ev: loc: defs:
          let
            steps = map (s: stepOf loc s.loc) (sitesOf ((importedFold capture) loc defs));
          in
          checkedThreaded (importedFold (
            via (
              e:
              genFace e
              // {
                # A threaded element folded at a step the split did not capture (a value the merge
                # returns, such as `functionTo`'s function body) keeps its fold, and its accessor's
                # `child` refuses by name: only a nested-tree read refuses, so a member that never
                # reads the tree still answers (ADR-0025 item 1).
                merge = carriedElement e (
                  eloc: edefs:
                  mergeDefsThreaded (
                    ev
                    // {
                      position = ev.position ++ stepOf loc eloc;
                    }
                    // (
                      if builtins.elem (stepOf loc eloc) steps then
                        { }
                      else
                        {
                          child = _site: throw (unexposedRefusal door eloc t);
                        }
                    )
                  ) eloc e edefs
                );
              }
            )
          )) loc defs;
      };
    };

  # Whether a record states an element or members AT ALL, in any carrying spelling (`carries`, a
  # non-empty `nestedTypes`, a top-level `elemType`), or OFFERS one to merge on in its functor
  # payload's `elemType` (read only so the walk can judge the offer, `payloadOffered`; a
  # `nonMountable` record's `functor` is a refusal, and it wraps nothing). Presence only, read before
  # any walk: a record doing neither can be neither re-homed nor refused, and most records crossing a
  # door do neither, so this is what keeps the nested-tree crossing's price off every leaf and every
  # `mkOptionType` descriptor.
  statesWrapped =
    t:
    t ? carries
    || (!(evaluatesOwnRoles t) && { } != (t.nestedTypes or { }))
    || (!(t ? nonMountable) && (t ? elemType || ((t.functor or { }).payload or null) ? elemType));

  # The import refusal's text: the door, the option where there is one, the container, what in it
  # declared the element, and the rule with the ways out that exist: one of the six, a container
  # whose rebuild threads (`threadedForeign`; in gen's own evaluation only, since the `mkOptionType`
  # door keeps this refusal), or the declared opt-out and its price.
  nestingImportRefusal =
    door: loc: t:
    let
      nested = t.nestedTypes or { };
      keys = filter (k: declaresNestingAt door loc nested.${k}) (attrNames nested);
    in
    "gen-merge: `${door}'${
      if loc == null then "" else " at option `${showOption loc}'"
    }: the option type `${nameOf t}' declares a gen nesting type as an element (${
      if keys != [ ] then "its `nestedTypes.${head keys}'" else "its `elemType'"
    }), and it cannot thread the evaluation to that nested tree here. Use attrsOf, lazyAttrsOf, "
    + "listOf, nullOr, either or oneOf; or, bound in gen's own evaluation rather than through "
    + "`mkOptionType', a container whose `substSubModules' rebuild states its element and whose "
    + "`check' does not read the nested tree; or state `declaresNesting = false' on the type and "
    + "take the stated price: a nested tree it forwards to is then evaluated standalone";

  # The refusal at a threaded element folded where the container's merge does not expose it
  # (`threadedForeign`), in the import refusal's form.
  unexposedRefusal =
    door: loc: t:
    "${doorAt door loc}the option type `${nameOf t}' folds its gen nesting element at a position its "
    + "own merge does not expose when the option is merged (inside a value it returns, such as a "
    + "function body), so that nested tree cannot be threaded into this evaluation. Declare the tree "
    + "at a position the merge returns as a value, or state `declaresNesting = false' on the type and "
    + "take the stated price: a nested tree it forwards to is then evaluated standalone";

  # The offer refusal's text (OQ1 arm (ii-a)): a record stating no element whose functor payload
  # offers one that declares a gen nesting type, raised inside the walk with its caller's door.
  nestingOfferRefusal =
    door: loc: t:
    "${doorAt door loc}the option type `${nameOf t}' offers a type declaring a gen nesting type to merge on "
    + "(its functor payload's `elemType') but states no element it carries; a payload says what a "
    + "type merges on, not what it carries, so its fold would evaluate the nested tree standalone "
    + "and nothing would say so. State the element in `nestedTypes.elemType' or a top-level "
    + "`elemType', or state `declaresNesting = false' on the type and take that stated price";

  # THE BRIDGE (item 7, OQ11 (d)): the evaluation's accessor where there is no gen evaluation — a
  # foreign engine folding a gen type through its exported `merge`. Its child is ONE root evaluation
  # of the nested tree, in the type's own CALLED mode, as the exported fold made it before the
  # sibling existed; a foreign engine carries no gen report.
  bridge = {
    position = [ ];
    child = site: nestedTreeAt site.nests.calledMode site;
  };
  # A fold as the foreign protocol publishes it: through the bridge where it carries the sibling,
  # and itself where it does not (a foreign fold, or a fold nothing nests under) — the export's
  # presence arm (gate C3).
  bridged = f: if f ? threaded then f.threaded bridge else f;

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
        else if evaluatesOwnRoles x then
          { }
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
  # ★ ONE DEFINITION, read three times — by the refusal below to decide its domain, by the import to
  # populate `carries`, and by the identity walk to learn what a raw foreign record carries
  # (`importedCarried`). The roles are read in each role's own introspection spelling
  # (`roleSpelling.<role>.nested`'s keys) or, for a module set, the sub-protocol slot that states it.
  # The order is load-bearing: a container's module set IS its element's, so the module-set arm is
  # reached only by a record stating no element, and reading it first would force the element type
  # at construction. A role key holding an OPTION record states no role: `attrTag`'s `nestedTypes`
  # is its tag set (see `joinRenames`), so a tag an author NAMED `elemType`, `left` or `right` is a
  # tag, and read as a role it would stop the identity walk on a slot whose type carries identity.
  #
  # `keys` are the `nestedTypes` keys the reading consumed as a role. Every other key the record
  # states (`freeformType`, `coercedType`/`finalType`, an `attrTag`'s tags, an author's own) names no
  # gen role and crosses VERBATIM (`unroledNested`, re-published by `exportType`).
  readRoles =
    t:
    let
      nested = if evaluatesOwnRoles t then { } else t.nestedTypes or { };
      isOption = v: isAttrs v && (v._type or null) == "option";
    in
    if nested ? elemType && !(isOption nested.elemType) then
      {
        roles.element = nested.elemType;
        keys = [ "elemType" ];
      }
    else if t ? elemType then
      {
        roles.element = t.elemType;
        keys = [ ];
      }
    else if nested ? left && nested ? right && !(isOption nested.left) && !(isOption nested.right) then
      {
        roles.alternatives = [
          nested.left
          nested.right
        ];
        keys = [
          "left"
          "right"
        ];
      }
    else if (t.getSubModules or null) != null then
      {
        roles.moduleSet = t.getSubModules;
        keys = [ ];
      }
    else
      noRoles;
  # Shared, so the common answer allocates nothing per read.
  noRoles = {
    roles = { };
    keys = [ ];
  };
  statedRoles = t: (readRoles t).roles;
  unroledNested = t: read: builtins.removeAttrs (t.nestedTypes or { }) read.keys;

  carrierRefusal =
    t: roles:
    let
      name = nameOf t;
      missing = filter (f: !(t ? ${f})) subProtocol;
    in
    # A union's members introduce no path level, so a leaf's three answers are ITS answers; the
    # roles that owe the sub-protocol are the two a leaf's answer is false for.
    if !(roles ? element || roles ? moduleSet) || missing == [ ] then
      null
    else
      "gen-merge: the structural type `${name}' carries "
      + (if roles ? element then "an element type" else "a module set")
      + " but does not supply "
      + concatStringsSep ", " (map (f: "`${f}'") missing)
      + "; a structural type may not inherit a leaf's protocol answer";

  # relationOwedRefusal — a record that CARRIES something and states nothing to answer for it.
  #
  # A carrier is rebuilt over another parameter wherever the export half derives its relation, so
  # gen's constructor owes it `recarry` unless a stated relation answers instead. A descriptor written
  # in the foreign protocol states its relation as `functor.binOp`; one stating neither would reach
  # gen's constructor and be refused there in a word its author never wrote. The refusal belongs here,
  # in the author's vocabulary, for the reason `carrierRefusal` does.
  relationOwedRefusal =
    t: roles:
    if roles == { } || statesRelation t || t ? recarry then
      null
    else
      "gen-merge: the structural type `${nameOf t}' carries "
      + (
        if roles ? element then
          "an element type"
        else if roles ? alternatives then
          "alternatives"
        else
          "a module set"
      )
      + " but states no merge relation for it; state one in `functor.binOp' (with `functor.name' and "
      + "`functor.type'), since a type that carries something answers for how two of it merge";

  # unroledCollisionRefusal — a key `nestedTypes` states that names no role, where the role's own
  # spelling would publish the SAME key. An unroled key crosses verbatim and the role's spelling is
  # derived beside it at export, so both cannot be kept: one of the two would be replaced without a
  # word. The one reachable shape is a record stating its element at the top-level `elemType` while
  # its `nestedTypes.elemType` holds something that is not a type (an `attrTag` tag an author named
  # `elemType`). Refused here, by name, rather than resolved by an order nobody chose.
  unroledCollisionRefusal =
    t: roles: unroled:
    let
      role = head (attrNames roles);
      spelled = attrNames (roleSpelling.${role}.nested roles.${role});
      clash = filter (k: builtins.elem k spelled) (attrNames unroled);
    in
    if roles == { } || { } == unroled || clash == [ ] then
      null
    else
      "gen-merge: the option type `${nameOf t}' states its ${role} in its top-level spelling, and its "
      + "`nestedTypes' holds ${concatStringsSep ", " (map (k: "`${k}'") clash)} as something that "
      + "is not that ${role}; a crossing publishes the ${role} under that key, so one of the two would "
      + "be lost. Rename the `nestedTypes' key, or state the ${role} there";

  # The role a foreign payload is stating, or null when it states none. `elemType` is the protocol's
  # key for BOTH a single wrapped type and a union's positional member list, and the two are told
  # apart by the only thing that distinguishes them: a member list is a LIST, a wrapped type is a
  # record.
  #
  # ★ ONE DEFINITION, read twice, and both reads are of what a payload OFFERS: by `importedOffered`
  # (what a type merges on) and by `payloadOffered` (the nesting walk judging an offer no carrying
  # spelling states). Neither reads it for what a type carries (`statedRoles` answers that). A second
  # copy of this decision would let the two disagree about what one payload offers.
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
    if f == null || !(f ? binOp) || !statesParameter || (f.binOp or null) != null then
      null
    else
      "gen-merge: the option type `${name}' states a parameter in its `functor' but leaves "
      + "`functor.binOp' empty, so nothing it states can discriminate on that parameter and "
      + "`${name}' would merge on its NAME ALONE — accepting two operands the parameter tells apart. "
      + "State the relation in `functor.binOp', or drop the `functor' if merging on the name alone is "
      + "what this type means";

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

  # `read` is bound ONCE per import and shared by every refusal and the record: `importType` runs per
  # instance, so each re-reading is paid once per declared position (perf-bench `schemaHosts`). An
  # empty `nestedTypes` states no unroled key, so it is not re-read for one. `{ }` is the LEFT operand
  # of that test and of `unroledCollisionRefusal`'s: attrset `==` forces the left side's `type`, and a
  # nesting record's `nestedTypes` is not otherwise read to decide its import.
  importType =
    t:
    let
      read = readRoles t;
      roles = read.roles;
      # A record whose `nestedTypes` is its own evaluation's output keeps its unroled keys UNFORCED:
      # the emptiness test would be that evaluation (`evaluatesOwnRoles`).
      unroled =
        if !(evaluatesOwnRoles t) && { } == (t.nestedTypes or { }) then { } else unroledNested t read;
    in
    if !(isAttrs t) then
      {
        refused = "gen-merge: cannot import an option type from a ${builtins.typeOf t}; the boundary translates records, not values";
      }
    else if !(t ? name) && !(t ? verify) && all (f: !(t ? ${f})) exportFields then
      {
        refused = "gen-merge: cannot import `${concatStringsSep ", " (attrNames t)}' as an option type; it answers neither this library's vocabulary nor any field of the foreign protocol";
      }
    else if declaresNestingMarkerRefusal t != null then
      { refused = declaresNestingMarkerRefusal t; }
    # A record crossing WHOLE is homed as a record bound to a position is (den-hoag-n6dh7 item 5):
    # one of the six stock containers is gen's own container, and a record declaring a gen nesting
    # element that is none of them is refused at construction, since `mkOptionType` is this door.
    #
    # ★ ONLY WHERE IT MAY NEST (`canNest`), which is what re-homing buys: a tree to thread to. A stock
    # container over no nesting element keeps its own fold, and with it any override its author
    # stated, since the stated price of re-homing buys nothing there (*defaulted, reversible*).
    #
    # A record that is ITSELF a nesting type declares nothing by crossing: it is a record copy, whose
    # fold this import replaces with the copied exported one — the stated price (gen-schema's
    # `refined` over a `submodule`), not a declaration.
    else if
      !(isNesting t) && statesWrapped t && importedRehomeAt "mkOptionType" null t != null && canNest t
    then
      (
        let
          rehomed = homedAt "mkOptionType" null t;
        in
        {
          imported = rehomed;
          inherit rehomed;
        }
      )
    else if !(isNesting t) && statesWrapped t && declaresNestingAt "mkOptionType" null t then
      { refused = nestingImportRefusal "mkOptionType" null t; }
    else if carrierRefusal t roles != null then
      { refused = carrierRefusal t roles; }
    else if functorRefusal t != null then
      { refused = functorRefusal t; }
    else if relationRefusal t != null then
      { refused = relationRefusal t; }
    else if relationOwedRefusal t roles != null then
      { refused = relationOwedRefusal t roles; }
    # Not asked of a record whose `nestedTypes` is its own evaluation's output: its one role is the
    # module set, which spells no nested key, so no unroled key can collide, and asking would force it.
    else if !(evaluatesOwnRoles t) && unroledCollisionRefusal t roles unroled != null then
      { refused = unroledCollisionRefusal t roles unroled; }
    else
      {
        imported =
          let
            name = t.name or "raw";
            fold = importedFold t;
            # Where the fold is CHECKED, the unchecked one it guards rides ON it, for the one site that
            # merges without checking (the freeformType); a caller replacing `mergeDefs` whole replaces
            # both at once, as with `mergeDefs.reported`.
            # A gen record whose `check` a wrapper rewrote crosses with that check as its checked fold
            # (`carriedFold`), never stripped with the protocol's names (den-hoag-4ifgb).
            checked = isV2 t || checksDefs t || rewritesCheck t;
            admits = importedAdmits t;
            deprecated = importedDeprecation t;
          in
          # WHAT THE FOREIGN PROTOCOL DID NOT SAY SURVIVES UNTOUCHED. Only the protocol's own names
          # are consumed here; a descriptor's other fields are the author's and are none of this
          # boundary's business, so they cross unread rather than being enumerated and lost.
          builtins.removeAttrs t (
            exportFields
            ++ [
              "_protoLeafMerge"
              "_checkWitness"
            ]
          )
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
          // (if roles == { } then { } else { carries = roles; })
          # What `nestedTypes` states beyond the roles crosses VERBATIM and is re-published at export,
          # as a nixpkgs type keeps it. It names no gen role, so nothing on this side reads it.
          // (
            if !(evaluatesOwnRoles t) && attrNames unroled == [ ] then { } else { unroledNested = unroled; }
          )
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

  # typeDefect — why a value standing where a TYPE is demanded is not one, or `null` when it is.
  # The engine asks it only where it folds a value against the type and nothing answered the
  # question already: a fold of its own, a `verify`, or no type at all (`./modules.nix`
  # `mergeDefsRichWith`, the freeform fold, and `mergeDefsWith`, where a container demands its
  # element). It judges one level deep and never walks, so a
  # namespace such as `refinements` is refused as the value it is rather than entered.
  #
  # The last arm is `importType`'s second refusal read positively, WIDENED by the fold's own
  # dispatch fields: that predicate was written for foreign records at the import boundary, and the
  # fold also sees native ones — `mkType { mergeDefs = …; }` answers by its fold alone, and
  # `mkType { }` carries only the relation `mkTypeWith` stamps. `importType` keeps its own.
  typeDefect =
    t:
    if isFunction t then
      "is a function, not a type (a type constructor must be applied)"
    else if !(isAttrs t) then
      "is a value of type `${builtins.typeOf t}', not a type"
    else if t ? _type && !(isOptionType t) then
      "is a tagged `${toString t._type}' value, not a type"
    else if
      !(t ? verify || t ? mergeDefs || t ? typeMergeRel || builtins.any (f: t ? ${f}) exportFields)
    then
      "answers neither this library's type vocabulary nor any field of the foreign protocol"
    else
      null;

  # foreignFace — the type a FOREIGN eval folds, which is the gen type minus what only gen's own
  # eval may read. The boundary is the eval (ADR-0014): inside gen's folds a union answers the
  # nesting tree's module domain (`admits`) and holds the tree as nesting, while a foreign engine
  # reaches a gen type only through the published `check` and `merge`, so those two read this face
  # and gen's own fields are untouched. It is therefore lazy by construction — computed only when a
  # foreign engine forces one of the two.
  #
  # The foreign face of a composite is the composite rebuilt over its members' foreign faces: the
  # functorial map `recarry` exists to perform. The tree's is the tree without its gen domain
  # answer, so a foreign membership question reaches its refused `check`, as before the tree
  # answered one. A leaf is its own face, and so is a type carrying a module set (`submodule`):
  # its fold is gen's own `evalModuleTree`, the eval boundary itself, which is why a union inside a
  # submodule mounted abroad still yields a value. For every library combinator the face of a type
  # holding the tree is therefore the type as it stood before, byte-for-byte.
  #
  # It rests on ONE law, `mkTypeWith`'s `recarry` contract (`t.recarry c'` is `t`'s own constructor
  # over `c'`), and on nothing stronger: it rebuilds only when a direct member is the tree or a
  # rebuildable composite, so a type over leaves is returned as itself and the identity round trip
  # `t.recarry t.carries == t` is never assumed. A caller `recarry` rebuilding ANOTHER type would
  # fold a foreign eval's definitions through that type's fold; the door refuses it by name, the
  # identity the vocabulary's nullary relation keys on. A same-named rebuild that still breaks the
  # law is past this door. Both guard and rebuild are one level deep and lazy, so a self-referential
  # type (`j = either str (attrsOf j)`) is unfolded only as deep as a definition reaches.
  #
  # The fence reaches what a type CARRIES. A caller fold closing over a union lexically, and a
  # foreign container's fold over a gen union in either eval, read no face this computes.
  #
  # ★ `exportType` CALLS IT INLINE IN BOTH FIELDS, never through a `let` binding: a binding is one
  # more thunk on EVERY type construction, gen's own included, for a question only a foreign engine
  # asks — measured on the hub bench as eleven gates over bound. And it asks `opensForeign` INLINE
  # before calling, because the published fields are not read by foreign engines alone: a gen
  # library may fold through a gen type's published `merge` inside gen's own eval (gen-aspects does,
  # over a fresh `submodule` per node), and a call per read there is a per-node price on gen's side,
  # which the fence does not charge. A type that does not open is returned before any binding.
  opensForeign = u: isAttrs u && u ? carries && u ? recarry && !(u.carries ? moduleSet);
  foreignMember =
    u: if isAttrs u && u ? nonMountable then builtins.removeAttrs u [ "admits" ] else foreignFace u;
  foreignFace =
    t:
    if !(opensForeign t) then
      t
    else
      let
        members = builtins.concatMap (c: if isList c then c else [ c ]) (builtins.attrValues t.carries);
        rebuilt = t.recarry (
          builtins.mapAttrs (_: c: if isList c then map foreignMember c else foreignMember c) t.carries
        );
      in
      if !(builtins.any (m: isAttrs m && (m ? nonMountable || opensForeign m)) members) then
        t
      else if nameOf rebuilt == nameOf t then
        rebuilt
      else
        throw "gen-merge: the type `${nameOf t}' cannot be folded by a foreign eval: its `recarry' rebuilds it as `${nameOf rebuilt}', so the fold published for it would be another type's";

  # exportType — a gen type EXPRESSED in the foreign protocol.
  #
  # ── THE PARTITION, AND IT IS TOTAL OVER THE FOURTEEN ────────────────────────────────────────────
  # DERIVED (10) — a real translation from a differently-named gen datum:
  #   check <- verify | admits · merge <- mergeDefs · emptyValue <- whenEmpty ·
  #   nestedTypes <- carries | unroledNested · deprecationMessage <- deprecated ·
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

      # Built once by gen-types' `witnessRecord` and published twice, as `check` and as
      # `_checkWitness` (below), so a `check` a wrapper rewrote is the one slot that no longer holds
      # the witness (`rewritesCheck`). The pair is spelled here rather than taken from
      # `witnessedCheck`, whose two-field result every exported type would read or copy
      # (den-hoag-ydro3, owner-ruled arm (c)); `default.nix`'s agreement door holds this spelling to
      # its output. Nix forces the record's slots, the function among them, before it compares their
      # pointers, so forcing the function must not compute the foreign face, which
      # gen's own eval never reads: the face is bound unforced behind the function, and computed at
      # its first application, by a foreign engine.
      check = witnessRecord (
        if t ? verify then
          (v: t.verify v == null)
        else if t ? admits then
          (
            if t ? carries && t ? recarry && !(t.carries ? moduleSet) then
              (
                let
                  face = foreignFace t;
                in
                v: face.admits v
              )
            else
              t.admits
          )
        else
          (_: true)
      );

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
        # `_checkWitness` is not a fifteenth protocol field: it is gen-types' check-witness
        # protocol field, the record of which `check` was published, read only by `rewritesCheck`.
        inherit check;
        _checkWitness = check;
        # Through the bridge where the fold carries the sibling (den-hoag-n6dh7 item 7, OQ11 (d)):
        # a nesting type's tree is one root evaluation, and a gen container threads the bridge to
        # each element through its one `split`, so the forward mount keeps working without a third
        # fold form. Every other fold publishes as it did (`bridged`'s presence arm).
        merge =
          if !(t ? mergeDefs) then
            leafFold
          else if t ? carries && t ? recarry && !(t.carries ? moduleSet) then
            bridged (foreignFace t).mergeDefs
          else
            bridged t.mergeDefs;
        # A nesting type's empty value is its tree over no definitions, through the same bridge: its
        # called `whenEmpty` refuses (den-hoag-n6dh7 item 1).
        emptyValue =
          if isNesting t then { value = t.mergeDefs.threaded bridge [ ] [ ]; } else t.whenEmpty or { };
        nestedTypes = (t.unroledNested or { }) // (if role == null then { } else spelling.nested carried);
        getSubOptions = if sub == null then (_prefix: { }) else sub.declares;
        getSubModules = if sub == null then null else sub.modules;
        substSubModules =
          m:
          if isAttrs m && m ? __genThreadElement then
            m.__genThreadElement exported
          else if sub == null then
            null
          else
            sub.rebuild m;
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
  #
  # ★ ONE FIELD ANSWERS INSIDE THE THREADING CHANNEL ONLY (den-hoag-f8mgj, arm (T)): handed the
  # channel's marker (`threadedForeign`), `substSubModules` answers with the record itself, so a
  # foreign container rebuilt in gen's own evaluation reaches the seam as its element. Handed
  # anything else it refuses as every other field does. A foreign engine never holds the marker, so
  # its mount is refused exactly as before. `fields` are the caller's own, and the record answered
  # through the channel is the whole one, with them.
  refuseMount =
    {
      name,
      reason,
      fold,
      whenEmpty,
      fields ? { },
    }:
    let
      refuse =
        field: throw "gen-merge: `${name}' is not an option type and does not answer `${field}'; ${reason}";
      record = {
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
        substSubModules =
          m:
          if isAttrs m && m ? __genThreadElement then
            m.__genThreadElement record
          else
            refuse "substSubModules";
        typeMerge = refuse "typeMerge";
      }
      // fields;
    in
    record;
in
{
  inherit
    admitsCarried
    carriedFold
    closuresFirst
    exportClasses
    exportFields
    exportType
    importDescriptor
    importType
    importedAdmits
    importedRehome
    isNesting
    canNest
    declaresNesting
    homedAt
    bridge
    importedCarried
    importedOffered
    importedDecidable
    importedDeprecation
    importedElementPrefix
    importedEmpty
    importedFold
    importedHeldAt
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
    rewritesCheck
    typeDefect
    ;
}
