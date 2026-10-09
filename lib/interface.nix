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
  # (i)), and every site here keeps the meaning it had, a functor read as an attrset. No site here
  # decides the function-ness of a definition or a default, so none takes nixpkgs' reading.
  inherit (builtins) isFunction;
  inherit (types) rewritesCheck witnessRecord;

  # THE THREAD MARKER (den-hoag-threadedforeign-substsubmodules-abort-srpix): what `threadedForeign`
  # hands a foreign `substSubModules`. nixpkgs types that argument as a module list, built as
  # `mergeOptionDecls` builds one (`setDefaultModuleLocation`): `[ { _file; imports = [ m ]; } ]`.
  # The marker is one such item whose import is an inert function module carrying the element
  # function, so a rebuild that CONSUMES the list as modules (`submoduleWith`, `attrTag`) evaluates
  # an empty module and states no marked element, and one that FORWARDS it reaches a gen element,
  # which answers with itself. `threadElementOf` reads the sentinel `_file` before `imports`, so a
  # real module list handed to a gen answerer by nixpkgs is never forced.
  threadMarkerFile = "<gen-merge thread marker>";
  threadMarker = refusal: f: [
    {
      _file = threadMarkerFile;
      imports = [
        {
          __functor = _: _: throw refusal;
          __genThreadElement = f;
        }
      ];
    }
  ];
  threadElementOf =
    m:
    let
      i =
        if isList m && length m == 1 && isAttrs (head m) && (head m)._file or null == threadMarkerFile then
          (head m).imports or null
        else
          null;
    in
    if isList i && length i == 1 && isAttrs (head i) && head i ? __genThreadElement then
      (head i).__genThreadElement
    else
      null;

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
      descriptionClass = "phraseClass | name, carries, payload";
    };
    foreignConstant = [
      "_type"
    ];
    nameCarried = [
      "name"
      "description"
    ];
  };

  # ── WHAT A DERIVATION DOES WITH EACH FIELD OF ITS BASE (den-hoag-5kic) ─────────────────────────
  # `types.deriveType` re-completes a SOURCE record cut from a completed base, and which fields cross
  # into it is this partition, as data beside `exportFields` for the reason `exportClasses` is: a
  # field gen's vocabulary gains and nobody classifies fails a cell by name (`ci/tests/derive-type.nix`
  # quantifies over every field a built type carries) rather than crossing as whatever a default makes
  # of it. `types.nix` reads the classes and never the names, so the foreign ones stay in this unit.
  #
  #   behaviour — the base's VALUE behaviour: crosses unread, which is what keeps the derivation's
  #               check and fold the base's.
  #   tied      — closed over the base's SELF or its CONSTRUCTOR, so each answers for the base: cut,
  #               and the ones that rebuild are lifted through the derivation again.
  #   identity  — the base's mint and what reads it (ADR-0034): a derivation is not its base, and
  #               never inherits them.
  #   derived   — this boundary's own output, re-derived when the source is exported again: the
  #               fourteen protocol fields and the two witnesses published beside them, gen-types'
  #               check witness and the rebuild's.
  #   datum     — the derivation's own record of what it was derived from.
  #
  # `nameCarried` fields are the only protocol fields a delta may restate. Every field outside these
  # classes is a caller's metadata, which a delta may set.
  deriveClasses = {
    behaviour = [
      "verify"
      "admits"
      "mergeDefs"
      "whenEmpty"
      "carries"
      "substructure"
      "deprecated"
      "unroledNested"
      "choose"
      "nests"
      "split"
      "specialArgs"
      "shorthandOnlyDefinesConfig"
      "__name"
      "__nameWithin"
    ];
    tied = [
      "typeMergeRel"
      "recarry"
      "retainedRelation"
      "withArgs"
      "_protoLeafMerge"
    ];
    identity = [
      "__mint"
      "__okAt"
      "__payload"
      "__sealed"
      "__typeSelf"
      "__staleStamp"
    ];
    derived = exportFields ++ [
      "_checkWitness"
      "_substSubModulesWitness"
      "phraseClass"
      "__phraseWithin"
    ];
    datum = [ "__derivation" ];
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

  # ── WHERE A GEN CONSTRUCTOR'S PARAMETERS EMBED IN A RICHER FOREIGN ONE ───────────────────────────
  # The foreign protocol keys a redeclaration on the FUNCTOR name, and for seven of gen's types it states
  # the construction under another name or with more parameters: `attrsOf`/`lazyAttrsOf` are one
  # `attrsWith` discriminated by `lazy` (at the default `placeholder`), `deferredModule` is
  # `deferredModuleWith` with no `staticModules`, gen-types' `string` is `str`, `path`/`pathLike`
  # are one `pathWith` at `absolute = true` and at no constraint, and gen-types' `number` is
  # `either int float` (a row whose parameters are TYPES, `members`; `rowOver`). Each gen type's parameters are a point
  # of that richer payload, so the export publishes the functor under the richer name with the fixed
  # parameters beside the role's key, and a gen relation facing a partner under that name joins it in
  # the partner's own relation over the same embedding (`joinCarriedInStatedRelation`). A row with no
  # `params` publishes a NULL payload (the protocol asserts two payloads agree on null-ness) and is
  # joined as a leaf at the richer name (`joinLeafInStatedRelation`). `joinsAs` names the record the
  # partner's join bears where it is not this type's own, and the witness reads names modulo it
  # (`joinRenames`). A ROW IS A CLAIM THAT THIS TYPE'S CHECK IS THE PARTNER'S AT THE EMBEDDED
  # PARAMETERS: both orders answer with the partner's record, so a row whose checks part swaps them.
  #
  # ★ A ROW IS REACHED BY THE CONSTRUCTION IT STANDS FOR, NEVER BY A NAME (den-hoag-n8cpq). A type's
  # name is the caller's wherever the vocabulary takes one (gen-types' `enum`, `struct`, `typedef`,
  # `mkOptionType`), so a name-keyed row served `enum "path" [ … ]` as nixpkgs' `path` with its own
  # check dropped. Every row is handed to the export (`types.nix` `defineEmbedded`) and to the
  # type's own relation by the gen-merge constructor that builds the type: the three container rows
  # by `attrsOf`/`lazyAttrsOf`/`deferredModule`, and the four leaf rows by the completion of the
  # leaf vocabulary (`default.nix` `completeExport`), which selects one by the MINT of the gen-types
  # leaf it completes (`embedsOf`; ADR-0034: a minted identity is consumable as a key). The
  # published `defineType` and `mkOptionType` hand none, so no caller-written record reaches a row:
  # a type of no row publishes under its own name, as before.
  embeddings = {
    # gen-types' `enum` (den-hoag-n8cpq item 2): nixpkgs' `enum` is gen-types' `enum` under no name,
    # both checks `elem v <members>`. Its parameter is an INSTANCE's, so this is the row's template:
    # the completion of the vocabulary's `enum` states it at the members it hands the constructor
    # (`default.nix` `completeParametric`), never read off a payload or a name.
    enum = {
      name = "enum";
      joinsAs = "enum";
      params.values = [ ];
    };
    attrsOf = {
      name = "attrsWith";
      params = {
        lazy = false;
        placeholder = "name";
      };
    };
    lazyAttrsOf = {
      name = "attrsWith";
      params = {
        lazy = true;
        placeholder = "name";
      };
    };
    deferredModule = {
      name = "deferredModuleWith";
      params.staticModules = [ ];
    };
    # leaves: no role, and the check is gen-types' (`checkers.nix` states the `pathWith` predicates)
    string = {
      name = "str";
      joinsAs = "str";
    };
    path = {
      name = "path";
      params = {
        absolute = true;
        inStore = null;
      };
    };
    pathLike = {
      name = "path";
      joinsAs = "path";
      params = {
        absolute = null;
        inStore = null;
      };
    };
    number = {
      name = "either";
      joinsAs = "either";
      members = [
        "int"
        "float"
      ];
    };
  };
  # The leaf rows by the digest of the leaf each stands for, bound once. A vocabulary lacking a leaf
  # or minting none for it reaches no row through it, and neither does one lacking a row's MEMBER or
  # minting none for it: the row is never formed, so the leaf publishes under its own name.
  mintOfLeaf = k: (types.${k} or { }).__mint.minted or null;
  leafEmbeddings = builtins.listToAttrs (
    prelude.concatMap
      (
        k:
        let
          d = mintOfLeaf k;
        in
        if
          builtins.isString d
          && builtins.all (m: builtins.isString (mintOfLeaf m)) (embeddings.${k}.members or [ ])
        then
          [
            {
              name = d;
              value = embeddings.${k};
            }
          ]
        else
          [ ]
      )
      [
        "string"
        "path"
        "pathLike"
        "number"
      ]
  );
  # A row whose parameters are TYPES (`members`: the vocabulary's leaves it is a union of) states
  # them at the completion, over the completed leaves `completed`, under the alternatives role's
  # payload key; every other row is its own. A members row therefore answers `? params` too, with
  # parameters that are not data: every `? params` reader asks `? members` FIRST (`types.nix`
  # `nullaryRel`, the export's `extrasAgree`), and that order is load-bearing, because the data join
  # (`joinCarriedInStatedRelation`) aborts uncatchably on a member list.
  rowOver =
    completed: row:
    if row != null && row ? members then
      row
      // {
        params.${roleSpelling.alternatives.payloadKey} = map (k: completed.${k}) row.members;
      }
    else
      row;
  # The functor names a row publishes (`attrsWith`, `deferredModuleWith`, `str`, `path`, …): a
  # completed record publishing none was completed under no row, so re-completing it loses nothing.
  rowFunctorNames = builtins.listToAttrs (
    map (r: {
      inherit (r) name;
      value = null;
    }) (builtins.attrValues embeddings)
  );
  # Whether `t` is a record this boundary completed under a row and still the record it completed
  # (its completion stamp holds), so re-completing it would lose the row (`types.nix` `defineType`).
  # The stamp, a cell-wise comparison of the whole record, is asked last.
  completedUnderRow =
    t:
    rowFunctorNames ? ${(t.functor or { }).name or ""}
    && builtins.isFunction (t.__typeSelf or null)
    && stampOk t;
  # Whether `other` is keyed under the name row `e` embeds in: the one place a relation asks it.
  keyedUnderEmbedding = e: other: e != null && (keyOf other) == e.name;
  # The leaf row `t`'s mint reaches, read only off the record its constructor (or this boundary)
  # COMPLETED: a `//` copy keeps its base's mark while changing what that mark stands for, so it
  # reaches none (gen-types' completion stamp, `stampOk`, which `restamp` re-ties at the import door).
  # The stamp is asked only of a record whose mint IS a leaf's. Read by the leaf completion
  # (`default.nix` `completeExport`) and by the join witness (`joinRenames`).
  embedsOf =
    t:
    if t ? carries then
      null
    else
      let
        r = leafEmbeddings.${t.__mint.minted or ""} or null;
      in
      # the record its completion produced (its stamp holds), or a `//` copy of it restating only
      # NAME-CARRIED fields (`exportClasses.nameCarried`, the fields a delta may restate, translating
      # nothing: the nixpkgs idiom `t // { description = …; }`), whose stamp holds once those are read
      # off its completion. Its check, fold and relation are its completion's, so it reaches the row
      # its mint does; a copy changing any other field (`verify`, `check`, a mint) does not.
      if
        r != null
        && builtins.isFunction (t.__typeSelf or null)
        && (
          stampOk t
          || stampOk (
            builtins.removeAttrs t exportClasses.nameCarried
            // builtins.intersectAttrs (builtins.listToAttrs (
              map (n: {
                name = n;
                value = null;
              }) exportClasses.nameCarried
            )) (t.__typeSelf null)
          )
        )
      then
        r
      else
        null;
  # A completed record's mint, `null` for any other: the leaf identity a row's TYPE-valued
  # parameter is decided by (ADR-0034's MINTED regime), read under the completion stamp exactly as
  # `embedsOf` reads a leaf's, so a raw `//` copy keeping its base's mark reaches none. The stamp
  # detects a raw copy and a copy re-completed through the published `defineType`, which keeps the
  # stale stamp a copy arrives with (`keepStamp`, den-hoag-59gnz).
  completedMintOf =
    t:
    let
      d = (t.__mint or { }).minted or null;
    in
    if isAttrs t && builtins.isString d && builtins.isFunction (t.__typeSelf or null) && stampOk t then
      d
    else
      null;
  # Two member lists agree position by position, each pair by its minted identity; pointer
  # equality is that regime's fast path (an equal record has an equal stamped mint), never a second
  # regime. A member with no mint (a foreign leaf) agrees with none of gen's.
  membersAgree =
    xs: ys:
    isList xs
    && isList ys
    && length xs == length ys
    && prelude.all (
      i:
      let
        x = elemAt xs i;
        y = elemAt ys i;
        dx = completedMintOf x;
        dy = completedMintOf y;
      in
      x == y || (dx != null && dy != null && dx == dy)
    ) (prelude.genList (i: i) (length xs));
  # The embedded payload: the role's key beside the embedding's fixed parameters. The one source for
  # the export's published payload and for the join (`joinCarriedInStatedRelation`).
  embeddedPayload =
    e: role: carried:
    if role == null && !(e ? params) then
      null
    else
      (if role == null then { } else { ${roleSpelling.${role}.payloadKey} = carried; })
      // (e.params or { });
  # What a RAW partner stating its relation under row `e`'s richer name offers at `role`:
  # the role's key read out of that payload, beside parameters gen does not carry. `null` where `e`
  # is no row or the partner is not stated under that name. Read only to NAME a refused pair, so
  # its reason is the element pair's, never a merge path of its own.
  embeddedOffered =
    e: role: t:
    let
      pf = t.functor or { };
    in
    if e == null || t ? carries || (pf.name or null) != e.name || !isAttrs (pf.payload or null) then
      null
    else
      pf.payload.${roleSpelling.${role}.payloadKey} or null;

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
    # a met record over a v2 join judges its own definitions (`meetOf`)
    if t ? __meetJoin && isV2 t then
      v2Fold t
    else if t ? _checkWitness && t ? check && t.check != t._checkWitness then
      checkedFold t (t.mergeDefs or leafFold)
    else if t._protoLeafMerge or false then
      null
    else if adHocChecked t then
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
  # a v2 type whose `check` is not the coherent one its constructor shipped: `type // { check = ...; }`
  adHocChecked = t: isV2 t && !(t.check.isV2MergeCoherent or false);
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
  # unequal. A record with no witness (a foreign descriptor) is not asked. A check rewritten over the
  # bare tree is not carried at its declared leaf, whose threaded fold reads none, and nixpkgs erases
  # it there too (the enumerated residue, README "The prices, stated"). A record re-bound by selection (`t // { inherit (t) check; }`) keeps the same
  # record and reads as its own on every evaluator. Four per-fold sites restate the test inline for
  # cost (`importedFold`, `modules.nix` `ownFold` and `threadedAs`, `types.nix` `isValid`), and the
  # library's construction door holds their spelling to this test (`lib/default.nix`).

  # Whether a value is inside a record's rewritten `check` as well as its gen domain: the member
  # choice of a union asks both (`types.isValid`), and the member's fold applies it (`checkedFold`).
  admitsCarried = t: v: !(rewritesCheck t) || t.check v;

  # What value does this type supply when nothing defined it? `{ }` is "it declares none" and is a
  # different fact from `{ value = null; }`, which is a declared null.
  importedEmpty = t: if (t.emptyValue or { }) ? value then { inherit (t.emptyValue) value; } else { };

  importedDeprecation = t: t.deprecationMessage or null;

  # A type's HEAD JUDGEMENT over a definition set (den-hoag-e6m9d): `null` when it takes them
  # whole, else why not. It is what nixpkgs' `merge.v2` reports as `headError` beyond the pointwise
  # check: a gen record states it beside its fold (`mergeDefs.headJudge`, published by the union
  # constructors), a foreign v2 type answers through its own `headError`, and any other type judges
  # no further than its definitions one by one.
  importedHeadJudge =
    t: loc: defs:
    if t ? mergeDefs.headJudge then
      t.mergeDefs.headJudge loc defs
    else if !(t ? typeMergeRel) && isV2 t then
      (v2Result (t.merge.v2 { inherit loc defs; })).headError.message or null
    else
      null;

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
  # ── THE SPINE: A FORWARDING CONTAINER'S MODULE SET AND DECLARATIONS, WITHIN FUEL (den-hoag-iaram) ─
  # A one-element container answers `getSubModules` and `getSubOptions` with its element's, the
  # second under the segment it adds. Both are observations of the TYPE, with no value to consume, so
  # on a cycle through containers alone (`r = nullOr (listOf r)`, contractive, so every value
  # observation of it serves) the forward never meets a node that answers for itself, and nixpkgs'
  # twin diverges on the same reads. The walk follows each forwarding step within the walk's fuel and
  # REFUSES BY NAME at exhaustion: neither `null` (no module set) nor `{ }` (no declarations) is
  # available there, since either is a silent wrong answer for a finite chain that deep over a
  # submodule. The first node that does not forward (a submodule, a union, a leaf, an unrecognised
  # foreign record) answers from its own substructure, as before.
  #
  # TWO KINDS OF STEP, AND ONLY ONE IS AN ANSWER. A gen container's step (`substructure.forward`, the
  # segment it adds on its way to `carries.element`) IS its answer, stated as data, so the walk answers
  # for it. A stock foreign record that forwards both
  # reads to one element (`listOf`, `nullOr`, `attrsWith`, `unique`, `functionTo`, `coercedTo`'s
  # `finalType`) is stepped for TERMINATION ONLY: once the rest of its chain is shown to bottom out,
  # the record answers for itself, so one whose sub-protocol was overridden after construction answers
  # its override, as nixpkgs' own container over it does. A cycle that crosses the import boundary on
  # every lap is bounded, because each crossing is a step of the same walk.
  #
  # ★ THE PRICE, STATED: a FINITE chain of more than `importedTypeWalkFuel` forwarding steps below a
  # container is refused on these two reads where it was answered, and so is a cycle passing through a
  # stock foreign container whose override stops forwarding (base answered the override). Both are
  # refusals by name. ★ THE ESCAPE HATCH (S2's posture, den-hoag-n6dh7): a record whose `substructure`
  # states no `forward` answers for itself, so stating a container's substructure ends the walk there.
  forwardStep =
    e:
    if !(isAttrs e) then
      null
    else if e ? substructure then
      if e.substructure ? forward then
        {
          name = nameOf e;
          element = e.carries.element;
          seg = if e.substructure.forward == null then [ ] else [ e.substructure.forward ];
        }
      else
        null
    else
      let
        name = (e.functor or { }).name or null;
        nested = e.nestedTypes or { };
        element =
          if name == "coercedTo" then
            nested.finalType or null
          else if
            name == "listOf"
            || name == "nullOr"
            || name == "attrsWith"
            || name == "unique"
            || name == "functionTo"
          then
            nested.elemType or null
          else
            null;
      in
      if isAttrs element then { inherit name element; } else null;
  forwardSpentRefusal =
    field: name:
    "gen-merge: cannot read `${field}' of the option type `${name}': its element chain forwards through "
    + "more containers than the walk's fuel (${toString importedTypeWalkFuel}), as a cycle through "
    + "containers alone does and as a finite chain nested that deep does. Close a cycle through a "
    + "union (either, oneOf) or a submodule, which answer for themselves; nest a finite chain less "
    + "deeply";
  # Does the chain from `e` reach a node that answers for itself within `fuel`? `true`, or the refusal.
  spineEnds =
    field: fuel: e:
    let
      st = forwardStep e;
    in
    if st == null then
      true
    else if fuel <= 0 then
      throw (forwardSpentRefusal field st.name)
    else
      spineEnds field (fuel - 1) st.element;
  spineModules =
    fuel: e:
    let
      st = forwardStep e;
    in
    if st == null then
      (importedSubstructure e).modules
    else if fuel <= 0 then
      throw (forwardSpentRefusal "getSubModules" st.name)
    else if e ? substructure then
      spineModules (fuel - 1) st.element
    else
      builtins.seq (spineEnds "getSubModules" (fuel - 1) st.element) (importedSubstructure e).modules;
  spineDeclares =
    fuel: e: prefix:
    let
      st = forwardStep e;
    in
    if st == null then
      (importedSubstructure e).declares prefix
    else if fuel <= 0 then
      throw (forwardSpentRefusal "getSubOptions" st.name)
    else if e ? substructure then
      spineDeclares (fuel - 1) st.element (prefix ++ st.seg)
    else
      builtins.seq (spineEnds "getSubOptions" (fuel - 1) st.element) (
        (importedSubstructure e).declares prefix
      );

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

  # A descriptor carrying a `substructure` BESIDE a callable `substSubModules` is a copy of a built
  # record (`base // Δ`), and the copy states its rebuild in one of the two fields, carrying the
  # other from the base. Which one the author overrode is read off the witness `exportType`
  # publishes beside `substSubModules` (`_substSubModulesWitness`, the check-witness pair's
  # construction): a `substSubModules` that no longer holds its witness was rewritten (gen-schema's
  # `refined`), and is the copy's own rebuild, the one nixpkgs' `fixupOptionType` calls on the outer
  # type; the `substructure.rebuild` the base's export derived it from is TIED, closed over the base
  # (`deriveType`'s note), and would drop the copy's layer. A `substSubModules` still holding its
  # witness is the base's, carried along stale, so the copy's `substructure` decides, as it does for
  # a copy that restated its rebuild there. The module set and the declarations are data, not tied,
  # and cross as carried. The fields are bound as formals, so the rebuild is the descriptor's own
  # value and the import allocates no thunk for it: this runs once per imported instance (perf-bench
  # `schemaHosts`).
  importedOwnSubstructure =
    {
      substructure ? null,
      substSubModules ? null,
      _substSubModulesWitness ? null,
      ...
    }@t:
    # gen-types' `rewritesCheck`, restated inline for cost over the rebuild's pair.
    if
      substructure != null
      && _substSubModulesWitness != null
      && substSubModules != _substSubModulesWitness
      && (isFunction substSubModules || isAttrs substSubModules && substSubModules ? __functor)
    then
      substructure // { rebuild = substSubModules; }
    else
      importedSubstructure t;

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

  # ── THE IDENTITY A RELATION KEYS ON (den-hoag-5kic) ─────────────────────────────────────────────
  # A type's `name` is its VALUE VOCABULARY, the word its messages speak, and for every type a
  # constructor builds it is also the identity a relation decides on. A DERIVATION
  # (`types.deriveType`) keeps its base's name and carries its own identity in `__derivation.id`, so a
  # relation reading the name would merge it with its base and drop it silently. Every gen relation
  # that decides by identity reads it here — one total reader, as `nameOf` is for a refusal's wording
  # — and `exportType` publishes the same identity as the functor name a foreign engine keys on. On
  # a record without the datum it is the name, so nothing built otherwise moves.
  keyOf =
    x: if isAttrs x && x ? __derivation then "derivation:${x.__derivation.id}" else x.name or null;

  # ── THE NAME THAT GOVERNED ──────────────────────────────────────────────────────────────────────
  # The foreign protocol keys a redeclaration on the FUNCTOR name, not the type name (`protoTypeMerge'
  # below, and the derived `typeMerge' in `exportType'). A type derived from another keeps its base's
  # `name', the value vocabulary its messages speak, and distinguishes only its functor. So a refusal
  # naming the pair by type name alone reads "`int' and `int'" in exactly the case the functor names
  # decided, which looks like a self-contradiction. Where both operands state a functor name and the
  # two differ, this answers them, read through `nameOf'; otherwise `null' and the refusal is
  # unchanged.
  functorNamesOf =
    a: b:
    let
      functorOf =
        x: if isAttrs x && isAttrs (x.functor or null) && x.functor ? name then x.functor else null;
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

  # ── THE TYPES nixpkgs' `internalModule` DECLARES ─────────────────────────────────────────────────
  # Whether a module's re-declaration of an engine-owned `_module.<k>` states a type nixpkgs'
  # `mergeOptionDecls` merges with that module's own: `args` is `lazyAttrsOf raw`, `check` `bool`,
  # `freeformType` `nullOr optionType`. Each own type's `typeMerge` is a test of functor names (and,
  # for `attrsWith`, of `lazy`), so this reads the declared type's names in both vocabularies'
  # spellings. `specialArgs` declares no type, so every type merges there.
  moduleOwnTypeAdmits =
    k: t:
    let
      named = n: (t.functor.name or null) == n;
      elem = t.nestedTypes.elemType.name or null;
    in
    {
      args =
        elem == "raw" && (named "lazyAttrsOf" || named "attrsWith" && (t.functor.payload.lazy or false));
      check = named "bool";
      freeformType = named "nullOr" && elem == "optionType";
      specialArgs = true;
    }
    .${k};

  # The sub-options a `submodule`-typed `_module` leaf's own submodule declares at `loc`, as
  # `{ judged; options; }`. gen's `types.submodule` states a record's fields as they were declared,
  # so its records are judged by the caller as they stand. A nixpkgs record states
  # `type = unspecified` for a declaration that states none, so an explicit `unspecified` cannot be
  # told from no type there, and a nixpkgs leaf is judged by nixpkgs, as nixpkgs judges it: the
  # engine's own declarations (`own`, which of `default` and `description` each states, beside the
  # type every key but `specialArgs` declares) are read off nixpkgs' own `_module` options in the
  # same evaluation and added last to its modules, where nixpkgs adds its `internalModule`, so they
  # fold first. An owned key's record is kept only where a leaf module declares it too, so reading
  # it runs nixpkgs' `mergeOptionDecls` over both. What that leaves the caller is the fields the
  # engine itself runs; a merged type is not one of them, so the `unspecified` one is taken off.
  moduleLeafSubOptions =
    own: t: loc:
    if t ? carries then
      {
        judged = false;
        options = t.getSubOptions loc;
      }
    else
      let
        ownModule = {
          _file = "<the engine's own _module options>";
          options = builtins.mapAttrs (
            k: fields:
            {
              _type = "option";
            }
            // builtins.intersectAttrs (
              if k == "specialArgs" then fields else fields // { type = true; }
            ) sub._module.${k}
          ) own;
        };
        sub = (t.substSubModules (t.getSubModules ++ [ ownModule ])).getSubOptions loc;
      in
      {
        judged = true;
        # Per key, so a reader of one key forces one record; `null` where no leaf module declares it.
        options = builtins.mapAttrs (
          k: _:
          if length sub.${k}.declarations == 1 then
            null
          else if sub.${k}.type.name == "unspecified" then
            builtins.removeAttrs sub.${k} [ "type" ]
          else
            sub.${k}
        ) own;
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
  # change and this is the only site that states it. Its readers include this pre-flight, which is
  # also the gen relation's at each of its entries (`lib/modules.nix` `relationMerge`,
  # `exportType`'s `typeMerge` and `binOp`), and the spine (`spineModules`, `spineDeclares`).
  importedTypeWalkFuel = 32;

  importedDecidable =
    let
      go =
        fuel: t:
        if !(isAttrs t) then
          true
        else if fuel <= 0 then
          false
        # A gen nesting type's relation unions module SETS and descends into no type, so the walk
        # stops there as it does at a foreign record evaluating its own roles: its carried modules
        # are not types and are not forced (den-hoag-iaram, the gen relation's pre-flight).
        else if evaluatesOwnRoles t || isNesting t then
          true
        # A gen record carrying its element alone (a one-element container) steps straight to it, the
        # node `importedWrapped` would list alone, without building that list (den-hoag-iaram: the
        # walk is the gen relation's pre-flight on every redeclaration, so its per-level constant is
        # paid there). A record with more than one role takes the general arm.
        else if t ? carries && attrNames t.carries == [ "element" ] then
          go (fuel - 1) t.carries.element
        # A record that wraps nothing (no `carries`, no `nestedTypes`) is a leaf, decidable at once:
        # `importedWrapped` would answer `[ ]` for it, so the walk answers without building that list
        # (den-hoag-c7uhw: every declared-type fold step asks this of both operands). `{ }` stands on
        # the left as in `importType0`: `==` first asks whether its LEFT operand is a derivation, which
        # would force a `nestedTypes.type` member the general arm does not force first.
        else if !(t ? carries) && { } == (t.nestedTypes or { }) then
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
  # (`carries`) never pays the read.
  #
  # ★ THE STATED RESIDUE: a record stating both and ALSO a static role in `nestedTypes` is served as
  # a module set with that role unread (no test that leaves `nestedTypes` unread can separate it);
  # one whose payload states no `modules`, or which states no `getSubModules`, is not recognised and
  # keeps the operand-alone evaluation and its refusal. "Served" holds for an HONEST record only: a
  # recognised record answers `importedDecidable` without a walk, so its own `typeMerge` runs
  # unguarded, and a hand-built one recursing through itself overflows the stack uncatchably where
  # the fuel refused it by name. What its `freeformType` wraps is unread too: a gen nesting type
  # there evaluates standalone through the bridge, and the lint does not scan it.
  evaluatesOwnRoles =
    t:
    !(t ? carries)
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
        else if isNesting t || t ? __threadedForeign then
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
  # what it carries.
  declaredWrapped =
    t:
    # No binding on the common path: `canNest` asks this of every option the engine folds, so one
    # there is paid per instance. A record with `carries` or a non-empty `nestedTypes` answers
    # `importedWrapped` whole. Past that, the one carrying spelling `statedRoles` can still reach is
    # a top-level `elemType`, so only a record stating one pays for the reading.
    if t ? carries || (!(evaluatesOwnRoles t) && { } != (t.nestedTypes or { })) then
      importedWrapped t
    else if t ? elemType then
      [ (statedRoles t).element ]
    else
      [ ];

  # What a record's functor payload OFFERS to merge on as an element or members; `[ ]` for a record
  # with `carries`. Read only where `declaredWrapped` is empty, and only to
  # JUDGE the offer: the walk below refuses a record offering a type that declares a gen nesting type
  # while stating none (OQ1 arm (ii-a), *defaulted, reversible*), and never takes the offer as a
  # declaration.
  payloadOffered =
    t:
    let
      payload = (t.functor or { }).payload or null;
      role = payloadRole payload;
    in
    if t ? carries then
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
        if !(isAttrs t) then
          false
        else if t ? declaresNesting then
          (
            let
              marker = declaresNestingMarkerRefusal t;
            in
            if marker == null then false else throw marker
          )
        else if isNesting t then
          true
        else
          let
            wrapped = declaredWrapped t;
          in
          if wrapped == [ ] then
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
      name = (t.functor or { }).name or null;
    in
    # everything past the name is bound only past the functor-name test: a door asks this of every
    # foreign record stating an element, so a binding ahead of it is paid per instance
    if
      !(isAttrs t)
      || t ? carries
      || !(name == "attrsWith" || name == "listOf" || name == "nullOr" || name == "either")
    then
      null
    else
      let
        payload = t.functor.payload or null;
        keys = if isAttrs payload then attrNames payload else [ ];
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

  # THE RECOGNITION DOOR: asked through it, `importedRehomeAt` answers its recognition and never
  # judges the payload's offer (`rehomeAgreed`), so it refuses nothing. The type-time mark
  # (`mayFoldNested`) asks through it, so the mark's foreign arm is the exact complement of what
  # re-homing recognises: ONE recognition, and a stock-named record whose payload or statement it
  # does not recognise is threaded, and is marked. A door rather than a second binding, so
  # re-homing's own call pays nothing for it (`homedAt` asks per position).
  recognitionDoor = "the type-time mark";

  # A recognition `r` of `t`, or the disagreement refusal where its payload offers another element
  # than the carrying spelling states. Two elements are the same type when their `check` and `merge`
  # are the same closures: a stock record states one value in both places, so the two are
  # pointer-equal there, and two separate constructions differ. Only those two slots are compared,
  # never the records whole: `==` on two distinct type records forces every attribute, and a
  # self-referential `description` (nixpkgs' `types.json` shape) then recurses uncatchably; a
  # compared record's `type` would be forced as well. `closuresOf` is not used here: it filters the
  # export fields by `isFunction`, which forces that same `description`.
  rehomeAgreed =
    door: loc: t: r:
    if door == recognitionDoor then
      r
    else
      let
        slots =
          x:
          builtins.intersectAttrs {
            check = null;
            merge = null;
          } x;
        same = a: b: isAttrs a && isAttrs b && (slots a == slots b);
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
          # record's check is carried on every re-home, and gen's own fold applies it as a
          # rewritten check (`checkedFold`). One that reaches the nested tree reads the tree's
          # `check`, its module-value domain (den-hoag-f8mgj arm Q).
          rebuilt // { inherit (t) check; }
        )
      else if declaresNestingAt door loc t then
        threadedForeign door loc t
      else
        t;

  # MAY this type be a CONTAINER NODE at an exact container's element, at its own position or
  # through a container below it? Gen's own union, or the stock foreign `either` that `homedAt`
  # re-homes as one; a split container other than `nullOr` and the attribute-keyed two (a `listOf`,
  # or another split container such as gen-aspects' `aspectsRoot`), or the stock `listOf`; an
  # `attrsOf` whose element may be a container (`mayBeContainer`), which `modules.keyedOverAt` makes
  # a node where that element would itself key over-approximately; a foreign container re-homing does not recognise (`importedRehomeAt`, asked through
  # `recognitionDoor`), which `homedAt` threads; through a gen container's element and a stock
  # foreign `nullOr`'s, which over-approximates, since `nullOr` is the one container besides a union
  # that adds no step. Read without homing, so it refuses nothing: an exact container asks it once,
  # when it is built, to decide whether its elements carry the container-node mark
  # (`types.exactThread`). The mark may over-approximate the walk's nodes, never under-approximate
  # them: the fold re-asks the walk's own predicate where the mark is set (`modules.unionNodeAt`).
  # Bounded by `importedTypeWalkFuel` and `true` AT EXHAUSTION, `canNest`'s posture: a wrong `true`
  # marks a position that folds no union, which allocates the mark and nothing else, where an
  # unbounded descent through a cycle of containers alone never returns (den-hoag-iaram).
  mayFoldNested =
    let
      go =
        fuel: t:
        isAttrs t
        && !(isNesting t)
        && canNest t
        && (
          if t ? carries then
            t ? choose
            || (
              t ? split
              && !(builtins.elem (t.name or null) [
                "nullOr"
                "attrsOf"
                "lazyAttrsOf"
              ])
            )
            || ((t.name or null) == "attrsOf" && mayBeContainer t.carries.element)
            || (t ? carries.element && (fuel <= 0 || go (fuel - 1) t.carries.element))
          else
            let
              r = importedRehomeAt recognitionDoor null t;
            in
            # a record re-homing does not recognise is threaded (`threadedForeign`), and is keyed where
            # read under an exact container, as a union is (`keyWalk`, `unionNodeAt`)
            r == null
            || r.container == "either"
            || r.container == "listOf"
            || (r.container == "attrsOf" && mayBeContainer r.element)
            || (r.container == "nullOr" && (fuel <= 0 || go (fuel - 1) r.element))
        );
    in
    go importedTypeWalkFuel;
  # MAY this element be a container the key walk's `containerMemberAt` holds? The type-time
  # answer, read without homing, which over-approximates: a split container other than `nullOr` (a
  # gen union states `split`, so every union answers yes), or one looked through `nullOr`; a foreign
  # record answers yes. An `attrsOf` over such an element may be a container node at an exact
  # container's element (`modules.keyedOverAt`), so it is marked. Bounded as `mayFoldNested` is.
  mayBeContainer =
    let
      go =
        fuel: e:
        isAttrs e
        && !(isNesting e)
        && canNest e
        && (
          if e ? carries then
            (e ? split && (e.name or null) != "nullOr")
            || (e ? carries.element && (fuel <= 0 || go (fuel - 1) e.carries.element))
          else
            true
        );
    in
    go importedTypeWalkFuel;

  # ── THE ROOT FIX-UP: WHERE NIXPKGS REBUILDS A TYPE, GEN DOES (den-hoag-threadedforeign-parity-residue-0hew4, den-hoag-gijly) ─
  # nixpkgs' `fixupOptionType` mounts a declared option's type as `t.substSubModules` over the
  # declaration's module set when `t.getSubModules` is non-null, and `t` otherwise, at the option's
  # ROOT only; the rebuild reaches what the root's own `substSubModules` forwards to, and nothing
  # below a container stating no module set (`either`, `oneOf`). Gen's evaluation does the same at
  # the same place, for every foreign root stating a module set:
  #   - one declaring NO gen nesting element is mounted as that rebuild, whose merge is the one
  #     served, and its own `check` rides on it (`carriedCheck`); a rebuild that is not an option
  #     type is refused by name (`rootRebuildRefusal`); the rebuild is judged before any read of the
  #     record's roles, so a copied submodule's `nestedTypes` is never forced (den-hoag-2lmky);
  #   - one declaring a gen nesting element its marker rebuild does not thread (`threadsAt`) is
  #     mounted as that rebuild where the result declares no gen nesting element; otherwise its
  #     homing threads or refuses by name as before.
  # `site` is the caller's own record, read only past the presence tests (`isOptionRoot`). A gen
  # record (`substructure`, `carries`, `verify`, a nesting type) is gen's own fold, unchanged.
  # The mount's cost, and its measured out (den-ag-design
  # reports/den-hoag-gijly-oq2-mount-cost-scout-v0.md, gen-merge 359a36f, nix/Determinate/Lix): on
  # stock submodule roots, against nixpkgs' own evaluation of the same workload, the full mount costs
  # +4.8% thunks and +2.5-3.7% bytes. The alternative, skipping the rebuild for a recognised intact
  # v2 record (`unifiedR`), is 10% cheaper than nixpkgs there, and saves nothing on `attrsOf
  # submodule`. It is not taken: it serves nixpkgs' value silently wrong over a class no witness
  # detects, any record whose `substSubModules`, `getSubModules` or functor payload differs from its
  # rebuild, an override assembled from stock parts included (`ySub // intersectAttrs {
  # substSubModules = null; } donor` reads as intact). Adopting it needs a fresh owner reading, and
  # its ADR-0025 item 1 exception must name that whole class (den-hoag-gijly).
  homedRootAt =
    door: loc: site: t:
    # presence first, with no binding: every option's root passes here, and a gen root or a leaf
    # pays these tests and nothing else
    if
      !(isAttrs t)
      || t ? verify
      || (t ? carries || t ? substructure) && !(crossedRoot t)
      || isNesting t
      || !(isList (t.getSubModules or null))
    then
      homedAt door loc t
    else
      homedRootFixed door loc site t;
  # Does this gen record state a `mount` (a module set that crossed the `mkOptionType` door,
  # `importType`), or carry an element that does? Its root is mounted as a foreign one is. A
  # container's module set IS its element's (`listOf`, `attrsOf`, `nullOr`), so it forwards the
  # mount as nixpkgs' `substSubModules` forwards to the element's; `either` carries no element and
  # states no module set, and is never mounted. The class is re-tested on the record handed in, never
  # trusted from the door: `importedSubstructure` copies a stated `substructure` wholesale, so a
  # crossed record passed through the door again with a `verify` (gen-schema's `refined`), overridden
  # ad hoc (`// { check }`) or with its module set nulled (`// { getSubModules = null; }`) still
  # states the mark it was given at its first crossing.
  #
  # Bounded by `importedTypeWalkFuel`, and `false` AT EXHAUSTION: a cycle through containers alone
  # (`cyclic-types`) reaches no crossed record, and `mountOf` follows only a walk that found one. THE
  # PRICE, stated: a crossed record nested that many containers deep keeps its own merge, as before
  # the mount.
  crossedRoot =
    let
      go =
        fuel: t:
        isAttrs t
        && (
          t ? substructure.mount && !(t ? verify) && isList (t.getSubModules or null) && !(adHocChecked t)
          ||
            fuel > 0
            && t ? recarry
            && t ? carries.element
            && (t.carries.element ? substructure.mount || t.carries.element ? carries.element)
            && go (fuel - 1) t.carries.element
        );
    in
    go importedTypeWalkFuel;
  # Is the position an OPTION ROOT? An evaluation's option (its fold's mode states the `reader`) or
  # a declared option's group; not the freeform group, whose type is no option's, nor the value-only
  # `mergeOption`'s option. nixpkgs fixes up neither.
  isOptionRoot = site: site ? reader || site ? hostMode && site.name != "freeform";
  homedRootFixed =
    let
      # The mount over a module set: the door record's own rebuild with the record's own `check` riding on
      # it (`carriedCheck`, den-hoag-4ifgb M-B), built from the record handed in, or the container rebuilt
      # over its element's (`recarry`, the container's own rebuild over another payload).
      mountOf =
        t: m:
        if t ? substructure.mount then
          let
            r = t.substructure.rebuild m;
          in
          if isAttrs r && r ? merge && r ? check && t ? check then r // { check = carriedCheck t r; } else r
        else
          t.recarry (t.carries // { element = mountOf t.carries.element m; });
    in
    door: loc: site: t:
    let
      # a foreign container is rebuilt over its element's own rebuild carrying the element's check
      # (`carriedAtDepth`); a module set's own root rebuilds as it always did
      s =
        if crossedRoot t then
          mountOf t
        else if t ? functor.payload.elemType then
          carriedAtDepth false t
        else
          t.substSubModules or null;
      # the shape `mergeOptionDecls` hands a rebuild, labelled as nixpkgs labels a module that states
      # no file
      fixed = s (
        map (m: {
          _file = "<unknown-file>";
          imports = [ m ];
        }) t.getSubModules
      );
      mountable =
        (isFunction s || isAttrs s && s ? __functor) && isAttrs fixed && fixed ? merge && fixed ? check;
      # judged on the record as written (a re-homing disagreement), then mounted as the rebuild over
      # the real module set, whose merge is the one served, the record's own `check` riding on it
      mounted = builtins.seq (importedRehomeAt door loc t) (
        homedAt door loc (fixed // { check = carriedCheck t fixed; })
      );
    in
    # the rebuild first, before any read of the record's own roles (a0c4z: never take a read nixpkgs
    # never takes): at an option root, a rebuild that is an option type declaring no gen nesting
    # element is mounted; an ad-hoc `check` keeps `adHocFold`
    if isOptionRoot site && !(adHocChecked t) && mountable && !(declaresNestingAt door loc fixed) then
      mounted
    else if !(statesWrapped t && declaresNestingAt door loc t) then
      # no gen nesting element: a rebuild that is not an option type is refused by name
      (
        if !(isOptionRoot site) || adHocChecked t then
          homedAt door loc t
        else if !mountable then
          throw (rootRebuildRefusal door loc t)
        else
          mounted
      )
    else if !(isFunction s || isAttrs s && s ? __functor) then
      homedAt door loc t
    else
      let
        threads = threadsAt door loc t;
      in
      if threads then
        # one verdict for the root: an unrecognised container threads with it, a recognised one is
        # re-homed as before
        (
          if importedRehomeAt door loc t == null then
            threadedForeignWith threads door loc t
          else
            homedAt door loc t
        )
      else if isAttrs fixed && fixed ? merge && !(declaresNestingAt door loc fixed) then
        homedAt door loc fixed
      else
        homedAt door loc t;

  # THE RECORD'S OWN `check` RIDES ON THE ROOT'S REBUILD, as on every re-home (den-hoag-4ifgb M-B,
  # `homedAt`): a refinement `{ x : F e | p x }` is not part of the functor, so `addCheck` over a
  # module-set root is rebuilt away unless carried. The rebuild's own `check` stays, so the domain is
  # the meet of the two; a v2 merge reads it as the coherent check its constructor would ship.
  carriedCheck = t: fixed: {
    __functor = _: x: fixed.check x && t.check x;
    isV2MergeCoherent = true;
  };
  # THE SAME CARRIAGE OVER A DECLARATION LIST AND AT EVERY DEPTH (den-hoag-8ip0d). `carriedAtDepth true ts
  # r` is the rebuild `r` restricted by every check in `ts` (the records it was rebuilt from) that it
  # cannot carry, its element rebuilt over the same carriage of their elements; `carriedAtDepth false t
  # m` is `t.substSubModules m` with its element so carried, as `fixupOptionType`'s rebuild forwards to
  # the element's. A rebuild erases a wrapper at the element as at the root, and a declaration fold joins
  # module sets without one (`metWith`), so neither depth is enforced unless carried. A gen record
  # stating its own check owes nothing (gen relations are exact); a foreign one is owed
  # unconditionally, since a foreign wrapper states no witness (`homedAt`'s carriage, den-hoag-4ifgb
  # M-B, reads it the same way). The walk descends through a record that owes nothing itself to an
  # element that does, a gen container's included (`owesIn`). An owed AD-HOC override
  # (`type // { check = ...; }`) is refused by name at any depth (`adHocFold`, den-hoag-ku5dt Q1), as it
  # is alone: the carried record is that override, so each reader that folds it refuses it.
  #
  # Bounded by `importedTypeWalkFuel`. THE PRICE, stated: a wrapper nested that many containers deep is
  # not carried, as `crossedRoot` states for the mount.
  carriedAtDepth =
    let
      owes = o: isAttrs o && (!(o ? typeMergeRel) || rewritesCheck o);
      # `owes`, inlined: it is asked once per element of every rebuild
      owesIn =
        fuel: o:
        isAttrs o
        && (
          !(o ? typeMergeRel) || rewritesCheck o || fuel > 0 && owesIn (fuel - 1) (carriedAt "element" o)
        );
      over =
        r: e:
        if r ? recarry && r ? carries.element then
          r.recarry (r.carries // { element = e; })
        else
          rebuiltOverAt "element" e r;
      below =
        fuel: ts: r:
        let
          es = filter (e: owesIn fuel e && isList (e.getSubModules or null)) (map (carriedAt "element") ts);
          re = carriedAt "element" r;
          x = over r (go false (fuel - 1) es re);
        in
        if fuel <= 0 || es == [ ] || !(isAttrs re) then
          r
        else if isAttrs x then
          x
        else
          r;
      # `adHocChecked`, the coherence mark read first: every owed record is asked
      isAdHoc = o: !(o.check.isV2MergeCoherent or false) && isV2 o;
      go =
        top: fuel: ts: r:
        let
          owed = filter owes ts;
          c0 = (head owed).check;
          c1 = (elemAt owed 1).check;
          adHoc = filter isAdHoc owed;
        in
        if owed == [ ] then
          below fuel ts r
        else
          carryBy top (
            if adHoc != [ ] then
              head adHoc
            else if length owed == 1 then
              head owed
            else
              # the owed checks' conjunction, as one record's
              {
                check = if length owed == 2 then (x: c0 x && c1 x) else (x: builtins.all (o: o.check x) owed);
              }
          ) (below fuel ts r);
      # `r` restricted by the owed record `o`'s check, or refused by name where `o` is an override
      carryBy =
        top: o: r:
        let
          holds = o.check;
        in
        if isAdHoc o then
          # a root keeps the override's own `check`, which routes the mount to the fold (`homedRootFixed`); an
          # element keeps its coherent one, so a foreign container's fold reaches the merge. Its rebuild is
          # refused the same way, so a later rebuild (the mount's, over the fixup's) does not erase it.
          r
          // {
            merge = {
              __functor =
                _: loc: defs:
                adHocFold o loc defs;
              v2 = args: adHocFold o args.loc args.defs;
            };
          }
          // (
            if r ? substSubModules then { substSubModules = m: carryBy top o (r.substSubModules m); } else { }
          )
          // (if top then { inherit (o) check; } else { })
        else
          r
          // {
            check = {
              # a FOREIGN carrier's own check is asked elsewhere: a declaration list's root is mounted, and
              # the mount meets its rebuild's (`homedRootFixed`); a v2 element's merge computes its own
              # `headError`. A gen carrier and a v1 element are asked it here.
              __functor = if r ? typeMergeRel || !top && !(isV2 r) then _: x: r.check x && holds x else _: holds;
              isV2MergeCoherent = true;
            };
          }
          # an element's v2 merge judges its own definitions inside a foreign container's fold, which reads
          # no `check`, so the owed checks ride on its `headError` too, as nixpkgs' `addCheck` places its
          # own; a root's `check` is what gen's checked fold reads (`importedFold`), and it pays no merge
          # wrapper
          // (
            if !top && isV2 r then
              {
                merge = {
                  __functor =
                    self: loc: defs:
                    (self.v2 { inherit loc defs; }).value;
                  v2 =
                    args:
                    let
                      v = r.merge.v2 args;
                    in
                    if v.headError != null || builtins.all holds (builtins.catAttrs "value" args.defs) then
                      v
                    else
                      v
                      // {
                        headError.message = "a definition is rejected by the check of a declaration of this option";
                      };
                };
              }
            else
              { }
          );
      carryElement = carryBy false;
      # `t.substSubModules m`, with an owing module-set element rebuilt by the same function, carried, and the
      # container rebuilt over it by its own constructor: one rebuild per level, as nixpkgs' forwarding does.
      # An element stating no element of its own is carried directly.
      rebuild =
        fuel: t: m:
        let
          e = carriedAt "element" t;
          c =
            if carriedAt "element" e == null then
              carryElement e (e.substSubModules m)
            else
              go false (fuel - 1) [ e ] (rebuild (fuel - 1) e m);
          # `over t c`, inlined: it is asked once per mounted root
          x =
            if t ? recarry && t ? carries.element then
              t.recarry (t.carries // { element = c; })
            else
              rebuiltOverAt "element" c t;
        in
        if fuel > 0 && owesIn fuel e && isList (e.getSubModules or null) && isAttrs x then
          x
        else
          t.substSubModules m;
    in
    top: if top then go true importedTypeWalkFuel else rebuild importedTypeWalkFuel;

  rootRebuildRefusal =
    door: loc: t:
    "gen-merge: `${door}' at option `${showOption loc}': the option type `${nameOf t}' states a module "
    + "set (`getSubModules'), and its `substSubModules' rebuild over that set is not an option type. "
    + "An option root stating a module set is mounted as that rebuild (fixupOptionType), here as in "
    + "the module system it comes from. Make `substSubModules' return an option type, or state `getSubModules = null' "
    + "where the type carries no module set";

  # The rebuild of a foreign container over the thread marker, and whether it THREADS: judged on
  # the ORIGINAL record, position by position (`threadsAt`). `null` where the record has no rebuild
  # to call (nixpkgs never calls one where `getSubModules` is null, so an absent or null one
  # rebuilds nothing).
  rebuiltOver =
    refusal: t: f:
    let
      s = t.substSubModules or null;
    in
    if isFunction s || isAttrs s && s ? __functor then
      s (threadMarker refusal (e: f e // { __genThreadMark = true; }))
    else
      null;

  # A record's declared positions, by name, as the walks read them (`declaredWrapped`'s reading,
  # keyed): `nestedTypes` unless it is an output of the record's own evaluation (a0c4z), and a
  # top-level `elemType`. An `attrTag` tag is an option record, read at its type.
  positionsOf =
    t:
    let
      nested = if isAttrs t && !(evaluatesOwnRoles t) then t.nestedTypes or { } else { };
      asType = v: if isAttrs v && (v._type or null) == "option" then v.type else v;
    in
    if !(isAttrs t) then
      { }
    else
      prelude.mapAttrs (_: asType) (nested // (if t ? elemType then { inherit (t) elemType; } else { }));

  # DOES THE MARKER REBUILD THREAD? Judged on the ORIGINAL record against its rebuild, position by
  # position, never on what the rebuild says it consumed:
  #   - every position the original declares that MAY NEST comes back in the rebuild as the marked
  #     element (a gen record), or as a record that threads in turn by this same rule;
  #   - every position the original declares that may NOT nest is a SIBLING the rebuild also hands
  #     the marker to. It must not substitute: its own `substSubModules` over the marker answers
  #     `null` (it has no module set to lose: a leaf, `either`), and the rebuild keeps it as an
  #     option type. A sibling that answers anything else would receive the marker in place of the
  #     module set nixpkgs leaves it, whether it evaluates the list (`submoduleWith`), stores it
  #     (`deferredModuleWith`), relabels it, or drops `getSubModules` from its rebuild.
  # A sibling's answer is a value, read to weak head normal form only; a rebuild that reads the
  # marker as modules meets its import, which throws the import refusal (`threadMarker`), so a
  # consumer the declarations do not show still refuses by name, never folding an empty module.
  # Bounded by the walks' fuel, refusing by name at exhaustion, as `declaresNestingAt` does.
  threadsAt =
    door: loc: t:
    let
      refusal = nestingImportRefusal door loc t;
      marker = threadMarker refusal (e: e);
      sibling =
        o: r:
        let
          s = if isAttrs o then o.substSubModules or null else null;
        in
        (!(isFunction s || isAttrs s && s ? __functor) || s marker == null) && isAttrs r && r ? merge;
      go =
        fuel: o: r:
        if o ? carries || isNesting o then
          isAttrs r && (r ? __genThreadMark || !(canNest o) && r ? merge)
        else if fuel <= 0 then
          throw refusal
        else
          let
            po = positionsOf o;
            pr = positionsOf r;
            pair =
              k:
              let
                a = po.${k};
                b = pr.${k} or null;
                as = if isList a then a else [ a ];
                bs = if isList b then b else [ b ];
              in
              isList a == isList b
              && length as == length bs
              && prelude.all (i: one (elemAt as i) (elemAt bs i)) (builtins.genList (i: i) (length as));
            # a position that declares positions of its own is walked in step; one that declares none
            # is a sibling (a leaf, a module set read as a whole)
            one =
              a: b:
              if isAttrs a && (a ? carries || isNesting a || positionsOf a != { }) then
                go (fuel - 1) a b
              else
                sibling a b;
          in
          isAttrs r && r ? merge && prelude.all pair (attrNames po);
      r = rebuiltOver refusal t (e: e);
    in
    # not under `tryEval`: a throw from the container's own closure keeps its own words, and the
    # walk's own refusals (exhaustion, the marker's import) are the import refusal already
    go importedTypeWalkFuel t r;

  # ── AN UNRECOGNISED CONTAINER THREADS THROUGH ITS OWN REBUILD (den-hoag-f8mgj, owner-ruled arm (T)) ─
  # A foreign container outside the six, declaring a gen nesting element, is rebuilt by its own
  # `substSubModules`, handed a module list that carries a marker (`threadMarker`). Every stock
  # container's rebuild calls its element's `substSubModules`, and a gen element answers the marker
  # with itself (`exportType`); the marker's function returns that
  # element with its `merge` replaced, so the container keeps its own merge and check (`coercedTo`
  # keeps its `coerceFunc`). Two rebuilds:
  #   capture  — the element's merge RECORDS each site (loc, defs), so the container's own merge is
  #              the split: the key walk reads which element positions exist and what defs each gets.
  #   threaded — the element's merge is the engine's threaded twin at position ++ (eloc - loc).
  # With no accessor (called) it refuses as the import refusal does. A rebuild that does not THREAD
  # (`threadsAt`: every declared position that may nest comes back marked, every other declared
  # position is a sibling with no module set to lose) is refused by name, as F2 α requires: a
  # container that drops its argument would otherwise reach the nested tree through the bridge, a
  # silent standalone evaluation. A foreign ROOT stating a module set is mounted as nixpkgs mounts
  # it instead, where that rebuild declares no gen element (`homedRootAt`).
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
  # above, and the second has no predicate here. Inside it sits a position the declarations do not
  # show whose merge STORES the handed list (`deferredModule`): its value carries the marker item,
  # silent on inspection, and refuses by name where the list is evaluated (the marker's import).
  threadedForeign =
    door: loc0: t:
    threadedForeignWith (threadsAt door loc0 t) door loc0 t;
  threadedForeignWith =
    threads: door: loc0: t:
    let
      refusal = nestingImportRefusal door loc0 t;
      via = f: if threads then rebuiltOver refusal t f else throw refusal;
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
        # on a stated-step chain, a key whose every definition was discharged away holds the
        # element's empty value (nixpkgs' lazy `attrsWith`), marked so the split and the threaded
        # fold read it as a key with no element folded under it
        // (if lvT != null then { emptyValue.value.__genTEmpty = true; } else { })
      );
      # ── A CHAIN KEYED BY ITS STATED STEPS (den-hoag-fozin, den-hoag-rlskz; ADR-0039's serve half,
      # ADR-0025 item 1) ─
      # A LEVEL is a chain of step-free wrappers (`unique`, `coercedTo`, `nullOr`: each folds its
      # element at its own loc, as gen's `nullOr` states with `forward = null`), then ONE
      # `attrsWith` step (any placeholder, lazy or strict). Below it sits either
      #   · on a LAZY step, step-free wrappers, then a gen element that may nest (`one`,
      #     den-hoag-fozin): the functors state every capture site sits one key below the fold's
      #     result, so the split keys the result's attribute names, which forces no element, and
      #     reads a site only when its element is read;
      #   · on either step, any other record that may nest (`node`, den-hoag-rlskz, den-hoag-i01nx):
      #     the functors state each key holds that record's fold, so each key is a CONTAINER NODE
      #     whose own walk is the record's level, read off the fold's result at that key only, and
      #     whose value is this chain's fold read at that key. A key's siblings are never forced to
      #     key it, as nixpkgs forces an element only where it is read: a strict step's key set
      #     forces each key's definitions, as nixpkgs' does, and never a key's own tree. The node
      #     keys its elements in the regime of the record whose step it splits by (`keysExactly`),
      #     as that record keys them in gen's own walk.
      # A strict step over a gen element is not a level: the eager walk reads each key's capture
      # site, which forces what nixpkgs' strict merge forces and no more, and the run stays the
      # authority there. Off a level (`null`) the eager `sitesOf` walk stays.
      #
      # ★ THE STATED SHORTFALL (ADR-0025 item 1, enumerated; den-hoag-i01nx): a `listOf` step under
      # a step-free wrapper is not a level (its keys are positions whose names its functor does not
      # state), so a record that may nest below it is walked eagerly, and aborts uncatchably where
      # nixpkgs serves with an element whose own tree reads the read tree: `uniq (listOf
      # (lazyAttrsOf e))` with a key below the list `mkIf` on the read tree, or `uniq (listOf
      # (attrsOf e))` with a second element's key `mkIf` on it.
      #
      # ★ THE STATED PRICE, an extension of den-hoag-n6dh7's (owner-accepted 2026-09-25: a stock
      # container whose `merge` was overridden cannot be told from the stock one, since Nix cannot
      # compare functions): the steps are TRUSTED from the functor names, at each level. The
      # run stays the authority over which tree sits at which key: a capture site must sit at its
      # own key (`siteLocAt`, and below a node, under the node's key), in the split and in the fold.
      # So a chain whose stock-named `attrsWith` step, lazy or strict, has a merge that does not fold
      # each element at `loc ++ [ k ]` (one key deeper, keys renamed or swapped, or a key holding no
      # element's tree) is refused by name at the key read (`statedStepRefusal`, and
      # `nodeStepRefusal` where the key holds a node, raised where an element below the key is
      # read, at the key), where nixpkgs serves it, and where base served it at a strict step,
      # below a `nullOr`, or at a step reached through either
      # (den-hoag-i01nx; measured: 14 overrides on the strict or `nullOr` step itself and 5 to 8 on
      # the step below it, each a catchable refusal, none a silent value); one that only drops a
      # key's tree serves nixpkgs' value, one that duplicates it does too except below a node whose
      # own record is a level, where it is refused, and one whose result is not an attrset keeps the
      # eager walk (below the option's own strict step, keyed over definitions, it is refused by
      # name). The
      # same trust reaches a node's REGIME: a node keys its elements exactly where its stated
      # record's NAME says it does (`keysExactly`), so a stock-named `attrsOf`, `listOf` or `nullOr`
      # whose merge was overridden to a lazy one is keyed exactly, as its name states.
      levelOf =
        c:
        let
          go =
            fuel: e:
            let
              st = forwardStep e;
              n = (e.functor or { }).name or null;
            in
            if fuel == 0 || st == null || e ? substructure then
              null
            else if n == "unique" || n == "coercedTo" || n == "nullOr" then
              go (fuel - 1) st.element
            else if n == "attrsWith" then
              (
                let
                  el = below (fuel - 1) st.element;
                in
                if el != null then
                  (
                    if e.functor.payload.lazy or false then
                      {
                        one = el;
                        step = e;
                      }
                    else
                      null
                  )
                else if isAttrs st.element && !(st.element ? substructure) && canNest st.element then
                  {
                    node = st.element;
                    step = e;
                  }
                else
                  null
              )
            else
              null;
          # below the step: step-free wrappers down to the gen element, whose capture site the
          # wrappers' merges return unchanged at the step's key (not `nullOr`, whose merge returns
          # `null` in place of the site where every definition is `null`)
          below =
            fuel: e:
            let
              st = forwardStep e;
              n = (e.functor or { }).name or null;
            in
            if fuel == 0 || !(isAttrs e) then
              null
            else if e ? substructure then
              (if canNest e then e else null)
            else if st != null && (n == "unique" || n == "coercedTo") then
              below (fuel - 1) st.element
            else
              null;
        in
        go importedTypeWalkFuel c;
      # a record's levels, decided once per record: a `node` level carries the level of the record
      # its step states (`next`), so no key re-walks it; a level carries its `step`, the record
      # whose split it is. A key whose value nixpkgs forces only where it is read, a strict
      # step's key as much as a lazy one's, is a node: keying below it needs its value, and only
      # its own group may force that.
      levels =
        c:
        let
          lv = levelOf c;
        in
        if lv != null && lv ? node then
          (
            let
              next = levels lv.node;
            in
            # scout D2: every level may be an `over` level, not only the option's own; a node level
            # with an `over` level anywhere below it keys each key's definitions (`keyed`), so the
            # `over` split is handed the definitions at its own key
            overAt (
              lv
              // {
                inherit next;
                keyed = next != null && (next ? over || next.keyed or false);
              }
            )
          )
        else
          lv;
      lvT = levels t;
      # ── THE OPTION'S OWN STRICT STEP OVER A STOCK LAZY STEP (den-hoag-i01nx v1, arm OV) ─
      # A strict step at the option's own level whose element is a stock container gen re-homes,
      # directly over the gen element (`lazyAttrsOf e`), is keyed as gen keys `attrsOf (lazyAttrsOf
      # e)`: its keys by gen's own `attrsOf` split over the option's definitions (definedness, as
      # nixpkgs' strict merge forces), and each key's lower keys over that key's definitions where it
      # is walked (`keyedOverAt`, mda6f), never over its merged value, which nixpkgs forces only where
      # the key is read. Below a node the definitions at a key are not in hand, so the step stays a
      # node there.
      overAt =
        lv:
        let
          # scout D1: `unique` wrappers over the lazy step are looked through: each adds no step and
          # folds its element over the same definitions, and keying from definitions runs neither
          # merge, so its refusal stays where the key is read
          strip =
            fuel: x:
            if
              fuel > 0 && isAttrs x && !(x ? substructure) && ((x.functor or { }).name or null) == "unique"
            then
              strip (fuel - 1) ((forwardStep x).element or null)
            else
              x;
          inner = strip importedTypeWalkFuel lv.node;
          e = (forwardStep inner).element or null;
          rehomed = importedRehomeAt door loc0 inner;
        in
        if
          lv != null
          && lv ? node
          && !(lv.step.functor.payload.lazy or false)
          && lv.next != null
          && lv.next ? one
          && isAttrs e
          && e ? substructure
          && rehomed != null
        then
          {
            over = (constructors.attrsOf (homedAt door loc0 inner)).split;
            inherit (lv) step next;
          }
        else
          lv;
      chainElement = lvT.one or null;
      # `l` below `base`: the steps past it, `null` where `l` does not extend it
      under =
        base: l:
        if
          isList l && length l >= length base && builtins.genList (i: elemAt l i) (length base) == base
        then
          builtins.genList (i: elemAt l (length base + i)) (length l - length base)
        else
          null;
      # the loc of the capture site a fold result holds at key `k`, `null` where it holds none;
      # whether it holds the empty value of a key with no element folded (`capture`)
      emptyAt = r: k: (r.${k} or null) ? __genTEmpty;
      siteLocAt =
        r: k:
        let
          v = r.${k} or null;
        in
        if isAttrs v && v ? __genTSite then v.__genTSite.loc else null;
      lazySplit =
        el: loc: r:
        map (k: {
          step = [ k ];
          loc = loc ++ [ k ];
          defs =
            let
              v = r.${k};
            in
            if v ? __genTEmpty then
              [ ]
            else if isAttrs v && v ? __genTSite && v.__genTSite.loc == loc ++ [ k ] then
              v.__genTSite.defs
            else
              throw (statedStepRefusal door (loc ++ [ k ]) t);
          # the level's own gen element, stated by the declaration: reading the site's would force
          # the element's merge, which discharges its definitions
          type = el;
        }) (attrNames r);
      # The split of the level `lv` at `base`, over `r`, the capture fold's result read there. `ds`:
      # the definitions the walk handed the split, which a node keys over (its fold is this chain's
      # over them, read at its key). `stated`: below the option's own level, the record the level
      # above states at `base` (a node's), where the merge chose the key a site sits under, so a
      # site's loc is checked to extend `base`; `null` at the option's own level.
      splitAt =
        lv: stated: oloc: root: base: ds: r:
        if lv != null && lv ? one && isAttrs r then
          lazySplit lv.one base r
        # scout N1: an `over` level keys over its definitions alone, so its split never forces the
        # capture fold; the threaded fold's own capture stays the authority where a key is read
        else if lv != null && lv ? over then
          lv.over base ds
        else if lv != null && lv ? node && isAttrs r then
          let
            node = nodeAt lv.node lv.next oloc root;
          in
          # scout D2: a level with an `over` level below it (`keyed`, decided once per record) hands
          # each key's node the definitions at that key, split by the step's own name (an
          # `attrsWith` step keys its definitions by attribute, as gen's `lazyAttrsOf` does), read
          # only where the key's node is walked; any other node level is handed `ds`, as before
          if lv.keyed or false then
            let
              byKey = builtins.listToAttrs (
                map (e: {
                  name = head e.step;
                  value = e.defs;
                }) ((constructors.lazyAttrsOf lv.node).split base ds)
              );
            in
            map (k: {
              step = [ k ];
              loc = base ++ [ k ];
              defs = byKey.${k} or [ ];
              type = node;
            }) (attrNames r)
          else
            map (k: {
              step = [ k ];
              loc = base ++ [ k ];
              defs = ds;
              type = node;
            }) (attrNames r)
        else
          map (
            s:
            let
              st = under base s.loc;
            in
            {
              step =
                if stated == null then
                  stepOf base s.loc
                else if st != null then
                  st
                else
                  throw (nodeStepRefusal door base t stated);
              inherit (s) loc defs type;
            }
          ) (sitesOf r);
      # The node at `base` (a key of a `node` level), holding `c`, the record the level's step
      # states there; `rB` is the capture fold's result read at `base`. Its walk is `c`'s level
      # over `rB`; its value is this chain's threaded fold over the option's definitions, read at
      # `base`, with every element below `base` threaded under the node's own accessor.
      nodeAt =
        c: lv: oloc: root:
        t
        // {
          __threadedForeign = true;
          # the node keys its elements as the record whose split it runs does (`keysExactly`): the
          # step of `c`'s own level, below its step-free wrappers, else `c`; an exact stock
          # container's elements are keyed in the exact regime, as gen's own are
          keysExactly = keysExactly (if lv != null then lv.step else c);
          split =
            base: ds: splitAt lv c oloc root base ds (builtins.foldl' (v: k: v.${k}) root (under oloc base));
          mergeDefs = {
            __functor =
              _: loc: _defs:
              throw (nestingImportRefusal door loc t);
            threaded =
              _ev: loc: _defs:
              throw (nestingImportRefusal door loc t);
          };
        };
      # The fold's result at a level, read where it is read: a `node` level's keys are read off
      # their nodes; a `one` level's keys are checked against their own capture sites
      # (`keyedWhereRead`); otherwise as folded.
      finishAt =
        lv: base: rB: ev: v:
        if lv != null && (lv ? node || lv ? over) && isAttrs rB && isAttrs v then
          prelude.mapAttrs (
            k: x:
            if lv.next != null then
              finishAt lv.next (base ++ [ k ]) (rB.${k} or null) ev x
            else
              heldAt lv base rB k (rB.${k} or null) x
          ) v
        else if lv != null && lv ? one && isAttrs rB then
          keyedWhereRead base rB v
        else
          v;
      # The value read at key `k` of a `node` level whose record is not itself a level, checked where
      # each element is read (`keyedWhereRead`'s rule, one record further down): walked beside `r`,
      # the capture fold's result at `k`, an element's tree is served where its site was folded
      # under `k`, or under a key `m` that holds its own tree (every site of `m`'s sits under `m`);
      # otherwise the read refuses at `k`. A read that reaches no element reads no site, so it
      # forces what nixpkgs forces for it.
      heldAt =
        lv: base: rB: k: r: x:
        if isAttrs r then
          if r ? __genTSite then
            let
              l = r.__genTSite.loc;
              n = length base;
              m = if length l > n && builtins.genList (elemAt l) n == base then elemAt l n else null;
            in
            if
              m == k || (m != null && rB ? ${m} && all (s: under (base ++ [ m ]) s.loc != null) (sitesOf rB.${m}))
            then
              x
            else
              throw (nodeStepRefusal door (base ++ [ k ]) t lv.node)
          else if isAttrs x && !(r ? __genTEmpty) then
            prelude.mapAttrs (j: heldAt lv base rB k (r.${j} or null)) x
          else
            x
        else if isList r && isList x && length r == length x then
          builtins.genList (i: heldAt lv base rB k (elemAt r i) (elemAt x i)) (length x)
        else
          x;
      # The threaded fold's result, read at key `k`, holds the tree folded at the site found there,
      # and that site must be its own key's (`loc ++ [ k' ]`, held at `k'`), or the empty value of a
      # key with none; a merge that duplicates or drops a key's tree passes, one that moves it
      # refuses here, where it is read.
      keyedWhereRead =
        loc: captured: v:
        if isAttrs v then
          prelude.mapAttrs (
            k: x:
            let
              l = siteLocAt captured k;
            in
            if
              emptyAt captured k
              ||
                l != null
                && length l == length loc + 1
                && l == loc ++ [ (prelude.last l) ]
                && siteLocAt captured (prelude.last l) == l
            then
              x
            else
              throw (statedStepRefusal door (loc ++ [ k ]) t)
          ) v
        else
          v;
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
      # (`coercedTo`, `attrsWith`) folds by `merge.v2` and never reads the record's `check`. A check
      # that reaches the nested tree (`unique`'s is its element's, `coercedTo`'s calls
      # `finalType.check`) reads the tree's `check`, its module-value domain, which reads only the
      # value (den-hoag-f8mgj arm Q). The verdict names the container, never its `description`,
      # which reads the element's and so the tree's refusing one.
      nt = t.nestedTypes or { };
      checkedThreaded = checkedFold {
        inherit (t) check;
        description = nameOf t;
      };
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
        if e ? _checkWitness && rewritten != [ ] then checkedFold (head rewritten) fold else fold;
      # The chain's threaded fold over the option's `loc` and `defs`, each element threaded under
      # `ev` at its steps below `base`, where `lv` (the level at `base`, `rB` the capture fold's
      # result there) placed it; any other element's nested-tree read refuses by name.
      threadedAt =
        lv: checked: base: rB: ev: loc: defs:
        let
          # One record per level, built once per fold and lazily per key (a `node` level's `sub`), so
          # an element's placement reads its level's `steps` rather than re-deriving them.
          infoAt = lv: checked: base: rB: rec {
            inherit
              lv
              checked
              base
              rB
              ;
            onLevel = lv != null && isAttrs rB;
            steps = map (s: stepOf base s.loc) (sitesOf rB);
            sub =
              if onLevel && lv ? node then prelude.mapAttrs (k: infoAt lv.next true (base ++ [ k ])) rB else { };
          };
          info0 = infoAt lv checked base rB;
          # Where element `eloc` is threaded: `{ ev; st; ok; }`, the accessor of the level that holds
          # it (a `node` level hands it to its key's node, `accessor`), its steps below that level,
          # and whether that level's split placed it there.
          placeAt =
            i: ev: st: eloc:
            if st == null then
              {
                inherit ev st;
                ok = false;
                lvOn = i.onLevel;
              }
            else if i.onLevel && i.lv ? over && st != [ ] then
              # an element below the option's strict step, placed off the site under its key alone
              let
                rK = i.rB.${head st} or null;
              in
              {
                inherit ev st;
                lvOn = if i.rB ? ${head st} then isAttrs rK else i.onLevel;
                ok = length st == 2 && isAttrs rK && siteLocAt rK (elemAt st 1) == eloc;
              }
            else if i.onLevel && i.lv ? node && st != [ ] && i.sub ? ${head st} then
              placeAt i.sub.${head st} (ev.child { position = ev.position ++ [ (head st) ]; }).accessor
                (builtins.tail st)
                eloc
            else
              {
                inherit ev;
                inherit st;
                lvOn = i.onLevel;
                ok =
                  if i.onLevel && i.lv ? one then
                    length st == 1 && siteLocAt i.rB (head st) == eloc
                  else if i.onLevel && i.lv ? node then
                    false
                  else
                    builtins.elem st i.steps;
              };
          onLevel = info0.onLevel;
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
                let
                  at = placeAt info0 ev (if checked then under base eloc else stepOf base eloc) eloc;
                  ok = at.ok;
                in
                mergeDefsThreaded (
                  at.ev
                  // {
                    position = at.ev.position ++ (if at.st == null then [ ] else at.st);
                    # The threaded fold never sets the exact-element mark (`unionNodeAt` reads it):
                    # an element it folds is keyed over-approximately. A node's own walk keys its
                    # elements in its stated record's regime (`keysExactly`), which this mark does
                    # not govern.
                    exactAt = null;
                  }
                  // (
                    if ok then
                      { }
                    else
                      {
                        # What the walk minted here (`minted`, the key walk's own records) is
                        # still the accessor's to state; only a read refuses.
                        child =
                          site:
                          if site ? __genMergeMinted then
                            at.ev.child site
                          else
                            throw ((if at.lvOn then statedStepRefusal else unexposedRefusal) door eloc t);
                      }
                  )
                ) eloc e edefs
              );
            }
          )
        )) loc defs;
    in
    t
    // {
      __threadedForeign = true;
      # the walk keys the split's elements in the regime of the step that holds them
      keysExactly = if lvT != null then keysExactly lvT.step else keysExactly t;
      split =
        loc: defs:
        # on a level, and only where the merge returned the attrset its functors state; any other
        # result keeps the eager walk, whose sites are found wherever the merge put them
        let
          captured = (importedFold capture) loc defs;
        in
        splitAt lvT null loc captured loc defs captured;
      mergeDefs = {
        __functor =
          _: loc: _defs:
          throw (nestingImportRefusal door loc t);
        threaded =
          ev: loc: defs:
          let
            captured = (importedFold capture) loc defs;
          in
          finishAt lvT loc captured ev (threadedAt lvT false loc captured ev loc defs);
      };
    };

  # Whether a record states an element or members AT ALL, in any carrying spelling (`carries`, a
  # non-empty `nestedTypes`, a top-level `elemType`), or OFFERS one to merge on in its functor
  # payload's `elemType` (read only so the walk can judge the offer, `payloadOffered`). Presence only, read before
  # any walk: a record doing neither can be neither re-homed nor refused, and most records crossing a
  # door do neither, so this is what keeps the nested-tree crossing's price off every leaf and every
  # `mkOptionType` descriptor.
  statesWrapped =
    t:
    t ? carries
    || (!(evaluatesOwnRoles t) && { } != (t.nestedTypes or { }))
    || t ? elemType
    || ((t.functor or { }).payload or null) ? elemType;

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

  # The node-level form of the stated-step refusal (den-hoag-rlskz, den-hoag-i01nx): a chain whose
  # step, lazy or strict, states that each key holds the record `c` folded at that key, whose merge
  # folded at the key read, `at`, a tree that sits under another key.
  nodeStepRefusal =
    door: at: t: c:
    "${doorAt door at}the option type `${nameOf t}' states (its functors) that each key below it, "
    + "under an `attrsWith', holds a `${nameOf c}' folded at that key, and its merge folded a tree "
    + "of another key's there: the merge was overridden, so the functor misstates it, and this tree "
    + "cannot be keyed where it is read. Declare the element under a container whose merge is its "
    + "constructor's, or state `declaresNesting = false' on the type and take the stated price: a "
    + "nested tree it forwards to is then evaluated standalone";

  # The stated-step refusal's text (den-hoag-fozin): a chain keyed by the step its functors state,
  # whose merge folded no element of its own at the key read, `at`.
  statedStepRefusal =
    door: at: t:
    "${doorAt door at}the option type `${nameOf t}' states (its functors) that its gen element sits "
    + "one key below it, under a lazy `attrsWith', and its merge did not fold that key's own element "
    + "there: the merge was overridden, so the functor misstates it, and this tree cannot be keyed "
    + "where it is read. Declare the element under a container whose merge is its constructor's, or "
    + "state `declaresNesting = false' on the type and take the stated price: a nested tree it "
    + "forwards to is then evaluated standalone";

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
    containerNodes = false;
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
  # ★ A REDECLARATION IS THE MEET (den-hoag-l1j4q, owner-ruled 2026-10-06). Read as a join, `port ∥
  # int → int` is an upper bound; read as the meet, which is the ruled reading, it drops `port`'s
  # check. A join this witness takes is met at the step (`lib/modules.nix` `mergeTypesBy`, through
  # `metWith`), and a relation's `meets` answer at `declaredPair` is met by the same function. A join
  # that renames past an operand is still refused here: the meet's carrier is the join, and a join that
  # is not the operand's constructor is not met by this boundary, so the refusal stands, sound under
  # the meet (it serves nothing an operand rejects). The witness compares the relation's ANSWER with
  # each operand's own name, never one operand with the other, so it keys no identity (ADR-0034 is
  # scoped to IDENTITY).
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
      # ★ A WITNESSED REWRITE IS READ AS ITS CARRIER. The meet owes every operand whose `check` is not its
      # witness (`metWith`), so a rewrite's own check is enforced at the step whatever join is taken here;
      # what this asks is only whether the join keeps the name the CARRIER states. A met record's carrier
      # is its join (`meetOf`'s `__meetJoin`) while it is still the record `meetOf` built, whose witness
      # is its join's: a re-completion (`mkOptionType`, `defineType`) re-ties the witness to the met
      # check and carries `__meetJoin` across, and the meet then owes it nothing, so read as its join it
      # would lose that check. Whether the witness is the join's is decided by `==`, so over a foreign
      # join whose `check` is a bare function (nixpkgs `enum`, `int`, `str`) Nix and Determinate decide
      # false and the record reads as itself, while Lix compares a function with itself by pointer and
      # reads it as its join; over a functor-record `check` (nixpkgs `listOf`, `attrsOf`, `nullOr`) all
      # three read it as its join. Either reading is sound: a record read as its join has that join's
      # witness, so its own check is the join's or is owed by the meet. A `//` copy whose only
      # departure from its completion is `check` and name-carried fields (nixpkgs `addCheck`) has its
      # completion; any other record is its own.
      # Restated inline at the entry of `default.nix`'s parametric relation, for the load gates' cost;
      # the two spellings are held alike by `check-family-merge`'s carrier cell.
      bare =
        x:
        if
          x ? __meetJoin
          && x ? _checkWitness
          && x._checkWitness == (x.__meetJoin._checkWitness or x.__meetJoin.check)
        then
          bare x.__meetJoin
        else if
          builtins.isFunction (x.__typeSelf or null) && (rewritesCheck x || departsWithinCarrier x)
        then
          let
            c = x.__typeSelf null;
            names = carrierTolerated;
          in
          if
            stampOk (
              builtins.removeAttrs x names
              // builtins.intersectAttrs (builtins.listToAttrs (
                map (n: {
                  name = n;
                  value = null;
                }) names
              )) c
            )
          then
            c
          else
            x
        else
          x;
      # one name, or two the embedding table states are one record's (`joinsAs`). The row is the one
      # the RECORD reaches (`embedsOf`), never one its name collides with: a caller's `enum "string"`
      # read as `str` would let a join that dropped its check pass as keeping it.
      asOf =
        src:
        let
          x = if isAttrs src then bare src else src;
          e = embedsOf x;
        in
        if e != null && e ? joinsAs then
          e.joinsAs
        # a record the export completed under a row stating `joinsAs` (an instance row, `embeddings.enum`,
        # has no mint to reach it by) publishes that name as its functor's: read only off a completed
        # gen record, whose functor is its export's, never a `//` copy's
        else if
          x ? typeMergeRel
          && builtins.isString ((x.functor or { }).name or null)
          && builtins.any (r: (r.joinsAs or null) == x.functor.name) (builtins.attrValues embeddings)
          && builtins.isFunction (x.__typeSelf or null)
          && stampOk x
        then
          x.functor.name
        else
          x.name or null;
      sameUpToEmbedding = a: b: (a.name or null) == (b.name or null) || asOf a == asOf b;
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
        else if !(sameUpToEmbedding j o) then
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
  # — and `f.type` is the partner's own constructor, so reconstructing the partner from its own
  # functor is well-typed whatever shape that payload has, foreign or ours. The protocol's spelling
  # makes `f.type` a function of the payload; nixpkgs' `either`/`oneOf` instead leave it the
  # constructor curried over the member pair, so an ALTERNATIVES payload is applied positionally
  # (`rebuiltFromPayload`). The row is consumed here and a TYPE is what leaves.
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
        (if payloadRole payload == "alternatives" then rebuiltFromPayload f payload else f.type payload)
      else
        null;

  # `f.type` APPLIED TO AN ALTERNATIVES PAYLOAD (the caller tests the role, so no other payload pays
  # for this), with the one foreign spelling where that is not the protocol: nixpkgs' `either` states
  # its relation in an overridden `typeMerge` and leaves `functor.type` as the constructor itself,
  # curried over the member pair, so `f.type payload` is a FUNCTION awaiting a second member. An
  # application that answers a function is therefore applied positionally, the way
  # `roleSpelling.alternatives` already reads that payload. Keyed on the role and the application's
  # result, never on a constructor name.
  rebuiltFromPayload =
    f: payload:
    let
      applied = f.type payload;
    in
    if isFunction applied && length payload.elemType == 2 then
      f.type (head payload.elemType) (elemAt payload.elemType 1)
    else
      applied;

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
  # exactly the shape this boundary exists to convert into a value the algebra can act on.
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

  # THE JOIN IN THE PARTNER'S OWN RELATION, for a gen nesting type facing a same-named foreign partner
  # whose module set is stated BESIDE parameters gen's relation does not carry (nixpkgs
  # `submoduleWith`'s `specialArgs`, `shorthandOnlyDefinesConfig`, `description`, `class`). gen's
  # parameters embed into that richer payload (`moduleSetPayload`, the payload `exportType` already
  # publishes), so the pair has a join there and only there, in the partner's parameter space.
  #
  # The join is the protocol's DEFAULT relation over the partner's PUBLISHED functor (`protoTypeMerge`,
  # nixpkgs' `defaultTypeMerge`), NOT the partner's own `typeMerge`: the default relation over its
  # functor is what nixpkgs' twin of this type applies when the twin decides. So for a partner whose
  # `functor.binOp`/`functor.type` are `submoduleWith`'s, the answer equals nixpkgs' in both orders.
  # A partner stating a `typeMerge` of its own is order-dependent here exactly as it is beside
  # nixpkgs' twin (the twin ignores it too), and a partner whose `functor.binOp` disagrees with its
  # own `typeMerge` gets that functor's relation in the order where this side decides.
  # `self` is `{ name; payload; }`, this type's functor name and payload; `null` where the partner
  # states no applicable relation.
  joinInStatedRelation =
    self: other:
    let
      pf = other.functor or null;
    in
    if !(statesRelation other) || !(isFunction (pf.type or null)) then
      null
    else
      protoTypeMerge (pf // { inherit (self) name payload; }) pf;

  # THE SAME JOIN FOR A CONTAINER, whose parameter is ONE carried role (`element`), against a RAW foreign
  # partner (one that carries no gen role). Taken only where the partner's join keeps each operand's
  # stated name (`joinRenames`), as `importedMerge` takes a foreign join; `null` otherwise, and the
  # caller's own relation then answers as it did before. A partner whose payload names more than the
  # role's own key (`importedOffered` null) is not read whole, so it is not joined here either —
  # UNLESS it is stated under the richer constructor the caller's row `embedding` names (`embeddings`): there gen's
  # parameters are a point of the partner's payload (`embeddedPayload`), so the pair is joined in the
  # partner's relation over that embedding, under the same witness. A role-less type (`role` null,
  # `deferredModule`) is joined only that way, and a gen partner of it too: gen publishes the same
  # embedding, so there is no gen-versus-foreign test.
  joinCarriedInStatedRelation =
    {
      name,
      embedding,
      role,
      carried,
      self,
    }:
    other:
    let
      e = embedding;
      joined =
        if other ? carries then
          null
        else if role != null && importedOffered role other != null then
          joinInStatedRelation {
            inherit name;
            payload = {
              ${roleSpelling.${role}.payloadKey} = carried;
            };
          } other
        else if e != null && ((other.functor or { }).name or null) == e.name then
          joinInStatedRelation {
            inherit (e) name;
            payload = embeddedPayload e role carried;
          } other
        else
          null;
    in
    # A row's LIST parameter (an `enum`'s members) is this type's own content, so a join that does not
    # keep every element of it drops this type's check, whatever names it keeps (den-hoag-n8cpq item 2).
    if
      joined == null
      || joinRenames joined self
      || joinRenames joined other
      || !(builtins.all (
        k:
        let
          v = e.params.${k};
          jv = ((joined.functor or { }).payload or { }).${k} or null;
        in
        !(isList v) || (isList jv && builtins.all (m: builtins.elem m jv) v)
      ) (attrNames (if e == null then { } else e.params or { })))
    then
      null
    else
      joined;

  # THE JOIN FOR A UNION, against a RAW foreign partner whose relation is NOT in its functor: nixpkgs'
  # `either` overrides `typeMerge` and publishes a `binOp` its own payload (a member LIST) cannot be
  # applied to, so the protocol's default over that functor (`joinInStatedRelation`) is not the
  # relation its constructor states. The partner is REBUILT from its published functor
  # (`importedPartner`), and the rebuilt record's relation is applied to this type's published
  # functor: the application nixpkgs makes in the order where the partner's constructor decides, so
  # both orders compute one function of one pair — ORDER-INDEPENDENT BY CONSTRUCTION ONLY WHERE THAT
  # RELATION ANSWERS a join the witness keeps; elsewhere the pair falls back to the caller's own
  # relation and keeps that relation's order behaviour (an `ints.u8` member). As with
  # `joinInStatedRelation`, the partner's OWN `typeMerge` is never called: a partner whose `typeMerge`
  # disagrees with its functor gets its functor's constructor. Held to the same witness as every
  # foreign join. A FOREIGN ANSWER THAT ABORTS IS NO ANSWER: the rebuilt relation runs foreign code
  # over gen's members (nixpkgs' `defaultTypeMerge` asserts two payloads agree on null-ness), so it is taken through
  # `tryEval`, the idiom `lib/default.nix` uses, and this relation stays a value or a named refusal
  # (ADR-0025 item 1).
  joinInRebuiltPartner =
    { role, self }:
    other:
    let
      partner =
        if other ? carries || importedOffered role other == null then
          null
        else
          importedPartner (other.functor or null);
      asked =
        if !(isAttrs partner) || !(partner ? typeMerge) then null else partner.typeMerge self.functor;
      tried = builtins.tryEval asked;
      joined = if tried.success then tried.value else null;
    in
    if joined == null || joinRenames joined self || joinRenames joined other then null else joined;

  # THE SAME JOIN FOR A LEAF, against a RAW foreign partner that is a leaf too (nullary: no payload). The
  # protocol's default relation over the partner's PUBLISHED functor answers `f.type`, the deciding
  # side's own record; here the partner is the decider's twin, so the answer is the record the partner's
  # functor names, which is what nixpkgs' twin answers in the order where it decides. Taken only where
  # the join keeps each operand's stated name (`joinRenames`), as `joinCarriedInStatedRelation` does;
  # `null` otherwise, and the caller's own relation then answers. A type whose embedding states no
  # parameters (`string`) is joined at the embedding's name. A partner stating a payload (nixpkgs
  # `pathWith`) is not a nullary leaf and is not joined here (a leaf whose embedding states parameters
  # is joined in `joinCarriedInStatedRelation`), and neither is one whose functor names no `type` (the
  # protocol's default would abort reading it): gen's own relation answers.
  joinLeafInStatedRelation =
    {
      name,
      embedding,
      self,
    }:
    other:
    let
      e = embedding;
      stated = if e != null && !(e ? params) then e.name else name;
      pf = other.functor or null;
      joined =
        if !(statesRelation other) || !(pf ? type) || statesPayload other then
          null
        else
          protoTypeMerge (pf // { name = stated; }) pf;
    in
    if !(isAttrs joined) || joinRenames joined self || joinRenames joined other then null else joined;

  # The module-set payload a gen nesting type offers a foreign engine, as ONE binding read by
  # `exportType` and by `joinInStatedRelation`'s callers.
  moduleSetPayload =
    {
      modules,
      specialArgs,
      shorthandOnlyDefinesConfig,
    }:
    {
      inherit modules specialArgs shorthandOnlyDefinesConfig;
      description = null;
      class = null;
    };

  # The caller's stated relation, however they stated it: their derived accessor where they had one,
  # the protocol's own default over their `functor' where they did not.
  callerTypeMerge = t: t.typeMerge or (protoTypeMerge t.functor);

  # ★★ THE PREDICATE IS THE RELATION THE CALLER STATED, NEVER THE ACCESSOR DERIVED FROM IT. Keying on
  # `typeMerge' asks "did some other library's `mkOptionType' build this record", which is a fact
  # about the descriptor's provenance and not about what its author said. Keying on `functor.binOp'
  # asks the question this boundary is actually deciding.
  statesRelation = t: ((t.functor or { }).binOp or null) != null;
  # Whether a container's split keys EXACTLY, so the key walk keys its elements in the exact regime
  # (`modules.nix` `keyWalk`'s `under = null`): an `attrsOf`, `listOf` or `nullOr`, whose key sets
  # already read each element's definitions to WHNF, by name; a record that states it answers itself
  # (a foreign chain's node, `threadedForeignWith` `nodeAt`, answers for the record its step states).
  # The name is trusted, as `threadedForeignWith`'s stated price says: a stock-named container whose
  # merge was overridden to a lazy one is keyed exactly. `modules.nix` `keyWalk` reads this predicate
  # inline, and `ci/tests/nesting-keys.nix` (`nesting-keys-keys-exactly-census`) holds the two equal.
  keysExactly =
    t:
    t.keysExactly or (
      let
        name = t.name or null;
      in
      name == "attrsOf" || name == "listOf" || name == "nullOr"
    );
  # Whether a record's published functor states a PAYLOAD: a nullary leaf states none, and nixpkgs'
  # default relation asserts that two operands agree on it, so a stated payload beside a leaf has no join
  # in that relation (a partner's OWN relation may still join one). Read by `joinLeafInStatedRelation`,
  # which declines it, and by the leaf relation, which refuses it where it decides (lib/types.nix
  # `nullaryRel`).
  statesPayload = t: ((t.functor or { }).payload or null) != null;

  # ── THE MEET (den-hoag-l1j4q, owner-ruled 2026-10-06) ──────────────────────────────────────────
  # A redeclared option accepts a definition only where EVERY declared check accepts it. `meetOf j os`
  # is the join `j` (the carrier: its fold, name, functor) restricted by each check in `os`, published as
  # a witnessed rewrite (`check` is not `_checkWitness`), so every later step sees it as owed.
  meetOf =
    j: os:
    let
      fold = j.mergeDefs or (importedRawFold j);
      # each check in its cheapest callable form: a witness record's function, not its functor
      direct = c: if isAttrs c && c ? _fn then c._fn else c;
      # an operand's declared domain, as the engine reads one declared alone: its `check` and, for a gen
      # record, its `verify`. Where its `check` is the witness its verify published, `verify` is read
      # alone, as `ov` reads it: that saves one check call per value, and no measured verdict moves
      dom =
        o:
        let
          c = direct o.check;
        in
        if !(o ? verify) then
          c
        else if o ? _checkWitness && o.check == o._checkWitness then
          (v: o.verify v == null)
        else
          (v: c v && o.verify v == null);
      jc = direct j.check;
      # a widened operand's stock check (`metWith`): it is owed only where its own parameters admit
      stockOf = o: if o ? __stockCheck then direct o.__stockCheck else null;
      ocs = map (
        o:
        let
          c = dom o;
          s = stockOf o;
        in
        if s == null then c else (v: c v || !(s v))
      ) os;
      oc = head ocs;
      c0 = dom o1;
      s0 = stockOf o1;
      c1 = dom (elemAt os 1);
      s1 = stockOf (elemAt os 1);
      # a gen operand whose published check is its own domain: its `verify`, read inline
      o1 = head os;
      ov =
        if o1 ? verify && !(o1 ? __stockCheck) && o1 ? _checkWitness && o1.check == o1._checkWitness then
          o1.verify
        else
          null;
      conj =
        if length os == 1 && ov != null then
          (v: jc v && ov v == null)
        else if length os == 1 then
          (v: jc v && oc v)
        else if length os == 2 && s0 == null && s1 == null then
          (v: jc v && c0 v && c1 v)
        else if length os == 2 then
          (v: jc v && (c0 v || s0 != null && !(s0 v)) && (c1 v || s1 != null && !(s1 v)))
        else
          (v: jc v && builtins.all (c: c v) ocs);
      # the owed checks over a definition list's values, by primops around the checks alone
      owedHold =
        vs:
        if length os == 1 && ov != null then
          builtins.all builtins.isNull (map ov vs)
        else if length os == 1 then
          builtins.all oc vs
        else
          builtins.all (v: builtins.all (c: c v) ocs) vs;
      # A join folding under nixpkgs' v2 protocol keeps it: its own merge (which checks the join) is
      # asked once and the owed checks are judged over the same definitions, by primops around the checks.
      # A v1 join keeps its own `merge`, which a foreign engine applies after the conjoined `check`.
      v2 = isV2 j && (j.getSubModules or null) == null;
      met =
        j
        // {
          check =
            if v2 then
              {
                __functor = _: conj;
                isV2MergeCoherent = true;
              }
            else
              conj;
          _checkWitness = j._checkWitness or j.check;
          __meetJoin = j;
          merge =
            if v2 then
              {
                __functor =
                  self: loc: defs:
                  (self.v2 { inherit loc defs; }).value;
                v2 =
                  { loc, defs }:
                  let
                    r = j.merge.v2 { inherit loc defs; };
                  in
                  if r.headError != null || owedHold (builtins.catAttrs "value" defs) then
                    r
                  else
                    r
                    // {
                      headError.message = "a definition is rejected by the check of another declaration of this option";
                    };
              }
            else
              j.merge;
          # asked by a foreign engine, which hands over a FUNCTOR only: the join is met with this record again,
          # through `metWith` like every other step, so a join widening this record's own parameters (enum)
          # owes it relativised. Where every step's relation answers at the top constructor, the fold is then
          # the same in every order; `lib/types.nix`'s `metElem` still meets through `meetOf` directly, which
          # can only over-refuse.
          typeMerge =
            f:
            let
              # a foreign relation's assert is no answer (`joinInRebuiltPartner`'s `tryEval`)
              asked = builtins.tryEval (callerTypeMerge j f);
              r = if asked.success then asked.value else null;
            in
            if r == null then null else metWith r [ met ];
        }
        // (if fold == null then { } else { mergeDefs = fold; });
    in
    met;
  # The answer of every type merge: `m` met with each operand whose check it does not carry.
  #  - A gen relation's answer over a gen operand stating its own check carries it (gen x gen relations
  #    are exact), so only a foreign operand, a witnessed rewrite (a wrapper's check, or a met record), or
  #    a foreign answer can owe one (`mayOwe`, asked before any comparison: a gen x gen step compares
  #    nothing). An operand that IS `m` owes nothing.
  #  - A module set's join is the union of its declarations, itself the meet of what they declare, and its
  #    own check is the module shape: its records are never compared (a comparison would evaluate their
  #    modules). A witnessed rewrite dropped there is refused by the step before this is asked
  #    (`lib/modules.nix` `mergeTypesBy`); a foreign wrapper's check is carried by the declaration
  #    list's fixup (`carriedAtDepth`).
  #  - A FRESH join (neither operand) of the SAME constructors that changes an operand's own PARAMETERS
  #    is those constructors' law over them, as nixpkgs' `enum` unions its values: that operand is owed
  #    RELATIVISED to its own parameters, `v: o.check v || !(stock o).check v`, where `stock o` is its
  #    constructor rebuilt from its functor (`__stockCheck`, read inline by `meetOf`). A wrapper's check
  #    is not in `stock o`, so it stays owed, while the union holds. The parameters are a TREE (den-hoag-
  #    kbiu2): each node's functor payload less the roles it carries, and its elements' trees, so
  #    `nullOr (enum [a])`, `unique`, `either` and `oneOf` over an enum widen as the bare enum does. The
  #    trees must name the same constructors at every node, and a node where they differ must state the
  #    operand's parameters: a nullary node states none, and a join that changes one changes the
  #    operand's check, which is then owed whole. A wrapper BELOW the top is not in `stock o`'s top
  #    node but is met at its own depth, where the join's roles are met (`rolesMet`, lib/modules.nix).
  #    This is sound only because the join's elements are themselves met, so a tree's elements are
  #    exactly the roles `rolesMet` meets, as `carriedAt` reads them (an element type, or a PAIR of
  #    alternatives): a member the meet does not meet is never released by the tree.
  #  - One value declared twice owes its check once.
  # Every binding is local, so the library's load pays for this one lambda alone.
  metWith =
    m: os:
    if
      m ? typeMergeRel
      && builtins.all (o: o ? typeMergeRel && !(rewritesCheck o) && !(replacesVerify o)) os
    then
      m
    else
      let
        mayOwe =
          o:
          !(o ? typeMergeRel)
          || !(m ? typeMergeRel)
          || (o ? _checkWitness && o ? check && o.check != o._checkWitness)
          || replacesVerify o;
        same = x: y: closuresFirst [ x ] x == closuresFirst [ y ] y;
        # the roles the meet meets, read as `carriedAt` reads a payload: an element type, or a pair of
        # alternatives; any other `elemType` states no element of the tree
        elementsOf =
          p:
          if isAttrs p && p ? elemType then
            (
              if isList p.elemType then
                (if length p.elemType == 2 then p.elemType else [ ])
              else if isAttrs p.elemType then
                [ p.elemType ]
              else
                [ ]
            )
          else
            [ ];
        # the parameter TREE: each constructor's name and payload less its roles, and its elements' trees
        # (an element's parameters are its container's: `nullOr (enum [a])` is parameterised by `[a]`).
        # Past the walk's fuel a tree states nothing more, so a change that deep is owed whole.
        shapeOf =
          fuel: t:
          let
            f = t.functor or { };
            p = f.payload or null;
          in
          {
            n = f.name or null;
            p =
              if isAttrs p then
                builtins.removeAttrs p [
                  "elemType"
                  "modules"
                ]
              else
                { };
            e = if fuel == 0 then [ ] else map (shapeOf (fuel - 1)) (elementsOf p);
          };
        # the same constructor at every node, and every node where the trees differ is one where the
        # operand states parameters: a nullary node has none for a law to widen, so a join that changes
        # it changes the operand's check (owed whole)
        widensAt =
          a: b:
          a.n == b.n
          && length a.e == length b.e
          && (a.p == b.p || a.p != { })
          && builtins.all (i: widensAt (elemAt a.e i) (elemAt b.e i)) (builtins.genList (i: i) (length a.e));
        sm = shapeOf importedTypeWalkFuel m;
        widens =
          o:
          let
            so = shapeOf importedTypeWalkFuel o;
          in
          so != sm && widensAt so sm;
        maybe = filter mayOwe os;
        notM = filter (o: !(same m o)) maybe;
        fresh = builtins.all (o: !(same m o)) os;
        relativised =
          o:
          let
            s = importedPartner (o.functor or null);
          in
          if isAttrs s && s ? check then o // { __stockCheck = s.check; } else o;
        owed = map (o: if fresh && widens o then relativised o else o) notM;
        once = if length owed == 2 && same (head owed) (elemAt owed 1) then [ (head owed) ] else owed;
      in
      if maybe == [ ] || (importedSubstructure m).modules != null || owed == [ ] then
        m
      else
        meetOf m once;
  # The join a RAW partner's own relation answers for `self`, the partner rebuilt from its published
  # functor as `joinInRebuiltPartner` rebuilds it, through `tryEval` (nixpkgs' default asserts); `null`
  # where it declines or renames.
  joinInPartnerRelation =
    self: other:
    let
      partner = importedPartner (other.functor or null);
      asked = builtins.tryEval (
        if isAttrs partner && partner ? typeMerge then partner.typeMerge self.functor else null
      );
    in
    if asked.success && isAttrs asked.value && !(joinRenames asked.value self) then
      asked.value
    else
      null;
  # What a record carries at `role`, in either vocabulary: a gen record's `carries`, a foreign record's
  # payload `elemType` (a type for `element`, a pair for `alternatives`).
  carriedAt =
    role: t:
    let
      p = (t.functor or { }).payload or null;
      e = if isAttrs p then p.elemType or null else null;
    in
    if t ? carries && !(t ? retainedRelation) then
      t.carries.${role} or null
    else if role == "element" && isAttrs e then
      e
    else if role == "alternatives" && builtins.isList e && length e == 2 then
      e
    else
      null;
  # A foreign record rebuilt over another value at `role`, by its own published constructor; `null` where
  # its functor states no payload to rebuild.
  rebuiltOverAt =
    role: carried: t:
    let
      f = t.functor or null;
    in
    if !(isAttrs f) || !(isAttrs (f.payload or null)) then
      null
    else
      importedPartner (
        f
        // {
          payload = f.payload // {
            ${roleSpelling.${role}.payloadKey} = carried;
          };
        }
      );

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
    let
      # nixpkgs' `mkOptionType` describes an undescribed type by its name (`description ? name`), so
      # a descriptor's name is never read as the vocabulary's word for one of its own constructions.
      described =
        if isAttrs d && d ? name && !(d ? description) then d // { description = d.name; } else d;
    in
    if isAttrs d && d ? name && !(d ? merge) && !(d ? mergeDefs) && !(d ? verify) then
      importType (described // { merge = mergeDescriptorDefault; })
    else
      importType described;

  # `read` is bound ONCE per import and shared by every refusal and the record: `importType` runs per
  # instance, so each re-reading is paid once per declared position (perf-bench `schemaHosts`). An
  # empty `nestedTypes` states no unroled key, so it is not re-read for one. `{ }` is the LEFT operand
  # of that test and of `unroledCollisionRefusal`'s: attrset `==` forces the left side's `type`, and a
  # nesting record's `nestedTypes` is not otherwise read to decide its import.
  # ★ THE COMPLETION STAMP AT THE BOUNDARY (gate C3, ruled arm (c)). A gen-types record carries a
  # completion stamp (`__typeSelf`, gen-types `completedType`) that a `//` copy keeps while the copy
  # changes what the record's mark stands for. This boundary REBUILDS every record it imports and
  # exports, and whatever completes a record ties its stamp, so the rebuilt record is RE-TIED here,
  # on import and on export. A record that fails the stamp on entry is a `//` copy: it is imported
  # and SERVES, but UNMINTED (owner Q3 ruling "A": the comparison site refuses an unminted pair by
  # name), keeping the stale witness, so gen-types' `typeEq` refuses it by name. Nothing is refused at
  # import. A vocabulary publishing no `stampOk` stamps nothing.
  stampOk = types.stampOk or (_: true);
  retied =
    r:
    let
      s = r // {
        __typeSelf = _: s;
      };
    in
    s;
  # The tag a demoted copy's `__mint` carries; the export reads it to keep the stale witness.
  copyMint = {
    unmintable = {
      ctor = "a `//` copy";
      reason = "a `//` over a type keeps its witness while changing what its mark stands for, so it is imported unminted";
    };
  };
  # ★ LAZY IN EVERY DECISION: the key set is fixed by `? __mint` alone, and whether the record is a
  # copy is read only when `__typeSelf` or `__mint` is. Deciding it at import would force the
  # stamp's `==` (and so the mint) while a self-referential type is still being built, which is an
  # uncatchable infinite recursion.
  restamp =
    src: r:
    if !(isAttrs src && src ? __mint) then
      r
    else
      let
        # a record whose `check` a wrapper rewrote is guarded by its check witness at every identity
        # reader (`rewritesCheck`, den-hoag-ydro3) and keeps its mark as the join's carrier; a copy
        # departing only at fields this door does not read keeps its completion's (den-hoag-59gnz C3)
        copy =
          src ? __typeSelf
          && !(rewritesCheck src)
          && !(stampOk src)
          && !(builtins.isFunction src.__typeSelf && departsOnlyOutside importReads src);
        s = r // {
          __typeSelf = if copy then src.__typeSelf else (_: s);
          __mint = if copy then copyMint else src.__mint;
        };
      in
      s;
  # WHAT EACH ENTRY DOOR READS (den-hoag-59gnz C3), derived from the partitions above, never listed here. A
  # re-completion (`defineType`) reads the fields gen's fold reads (the behaviour, tied, identity and
  # datum classes, and gen-types' check-witness pair, which `rewritesCheck` reads) and re-derives every
  # other protocol field from them. The import door (`mkOptionType`) also reads every protocol field
  # except the name-carried ones, which translate nothing. A field a door does not read is metadata
  # there: a copy departing from its completion only at such fields has its completion's distinguishing
  # content, so it keeps its completion's identity (ADR-0034: identity is structural).
  completionReads = builtins.listToAttrs (
    map
      (n: {
        name = n;
        value = null;
      })
      (
        deriveClasses.behaviour
        ++ deriveClasses.tied
        ++ deriveClasses.identity
        ++ deriveClasses.datum
        ++ [
          "check"
          "_checkWitness"
        ]
      )
  );
  importReads =
    completionReads
    // builtins.listToAttrs (
      map (n: {
        name = n;
        value = null;
      }) (filter (n: !(builtins.elem n exportClasses.nameCarried)) exportFields)
    );
  # ★ A RECORD WHOSE `verify` NO COMPLETION VOUCHES FOR (den-hoag-ndgcz): a `//` copy that replaced a
  # completed record's `verify`, or a record stating one with no completion stamp. Its `check` and
  # witness can still be its base's, so `rewritesCheck` cannot see it, and the relation it inherited
  # answers for its base's verify only. One slice of each record, compared by the pointer of its slot as
  # `stampAgrees` compares one, so the answer is the same on every evaluator for a replaced verify.
  verifySlice = builtins.intersectAttrs { verify = null; };
  replacesVerify =
    t:
    t ? verify
    && !(
      builtins.isFunction (t.__typeSelf or null) && verifySlice t == verifySlice (t.__typeSelf null)
    );
  # Whether a completed record's `//` copy departs from its completion at a field its carrier still
  # reads as the completion's (`joinRenames`' `bare`): a name-carried one, which translates nothing, or
  # `verify`, which the meet owes (`replacesVerify`). One slice of all three, asked of a stamped record.
  carrierSlice = builtins.intersectAttrs (
    builtins.listToAttrs (
      map (n: {
        name = n;
        value = null;
      }) (exportClasses.nameCarried ++ [ "verify" ])
    )
  );
  departsWithinCarrier = t: carrierSlice t != carrierSlice (t.__typeSelf null);
  # The fields at which a `//` copy may depart from its completion and still be read as it by every carrier
  # reader (`joinRenames`' `bare`, its restatement in `default.nix`, `carriedCopy`): the name-carried ones,
  # which translate nothing; `check` and `verify`, which the meet owes; and `typeMerge`, which a
  # re-completion door re-states (`carriedCopy`). The engine reads a gen record's relation at its
  # `typeMergeRel` wherever one is stated (`lib/modules.nix` `relationMergeWithin`), so `typeMerge` reaches
  # gen's engine only through a foreign container's relation asking its element's exported field; there a
  # carried copy's met relation keeps its check (den-hoag-5kzqp, its gate's `npwrap.nix`).
  carrierTolerated = exportClasses.nameCarried ++ [
    "check"
    "verify"
    "typeMerge"
  ];
  # ★ A `//` COPY A RE-COMPLETION DOOR CARRIES AS IT IS (den-hoag-5kzqp). A copy of a completed gen record
  # departing from its completion only where `joinRenames`' `bare` reads it as that completion (`check`,
  # `verify`, name-carried fields) already holds everything a door would derive but its foreign `check`:
  # its row, functor, relation and fold are its completion's, and re-deriving them from the gen datum alone
  # loses the row (`enum` publishes its caller's name with no payload, `string` publishes `string`) and
  # makes the copy its own record to every carrier reader. So the door returns it as it is, and where its
  # `verify` replaced its completion's it publishes the copy's declared domain, as the engine reads one
  # declaration alone (`meetOf`'s `dom`), as a witnessed rewrite: a foreign engine enforces it, and every
  # gen reader owes it. A copy departing only at name-carried fields keeps the door's re-tied stamp
  # (`keepStamp`). `null` for every other record. A container copy stating `verify` (`listOf`, `struct`) is
  # carried too, its own functor kept. The `verify` presence test comes first: a per-instance submodule
  # copy (gen-aspects `entryCoerced`) states none, so its stamp is never asked here.
  carriedCopy =
    x:
    if
      !(
        x ? verify
        && builtins.isFunction (x.__typeSelf or null)
        && (rewritesCheck x || departsWithinCarrier x)
      )
    then
      null
    else
      let
        c = x.__typeSelf null;
        names = carrierTolerated;
        dom =
          if x.check == x._checkWitness then
            (v: x.verify v == null)
          else
            (v: x.check v && x.verify v == null);
      in
      if
        !(stampOk (
          builtins.removeAttrs x names
          // builtins.intersectAttrs (builtins.listToAttrs (
            map (n: {
              name = n;
              value = null;
            }) names
          )) c
        ))
      then
        null
      else if replacesVerify x || rewritesCheck x then
        let
          s = x // {
            ${if replacesVerify x then "check" else null} = witnessRecord dom // {
              isV2MergeCoherent = true;
            };
            # its completion's foreign relation, met with this record, as `meetOf`'s published rewrite
            # answers: a foreign engine asking this record's `typeMerge` keeps its check
            typeMerge =
              f:
              let
                r = x.typeMerge f;
              in
              if r == null then null else metWith r [ s ];
          };
        in
        s
      else
        keepStamp x;
  # `t` departs from the record its constructor completed only at fields `reads` does not hold.
  departsOnlyOutside =
    reads: t:
    let
      c = t.__typeSelf null;
    in
    stampOk (builtins.removeAttrs c (attrNames reads) // builtins.intersectAttrs reads t);
  # THE PUBLISHED `defineType` DOOR (den-hoag-59gnz C2): a caller's record keeps the witnesses it arrived with,
  # as the raw record holds them. A record whose stamp holds, or that departs from its completion only
  # at metadata, is re-tied; any other copy keeps its stale stamp (`__staleStamp`, read by the export),
  # so `idOf` and `typeEq` refuse it by name as they refuse the raw copy, and it keeps its mark, so a
  # join reads its parameters as it reads the raw copy's. Decided lazily: only a read of `__typeSelf`
  # asks the stamp.
  keepStamp =
    t:
    # a record completed under a row and still the record it completed is the door's to return as it is
    # (`types.nix` `defineType`); the row pre-filter keeps the stamp unasked on every other record. The
    # stamp slot is tested for presence only: forcing it forces the record's mint (the export decides
    # it against `copyMint`), which gen-aspects' per-instance `//` copies never pay for otherwise
    if !(isAttrs t && t ? __typeSelf) || completedUnderRow t then
      t
    else
      let
        # a record completed under a row is returned as it is, so every field it publishes survives the
        # door, and the door reads there what the import door reads (den-hoag-59gnz gate G-1)
        stale =
          builtins.isFunction t.__typeSelf
          && !(stampOk t)
          && !(departsOnlyOutside (
            if rowFunctorNames ? ${(t.functor or { }).name or ""} then importReads else completionReads
          ) t);
        # a copy the door keeps as its completion is re-tied here, so a row's completion still returns it
        # as it is (`completedUnderRow`) and keeps the row
        s = t // {
          __typeSelf = if stale then t.__typeSelf else (_: s);
          __staleStamp = stale;
        };
      in
      s;
  importType =
    t:
    let
      answer = importType0 t;
    in
    if answer ? imported then answer // { imported = restamp t answer.imported; } else answer;
  importType0 =
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
            # (`checkedFold`), never stripped with the protocol's names (den-hoag-4ifgb).
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
              "_substSubModulesWitness"
            ]
          )
          // {
            inherit name;
            whenEmpty = importedEmpty t;
            # ★ A MODULE SET THAT CROSSED THIS DOOR IS MOUNTED, NOT FOLDED (den-hoag-6yfat). Its author
            # stated the fold and the rebuild apart, so the rebuild's merge is not this record's by
            # construction, as it is for every constructor this library ships. `mount` marks the record
            # for gen's root fix-up (`homedRootAt`), which mounts its rebuild as `fixupOptionType` mounts
            # `substSubModules`, with the record's own `check` riding on it (`mountOf`); the published
            # `substSubModules` stays the author's. Only its presence is read, and the class is re-tested
            # where it is read (`crossedRoot`). An ad-hoc `check` keeps `adHocFold`. A record stating
            # `verify` is marked too and never mounted while it states it (`crossedRoot`, `homedRootAt`):
            # its refinement is its own fold's, which a rebuild would drop, and a copy that drops the
            # `verify` is mounted as nixpkgs mounts the same copy. Presence first, so a record outside
            # the class pays no application.
            substructure =
              if
                (t.substructure.modules or t.getSubModules or null) != null
                && isList (t.substructure.modules or t.getSubModules)
                && !(adHocChecked t)
              then
                importedOwnSubstructure t // { mount = true; }
              else
                importedOwnSubstructure t;
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
          # A stated class travels with its phrase, under gen's name for it (`phraseOf`).
          // (if t ? descriptionClass then { phraseClass = t.descriptionClass; } else { })
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

  # ── THE FREEFORM DATUM, CROSSED (den-hoag-foreign-mount-parity-knhyg) ─────────────────────────
  # A nesting type states its resolved freeform type as `unroledNested.freeformType` (the tree reads
  # its own evaluation's, `submodule` its base evaluation's, as nixpkgs' `submoduleWith` reads
  # `base`'s). nixpkgs derives two more fields from it, and so does the export, in nixpkgs' words:
  # the description "open <name> of <phrase>" (`phraseOfWithin`'s freeform arm), the phrase
  # parenthesised unless its class is `noun` or `composite`, and `_freeformOptions` beside the
  # declared sub-options. Both are read only when
  # the field is, and an argument is evaluated only when read, so a type that is never described
  # abroad never resolves its freeform type here.
  freeformOf = t: (t.unroledNested or { }).freeformType or null;

  # ── THE DOCS PHRASE (den-hoag-type-description-parity-5k1l1) ──────────────────────────────────
  # nixpkgs describes a type by a phrase and a class saying where the phrase needs parentheses, and
  # a container composes its element's phrase through `optionDescriptionPhrase`. The export derives
  # the pair here, once, from what the record says about itself: a stated phrase crosses verbatim
  # with its class (nixpkgs' `mkOptionType` defaults neither beyond `description ? name`), a
  # freeform nesting type reads "open …", a container composes its carried element's phrase, and a
  # nullary type answers from the vocabulary's own word for itself. Elements are read through the
  # same function, so a foreign element answers by its own fields and a gen one by this.
  #
  # ★★ THE PHRASE IS RENDERED WITHIN A NODE BUDGET HANDED DOWN IN PREORDER, because a type can hold
  # itself (`let v = nullOr (oneOf [ str (attrsOf v) (listOf v) ]); in v`). Its phrase then denotes
  # an infinite tree, and a phrase built by reading the members' `description` needs its own value:
  # an uncatchable black hole on every foreign read of it, a refusal's text included. So a member
  # of a gen container is read through its own renderer (`__phraseWithin`) and never through its
  # `description`, which is gen-types' `__nameWithin` and this file's `importedTypeWalkFuel` again:
  # Nix has no observation that two visited nodes are one, so the walk is bounded by count.
  #
  # ★ THE ACCOUNTING IS COMPOSING NODES, NOT BYTES. Every container, union or freeform nest whose
  # phrase composes a member costs one unit, and the units are threaded through the siblings
  # (`left`), so the budget bounds the whole tree rather than its depth. A derivation stating no
  # phrase (`types.deriveType`) costs one unit too: it is described by re-entering the renderer on
  # the base it reads (`__derivation.read`), which is a descent. A leaf's text, a stated
  # description and a foreign member's own fields cost nothing: they are finite data, never a
  # descent, so they are never what diverges. Termination: each composing call, the freeform nest's
  # included, is handed `b - 1` or less, and the budget-spent arm stops every one of them at `b <= 0`.
  #
  # ★ THE CEILING, STATED: a phrase composing more than `phraseBudget` nodes elides its remaining
  # members to `…` (class `noun`, so no parentheses). nixpkgs never elides, so that is a departure,
  # and it is placed past every real shape measured: the deepest composed phrase in nixpkgs' NixOS
  # option tree composes 35 nodes, and no type in the gen roster or the gen-demo corpus composes more
  # than 3 (den-hoag-type-description-parity-5k1l1 respec v1). Below the ceiling the phrase is
  # byte-identical to nixpkgs', whatever its length: a 20 KB enum costs one leaf.
  #
  # ★ THE PRICE IS PER LAP. On a cyclic type every lap re-emits its leaves at no cost, so the elided
  # phrase is bounded by `phraseBudget` times the widest text one lap emits, not by a byte figure:
  # 1 473 B for `v` above, 1 850 177 B for a cycle carrying a 1 500-member enum (whose refusal still
  # terminates and is still caught, at about 444 MB RSS). No byte cap is placed on it: one would
  # have to stay above the widest single leaf to keep parity, and it bounds no descent.
  phraseBudget = 128;
  elided = {
    text = "…";
    class = "noun";
    left = 0;
  };
  # A member's phrase within budget `b`: a gen export's own renderer, else its stated fields (cost 0).
  phraseOfMember =
    b: e:
    if isAttrs e && isFunction (e.__phraseWithin or null) then
      e.__phraseWithin b
    else
      phraseOfWithin b e;
  memberWithin =
    classes: b: e:
    let
      p = phraseOfMember b e;
    in
    {
      text = if builtins.elem p.class classes then p.text else "(${p.text})";
      inherit (p) left;
    };
  # What a derivation keeps of its base's phrase: both halves, as nixpkgs' `base // { … }` keeps them.
  carriedPhrase =
    t:
    let
      p = statedPhrase t;
    in
    {
      description = p.text;
      phraseClass = p.class;
    };
  statedPhrase = t: {
    text = t.description;
    class = if isOptionType t then t.descriptionClass or null else t.phraseClass or null;
  };
  noun = text: {
    inherit text;
    class = "noun";
  };
  # The leaf vocabulary's nouns, keyed by its CONSTRUCTION (`payloadOf`'s `prim` coordinate), never
  # by name: a caller's `typedef "int"` is sealed, reads no payload, and is described by its name.
  primPhrase = {
    int = noun "signed integer";
    string = noun "string";
    bool = noun "boolean";
    float = noun "floating point number";
    number = {
      text = "signed integer or floating point number";
      class = "conjunction";
    };
    path = noun "absolute path";
    # The vocabulary's own leaves with no nixpkgs namesake, in the same register.
    any = noun "any value";
    list = noun "list";
    function = noun "function";
    derivation = noun "derivation";
    null = noun "null";
    never = noun "impossible (no value)";
    # nixpkgs' `pathWith { }`, whose description is the bare noun.
    pathLike = noun "path";
  };
  showEnumMember =
    v:
    if builtins.isString v then
      "\"${v}\""
    else if builtins.isInt v then
      toString v
    else if builtins.isBool v then
      (if v then "true" else "false")
    else
      "<${builtins.typeOf v}>";
  payloadPhrase =
    t:
    let
      r = builtins.tryEval (
        if types ? payloadOf then
          let
            p = types.payloadOf t;
          in
          builtins.deepSeq p (if isAttrs p && p ? ctor && p ? args then p else null)
        else
          null
      );
      p = if r.success then r.value else null;
      elems = if p != null && isAttrs p.args then p.args.elems or null else null;
    in
    if p == null then
      null
    else if p.ctor == "prim" && builtins.isString p.args && primPhrase ? ${p.args} then
      primPhrase.${p.args}
    else if p.ctor == "enum" && isList elems then
      if elems == [ ] then
        noun "impossible (empty enum)"
      else if length elems == 1 then
        noun "value ${showEnumMember (head elems)} (singular enum)"
      else
        {
          text = "one of ${concatStringsSep ", " (map showEnumMember elems)}";
          class = "conjunction";
        }
    else
      null;
  phraseOf = t: builtins.removeAttrs (phraseOfWithin phraseBudget t) [ "left" ];
  phraseOfWithin =
    b: t:
    let
      name = t.name or "raw";
      ff = freeformOf t;
      carried = t.carries or { };
      el = carried.element or null;
      alts = carried.alternatives or null;
      # a phrase that spends nothing
      flat = p: p // { left = b; };
      # one composing node: costs a unit, then its members share what is left
      over =
        class: prefix: classes: e:
        let
          m = memberWithin classes (b - 1) e;
        in
        {
          inherit class;
          text = prefix + m.text;
          inherit (m) left;
        };
      leaf = payloadPhrase t;
    in
    if !(isAttrs t) then
      flat {
        text = nameOf t;
        class = null;
      }
    else if t ? description then
      flat (statedPhrase t)
    # a derivation stating no phrase says its base's: one descent, so it costs a unit like any other
    else if t ? __derivation then
      if b <= 0 then elided else phraseOfMember (b - 1) t.__derivation.read
    else if (ff != null || el != null || alts != null) && b <= 0 then
      elided
    else if ff != null then
      let
        m = memberWithin [ "noun" "composite" ] (b - 1) ff;
      in
      {
        text = "open ${name} of ${m.text}";
        class = null;
        inherit (m) left;
      }
    else if el != null && name == "listOf" then
      over "composite" "list of " [ "noun" "composite" ] el
    else if el != null && name == "attrsOf" then
      over "composite" "attribute set of " [ "noun" "composite" ] el
    else if el != null && name == "lazyAttrsOf" then
      over "composite" "lazy attribute set of " [ "noun" "composite" ] el
    else if el != null && name == "nullOr" then
      over "conjunction" "null or " [ "noun" "conjunction" ] el
    else if isList alts && length alts == 2 && name == "either" then
      let
        pa = phraseOfMember (b - 1) (head alts);
        ta =
          if pa.class == "nonRestrictiveClause" then
            "${pa.text},"
          else if
            builtins.elem pa.class [
              "noun"
              "conjunction"
            ]
          then
            pa.text
          else
            "(${pa.text})";
        mb = memberWithin (
          if pa.class == "nonRestrictiveClause" then
            [
              "noun"
              "conjunction"
            ]
          else
            [
              "noun"
              "conjunction"
              "composite"
            ]
        ) pa.left (elemAt alts 1);
      in
      {
        class = "conjunction";
        text = "${ta} or ${mb.text}";
        inherit (mb) left;
      }
    else if leaf != null then
      flat leaf
    else if name == "raw" then
      flat (noun "raw value")
    else if name == "anything" then
      flat (noun "anything")
    else if name == "deferredModule" then
      flat (noun "module")
    else if name == "attrs" then
      flat {
        text = "attribute set";
        class = null;
      }
    else
      flat {
        text = name;
        class = null;
      };
  freeformSubOptions =
    declares: ff: prefix:
    if ff == null then
      declares prefix
    else
      declares prefix // { _freeformOptions = ff.getSubOptions prefix; };

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
  exportType = exportTypeWith null;
  # `row` is the `embeddings` row the type's gen-merge constructor states (`types.nix`
  # `defineEmbedded`), or `null`, which every other caller hands. With none, a completed gen-types
  # leaf handed to a published door as it is (`defineType gm.types.string`) is read off `t` itself
  # (`embedsOf`: its mint, under its stamp; `mkTypeWith` completes such a record without copying it),
  # inside the two fields that use it, so the export allocates nothing per call. A rebuilt container
  # is re-exported under its constructor's row.
  exportTypeWith =
    row: t:
    let
      role = if t ? carries then roleOf (nameOf t) t.carries else null;

      # Built once by gen-types' `witnessRecord` and published twice, as `check` and as
      # `_checkWitness` (below), so a `check` a wrapper rewrote is the one slot that no longer holds
      # the witness (`rewritesCheck`). The pair is spelled here rather than taken from
      # `witnessedCheck`, whose two-field result every exported type would read or copy
      # (den-hoag-ydro3, owner-ruled arm (c)); `default.nix`'s agreement door holds this spelling to
      # its output. The record is extended by `isV2MergeCoherent`, because the export answers
      # `merge.v2` (below) and nixpkgs' `checkV2MergeCoherence` refuses a v2 type whose `check` does
      # not say it is the one its merge was built with (den-hoag-c2z7q).
      # ★ A RE-COMPLETION NEVER RE-TIES THE WITNESS OVER A CHECK IT DID NOT DERIVE (den-hoag-59gnz C1): a
      # record arriving as a witnessed rewrite publishes its own `check` and its stale `_checkWitness`
      # unchanged, so every identity reader and the meet read the copy as they read the raw record.
      check =
        if t ? _checkWitness && t.check != t._checkWitness then
          t.check
        else
          witnessRecord (
            if t ? verify then
              (v: t.verify v == null)
            else if t ? admits then
              t.admits
            else
              (_: true)
          )
          // {
            isV2MergeCoherent = true;
          };
      # The rebuild, built once by the same `witnessRecord` and published twice, as `substSubModules`
      # and as `_substSubModulesWitness`.
      rebuild = witnessRecord (
        m:
        if threadElementOf m != null then
          threadElementOf m exported
        else if (t.substructure or null) == null then
          null
        else
          t.substructure.rebuild m
      );

      # `typeMerge` and `functor` are ONE derivation from ONE gen datum. The relation is row-free —
      # it takes the other TYPE — so the outbound half recovers a type from whatever functor arrives
      # and the inbound half publishes a functor a foreign engine can recover THIS type from.
      functor =
        let
          name = t.name or "raw";
          embeds = if row != null then row else embedsOf t;
          # Rebuild this type over a payload in the protocol's spelling — the inverse of `payload` below,
          # and the only inversion needed, because the role is fixed by the type rather than guessed.
          recarried = p: t.recarry { ${role} = p.${roleSpelling.${role}.payloadKey}; };
          extrasAgree =
            p:
            if embeds ? members then
              membersAgree (p.${roleSpelling.alternatives.payloadKey} or null
              ) embeds.params.${roleSpelling.alternatives.payloadKey}
            else
              builtins.all (k: (p.${k} or null) == embeds.params.${k}) (attrNames (embeds.params or { }));
        in
        {
          # Read by the functor alone, so it is built when the functor is: a binding beside the
          # export's other fields is a thunk on every exported type (den-hoag-c7jkw.2). The embedding
          # is read inside it, never as a binding of its own, for the same reason.
          payload =
            if row != null then
              embeddedPayload row role (if role == null then null else t.carries.${role})
            else if embedsOf t != null then
              embeddedPayload (embedsOf t) role (if role == null then null else t.carries.${role})
            else if role == null then
              null
            else if role == "moduleSet" then
              moduleSetPayload {
                modules = t.carries.${role};
                specialArgs = t.specialArgs or { };
                shorthandOnlyDefinesConfig = t.shorthandOnlyDefinesConfig or null;
              }
            else
              {
                ${roleSpelling.${role}.payloadKey} = t.carries.${role};
              };
          # A derivation keeps its base's `name` and is keyed on its own identity (`keyOf`).
          name =
            if t ? __derivation then
              t.__derivation.id
            else if embeds != null then
              embeds.name
            else
              name;
          # Over an embedding, a payload whose fixed parameters are not this type's is a construction
          # this type cannot be rebuilt as: refused by name, as `substructure.rebuild` refuses static
          # modules, never rebuilt at its own parameters with the caller's dropped. The refusal is
          # spelled in each arm rather than bound, so the export carries no thunk for it.
          type =
            if role == null && (embeds == null || !(embeds ? params)) then
              exported
            else if role == null then
              (
                p:
                if extrasAgree p then
                  exported
                else
                  throw "gen-merge: `${name}' cannot be rebuilt over a `${embeds.name}' payload other than its own embedding"
              )
            else if embeds == null then
              (p: exportTypeWith row (recarried p))
            else
              (
                p:
                if extrasAgree p then
                  exportTypeWith row (recarried p)
                else
                  throw "gen-merge: `${name}' cannot be rebuilt over a `${embeds.name}' payload other than its own embedding"
              );
          binOp =
            if role == null && (embeds == null || !(embeds ? params)) then
              (_a: _b: null)
            else if role == null then
              (a: b: if extrasAgree a && extrasAgree b then embeds.params else null)
            else
              (
                a: b:
                let
                  ra = recarried a;
                  rb = recarried b;
                  # the relation's entry: its pre-flight, as `lib/modules.nix` `relationMerge` states
                  answer = if importedDecidable ra && importedDecidable rb then ra.typeMergeRel rb else { };
                in
                if embeds != null && !(extrasAgree a && extrasAgree b) then
                  null
                else if !(answer ? merged) || !(answer.merged ? carries) then
                  null
                else
                  (if embeds == null then { } else embeds.params)
                  // {
                    ${roleSpelling.${role}.payloadKey} = answer.merged.carries.${role};
                  }
              );
        };

      phrase = phraseOf t;
      # the export completes the record, so it re-ties the stamp the import tied; a demoted copy keeps
      # its stale witness (`restamp`). Lazy for the reason `restamp` is, and a key of the one attrset
      # below rather than a `//` layer of its own (a null name adds no attribute).
      exported = t // {
        ${if t ? __typeSelf then "__typeSelf" else null} =
          if t.__staleStamp or false || (t.__mint or null) == copyMint then t.__typeSelf else (_: exported);
        # this type's phrase within a budget, for a container reading it as a member (`phraseOfMember`)
        __phraseWithin = b: phraseOfWithin b t;
        _type = "option-type";
        descriptionClass = phrase.class;
        # a record stating its `name` keeps it, and only a nameless one is published as `raw`
        ${if t ? name then null else "name"} = "raw";
        # ★★ THE CALLER'S FUNCTOR IS REPUBLISHED WITH ITS NAME INTACT, AND THAT NAME GOVERNS. The
        # derivation above is what a type with no stated relation is published as; overwriting a
        # stated one with it is name-only identity re-imposed at a KEYING site with the
        # distinguishing content available (ADR-0034), and it is what makes a refinement merge with
        # the base it exists to be distinguished FROM. Preserving it fails closed instead.
        # It is read off `retainedRelation', a differently-named gen datum, exactly as every other
        # derived field is read off one — see the retention site in `importType' for why.
        functor = t.retainedRelation.functor or functor;
        description = phrase.text;
        # Decided by the record's own attribute presence, so each arm is published as written: a
        # computed field is a thunk on every exported type (den-hoag-c7jkw.2). `_protoLeafMerge` below too.
        ${if t ? deprecated then "deprecationMessage" else null} = t.deprecated;
        ${if t ? deprecated then null else "deprecationMessage"} = null;
        # `_checkWitness` is not a fifteenth protocol field: it is gen-types' check-witness
        # protocol field, the record of which `check` was published, read only by `rewritesCheck`.
        # A witnessed rewrite keeps its own stale witness (C1): the name is decided at construction, so
        # `t`'s binding survives the `//` and no per-export thunk is allocated for the choice.
        inherit check;
        ${if t ? _checkWitness && t.check != t._checkWitness then null else "_checkWitness"} = check;
        # Through the bridge where the fold carries the sibling (den-hoag-n6dh7 item 7, OQ11 (d)):
        # a nesting type's tree is one root evaluation, and a gen container threads the bridge to
        # each element through its one `split`, so the forward mount keeps working without a third
        # fold form. Every other fold publishes as it did (`bridged`'s presence arm).
        #
        # A type publishing a HEAD JUDGEMENT (`mergeDefs.headJudge`) answers nixpkgs' `merge.v2`
        # too, as nixpkgs' own `either`, `nullOr` and `addCheck` do (den-hoag-c2z7q), so a nixpkgs
        # union holding it asks it for its `headError` rather than judging it by `check` alone,
        # and takes the next member where gen's own fold would refuse the definitions whole. A
        # type stating none publishes the bare fold, as nixpkgs' leaves do: its `headError` would
        # be the pointwise check alone, which nixpkgs' v1 reading already computes, and a v2
        # `merge` would make nixpkgs refuse the ad-hoc `type // { check = …; }` it accepts on a
        # v1 type (den-hoag-e6m9d landing gate F1). The `headError` is the published `check` over each
        # definition, then the record's head judgement: under v2, nixpkgs' `mergeDefinitions`
        # reads only this, never `check`, so the pointwise half is what keeps a gen leaf verified
        # there. The functor calls the fold directly, so a caller applying `merge` pays no
        # judgement, and the judgement is written inside `v2`, so a type nothing asks pays nothing.
        merge =
          let
            fold = if !(t ? mergeDefs) then leafFold else bridged t.mergeDefs;
          in
          if !(t ? mergeDefs.headJudge) then
            fold
          else
            {
              __functor = _: fold;
              v2 =
                { loc, defs }:
                {
                  headError =
                    let
                      bad = filter (d: !(check d.value)) defs;
                      judged = t.mergeDefs.headJudge loc defs;
                    in
                    if bad != [ ] then
                      {
                        message = "Definition values: ${
                          concatStringsSep ", " (map (d: "`${toString (d.file or "<def>")}'") bad)
                        }";
                      }
                    else if t ? mergeDefs.headJudge && judged != null then
                      { message = judged; }
                    else
                      null;
                  value = fold loc defs;
                  valueMeta = { };
                };
            };
        # A nesting type's empty value is its tree over no definitions, through the same bridge: its
        # called `whenEmpty` refuses (den-hoag-n6dh7 item 1).
        emptyValue =
          if isNesting t then { value = t.mergeDefs.threaded bridge [ ] [ ]; } else t.whenEmpty or { };
        nestedTypes =
          (t.unroledNested or { })
          // (if role == null then { } else roleSpelling.${role}.nested t.carries.${role});
        getSubOptions =
          if (t.substructure or null) == null then
            (_prefix: { })
          else
            freeformSubOptions t.substructure.declares (freeformOf t);
        getSubModules = if (t.substructure or null) == null then null else t.substructure.modules;
        # Published under both fields, as `check` is: a copy that rewrote `substSubModules` is the
        # one record whose field no longer holds the witness (`importedOwnSubstructure`).
        substSubModules = rebuild;
        _substSubModulesWitness = rebuild;
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
            # the relation's entry: its pre-flight, as `lib/modules.nix` `relationMerge` states
            else if !(importedDecidable t && importedDecidable partner) then
              null
            else
              (
                let
                  answer = t.typeMergeRel partner;
                in
                # a foreign engine hands gen a FUNCTOR: a wrapper's check on the record it holds is
                # invisible here, so a join the twin refuses (`twinRefuses`) is refused as the twin does
                if answer ? merged && !(answer.twinRefuses or false) then
                  metWith answer.merged [
                    exported
                    partner
                  ]
                else
                  null
              )
          );

        # Not a fifteenth protocol field: gen's own record of whether the fold published above is
        # the type's or this boundary's. It exists BECAUSE the boundary exists — the export half
        # publishes a fold for every type, so past this point presence cannot answer the question —
        # and it is derived from the gen record's own `mergeDefs`, never defaulted true, because a
        # `true` marker outliving a real fold drops that fold silently. The engine no longer needs
        # it on the gen path, which reads `mergeDefs` directly; it is read on the FOREIGN path,
        # where a completed record stripped of its gen half would otherwise re-enter the core's own
        # fold through the type. The field retires with the completion, not with the engine's read.
        ${if t ? mergeDefs then "_protoLeafMerge" else null} = false;
        ${if t ? mergeDefs then null else "_protoLeafMerge"} = true;
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

in
{
  inherit
    importedHeadJudge
    admitsCarried
    checkedFold
    closuresFirst
    carriedPhrase
    deriveClasses
    exportClasses
    exportFields
    exportType
    exportTypeWith
    importDescriptor
    importType
    importedAdmits
    importedRehome
    isNesting
    joinInStatedRelation
    joinCarriedInStatedRelation
    joinInRebuiltPartner
    joinLeafInStatedRelation
    statesPayload
    keysExactly
    meetOf
    metWith
    carriedAt
    carriedAtDepth
    joinInPartnerRelation
    rebuiltOverAt
    embeddedOffered
    embeddings
    embedsOf
    rowOver
    completedUnderRow
    keyedUnderEmbedding
    moduleSetPayload
    canNest
    declaresNesting
    homedAt
    homedRootAt
    crossedRoot
    mayFoldNested
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
    replacesVerify
    departsWithinCarrier
    keyOf
    nameOf
    functorNamesOf
    moduleOwnTypeAdmits
    moduleLeafSubOptions
    importedPartner
    importedRebuilds
    importedSubstructure
    spineModules
    spineDeclares
    importedTypeWalkFuel
    importedWrapped
    isOptionType
    rewritesCheck
    keepStamp
    carriedCopy
    carrierTolerated
    typeDefect
    ;
}
