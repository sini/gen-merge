# Structural merge-strategy types (spec §2 + §4).
#
# These are the MERGE half — the types that own how their defs combine. Each carries a `.merge loc
# defs`. Leaf CHECKING types (str/int/bool/enum/path/…) come from gen-types (injected), NOT here —
# gen-merge answers "how do defs combine?", gen-types answers "is v well-typed?" (spec §4). `raw`
# and `anything` live here because they are defined by their MERGE behavior (one-def / recursive),
# not by a value predicate.
{
  prelude,
  core,
}:
let
  inherit (prelude)
    isList
    isAttrs
    concatMap
    concatLists
    map
    attrNames
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
    evalModuleTree
    mergeDefs
    showOption
    setDefaultModuleLocation
    ;

  # mkOption — a plain descriptor; evalModuleTree reads .type/.default/.apply/.readOnly. Identity
  # (tagged) so the gen-aspects/gen-schema re-host is a `lib.mkOption` → `mkOption` rename.
  mkOption = descriptor: descriptor // { _type = "option"; };

  # ── nixpkgs optionType PROTOCOL completion ──────────────────────────────────────────────────────
  # A gen-merge type must mount inside a REAL nixpkgs `lib.evalModules` (nix-config's
  # `mkInstanceRegistry`-in-flake-parts is the proven consumer: gen-schema injects gen-merge-typed
  # options — mkIdentityModule's `id_hash`, mkStrictModule's freeform — into a submodule the corpus
  # evaluates with nixpkgs). nixpkgs' module system reads a FIXED field-set off every option type
  # (`deprecationMessage`/`check`/`merge`/`emptyValue`/`getSubModules`/`substSubModules`/`nestedTypes`/
  # `functor`/`typeMerge`/…). The pure re-host carried only the MERGE half; this completes the shape
  # PURELY (no nixpkgs import — same philosophy as gen-merge's byte-compat merge).
  #
  # ADDITIVE + behaviour-preserving to gen-merge's OWN core (verified against modules.nix `mergeDefs`):
  # the fold dispatches on `.merge` (else `mergeLeaf`) and validates via `.verify` — never `.check`. So
  # the only field the core newly-sees is `.merge` added to a leaf, and its default equals `mergeLeaf`
  # on the same defs (byte-identical fold). `.check` is read ONLY by the union `isValid`, which prefers
  # `.verify`; a leaf keeps its verify, a structural without a check gets `_: true` (preserving the
  # prior `isValid = true`). See ci/tests for the mount witness + the byte-identity gates.
  pureDefaultFunctor = name: {
    inherit name;
    type = null;
    payload = null;
    binOp = _a: _b: null;
  };
  # nixpkgs `defaultTypeMerge`, replicated purely: same-name types merge (via payload binOp when
  # present, else the type constructor); different names ⇒ null ("not mergeable").
  pureTypeMerge =
    functor: f':
    if functor.name != (f'.name or null) then
      null
    else if functor.payload != null then
      (
        let
          mp = functor.binOp functor.payload (f'.payload or null);
        in
        if mp == null then null else functor.type mp
      )
    else
      functor.type;
  # Leaf merge = nixpkgs `mergeEqualOption` = gen-merge's `mergeLeaf` on {file,value} defs (one def, or
  # all-equal, else conflict) — so a leaf that gains this `.merge` folds byte-identically to before.
  protoLeafMerge =
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

  # completeType — stamp the full nixpkgs protocol onto a type, each field overridable by the
  # descriptor (a real `.merge`/`.check`/`.substSubModules`/`.functor` a type already carries wins).
  # Self-referential: the default functor's `type` points at the completed type, so `typeMerge` of two
  # same-named types returns the type (nixpkgs `defaultTypeMerge`'s self-merge), null across names.
  completeType =
    t:
    let
      name = t.name or "raw";
      functor = t.functor or (pureDefaultFunctor name // { type = result; });
      result = t // {
        _type = "option-type";
        inherit name functor;
        description = t.description or name;
        descriptionClass = t.descriptionClass or null;
        deprecationMessage = t.deprecationMessage or null;
        # check (v -> bool): mirror the union `isValid` order — a gen-types leaf's `verify` (v -> null|err)
        # gives a REAL derived check (its own `.check` is CURRIED, must not be used as v -> bool); a
        # gen-merge structural keeps its own v -> bool `check` (nullOr/either); anything else defers to
        # merge (`_: true`, the nixpkgs `anything` posture, preserving the prior `isValid = true`).
        check =
          if t ? verify then
            (v: t.verify v == null)
          else if t ? check then
            t.check
          else
            (_: true);
        merge = t.merge or protoLeafMerge;
        emptyValue = t.emptyValue or { };
        getSubOptions = t.getSubOptions or (_prefix: { });
        getSubModules = t.getSubModules or null;
        substSubModules = t.substSubModules or (_m: null);
        typeMerge = t.typeMerge or (pureTypeMerge functor);
        nestedTypes = t.nestedTypes or { };
      };
    in
    result;

  # mkOptionType — the (loc,defs) custom-merge escape hatch (spec §1 item 6) AND the protocol
  # completion: a type IS its `{ name; check?; merge?; verify? }` record, completed to the full nixpkgs
  # optionType shape. Consumers write `mkOptionType { name = "aspect"; merge = loc: defs: …; }` and get
  # a type that both gen-merge (dispatches on `.merge`) and nixpkgs (reads the full protocol) accept.
  mkOptionType = completeType;

  # Turn a def value into a module (located) for a nested evalModuleTree.
  defToModule = d: setDefaultModuleLocation (toString (d.file or "<def>")) d.value;

  # submodule — recurse into a nested evalModuleTree over the submodule module + all defs; binds the
  # per-key `name` (spec §1 item 3). One nested fixpoint per merge (spec §1 item 4).
  submodule =
    modOrMods:
    let
      mods = if isList modOrMods then modOrMods else [ modOrMods ];
    in
    mkOptionType {
      name = "submodule";
      getSubModules = mods;
      # nixpkgs protocol: rebuild the submodule type with the module set nixpkgs supplies (read at
      # modules.nix:1477 for submodule-typed options). REPLACES `mods` — it does NOT append: nixpkgs'
      # `mergeOptionDecls` builds `m` as `map (setDefaultModuleLocation _file) type.getSubModules ++
      # res.options`, i.e. this type's OWN modules (relocated) plus any sibling declarations. Concatenating
      # would re-include `mods` a second time, double-evaluating the base module (a readOnly config value —
      # e.g. gen-schema's `den.schema._kindNames` — then throws "defined 2 times"). This mirrors nixpkgs
      # `submoduleWith.substSubModules = m: submoduleWith (attrs // { modules = m; })`.
      substSubModules = m: submodule (if isList m then m else [ m ]);
      merge =
        loc: defs:
        (evalModuleTree {
          modules = mods ++ map defToModule defs;
          prefix = loc;
          specialArgs = {
            name = if loc == [ ] then "" else prelude.last loc;
          };
          check = true;
        }).config;
    };

  # listOf — concat all list defs in order (byte-mode drops the order pass; spec §7), each element
  # merged through the element type (a submodule element becomes an instance; a leaf is verified).
  listOf =
    elemType:
    mkOptionType {
      name = "listOf";
      inherit elemType;
      # nixpkgs-parity introspection alias — lets a consumer's type-tree walker (e.g. gen-schema's
      # `mkCoerceChain`, which reads `t.nestedTypes.elemType`) recurse unchanged.
      nestedTypes = { inherit elemType; };
      merge =
        loc: defs:
        concatMap (
          d:
          imap0 (
            i: v:
            mergeDefs (loc ++ [ (toString i) ]) elemType [
              {
                inherit (d) file;
                value = v;
              }
            ]
          ) d.value
        ) defs;
    };

  # attrsOf / lazyAttrsOf — per-key merge through the element type. Byte-mode output is identical
  # for both (Nix values are already lazy — spec §1 item 2); kept as distinct names for the surface.
  attrsOfWith =
    tyName: elemType:
    mkOptionType {
      name = tyName;
      inherit elemType;
      nestedTypes = { inherit elemType; };
      merge =
        loc: defs:
        let
          # key union via attrset fold — a list `unique` is O(k²) in key count
          keys = attrNames (foldl' (acc: d: acc // d.value) { } defs);
        in
        listToAttrs (
          map (k: {
            name = k;
            value = mergeDefs (loc ++ [ k ]) elemType (
              concatMap (
                d:
                optional (d.value ? ${k}) {
                  inherit (d) file;
                  value = d.value.${k};
                }
              ) defs
            );
          }) keys
        );
    };
  attrsOf = attrsOfWith "attrsOf";
  lazyAttrsOf = attrsOfWith "lazyAttrsOf";

  # deferredModule (spec §1 item 7) — collect defs into ONE module (via imports), located; NEVER
  # forced by the composition plane. Output is a plain, import-usable module value (nixpkgs-faithful:
  # `types.deferredModule.merge` produces `{ imports = [ … ]; }`), handed opaque to the terminal.
  deferredModule = mkOptionType {
    name = "deferredModule";
    merge = loc: defs: {
      imports = map (
        d: setDefaultModuleLocation "${toString (d.file or "<def>")}, via option ${showOption loc}" d.value
      ) defs;
    };
  };

  # Membership predicate for union dispatch. gen-types leaf checkers expose `verify` (v → null|err);
  # gen-merge structural types expose a 1-arg `check` (v → bool). Prefer `verify` FIRST — a gen-types
  # `check` is curried (not v → bool), so it must never be applied here.
  isValid =
    t: v:
    if t ? verify then
      t.verify v == null
    else if t ? check then
      t.check v
    else
      true;

  # nullOr / option — a MERGE-aware nullable (NOT a gen-types verify-only `option`, which would drop
  # a wrapped merge-type's behaviour, e.g. a ref field's coercion). null defs drop; non-null defs
  # merge through the element type (leaf verify or ref/submodule merge, via mergeDefs). Carries
  # `name = "nullOr"` + `nestedTypes.elemType` so gen-schema's coercion walker treats it like nixpkgs.
  nullOr =
    elemType:
    mkOptionType {
      name = "nullOr";
      nestedTypes = { inherit elemType; };
      check = v: v == null || isValid elemType v;
      merge =
        loc: defs:
        let
          nonNull = filter (d: d.value != null) defs;
        in
        if nonNull == [ ] then null else mergeDefs loc elemType nonNull;
    };
  option = nullOr;

  # either A B — recursion-safe lazy union: dispatch on the shape of the first winner (byte-mode
  # best-effort; the surface's only use is aspectOrFn where A's check is total).
  either =
    a: b:
    mkOptionType {
      name = "either";
      nestedTypes = {
        left = a;
        right = b;
      };
      check = v: isValid a v || isValid b v;
      # Dispatch on the first value's shape, then merge through the chosen type via mergeDefs so leaf
      # members (str/int, no `.merge`) verify and merge-bearing members (ref/submodule) recurse.
      merge =
        loc: defs:
        let
          chosen = if defs != [ ] && isValid a (head defs).value then a else b;
        in
        mergeDefs loc chosen defs;
    };

  # oneOf [t1 t2 …] — n-ary either (right-nested). One use on the surface (schema either-chains).
  oneOf =
    ts:
    if ts == [ ] then
      throw "gen-merge: oneOf: empty type list"
    else if length ts == 1 then
      head ts
    else
      either (head ts) (oneOf (tail ts));

  # raw — opaque single value; the protocol completion supplies `merge = protoLeafMerge`, byte-identical
  # to the core `mergeLeaf` fallback this type relied on (one winner, or equal winners).
  raw = mkOptionType {
    name = "raw";
  };

  # anything — recursive value merge (lists concat, attrsets per-key recurse, else last-wins). Used
  # by non-strict instance freeform + niche raw-ish spots; byte-mode-adequate, not the full nixpkgs
  # `types.anything` module-composition of function values.
  mergeAnythingVals =
    vals:
    if vals == [ ] then
      throw "gen-merge: anything: no definitions"
    else if all isList vals then
      concatLists vals
    else if all isAttrs vals then
      let
        keys = attrNames (foldl' (acc: v: acc // v) { } vals);
      in
      listToAttrs (
        map (k: {
          name = k;
          value = mergeAnythingVals (concatMap (v: optional (v ? ${k}) v.${k}) vals);
        }) keys
      )
    else
      prelude.last vals;
  anything = mkOptionType {
    name = "anything";
    merge = _loc: defs: mergeAnythingVals (map (d: d.value) defs);
  };
in
{
  inherit
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
}
