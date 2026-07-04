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

  # mkOptionType — the (loc,defs) custom-merge escape hatch (spec §1 item 6). A type IS its
  # `{ name; check?; merge?; verify? }` record, so this is an identity constructor; consumers write
  # `mkOptionType { name = "aspect"; merge = loc: defs: …; }` and gen-merge dispatches on `.merge`.
  mkOptionType = descriptor: descriptor;

  # Turn a def value into a module (located) for a nested evalModuleTree.
  defToModule = d: setDefaultModuleLocation (toString (d.file or "<def>")) d.value;

  # submodule — recurse into a nested evalModuleTree over the submodule module + all defs; binds the
  # per-key `name` (spec §1 item 3). One nested fixpoint per merge (spec §1 item 4).
  submodule =
    modOrMods:
    let
      mods = if isList modOrMods then modOrMods else [ modOrMods ];
    in
    {
      name = "submodule";
      getSubModules = mods;
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
  listOf = elemType: {
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
  attrsOfWith = tyName: elemType: {
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
  deferredModule = {
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
  nullOr = elemType: {
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
  either = a: b: {
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

  # raw — opaque single value (mergeOneOption); no verify, no structural merge → the core mergeLeaf
  # handles it (one winner, or equal winners).
  raw = {
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
  anything = {
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
