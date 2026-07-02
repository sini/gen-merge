# Core byte-mode merge engine — `evalModuleTree` + the shared `mergeDefs` fold.
#
# Design spec §1 (the 7-item primitive) + §2 (API). Reproduces `lib.evalModules` merge OUTPUT for
# den's surface with none of `lib.types`: collect+flatten imports, tie the self-referential `config`
# fixpoint (one local `fix` per call — spec §1 item 4), collect per-option defs, priority-resolve
# (spec §1 priority subset, via ./priority.nix), dispatch structural types to their `.merge`
# strategy, route unknown keys through the freeformType, and check leaves via the injected gen-types
# `verify`. Class layering: gen-prelude → gen-types → gen-merge (this) → {gen-schema, gen-aspects}.
{ prelude, priority }:
let
  inherit (prelude)
    isAttrs
    isList
    isFunction
    functionArgs
    concatMap
    foldl'
    filter
    map
    mapAttrs
    attrNames
    listToAttrs
    concatStringsSep
    optional
    unique
    length
    head
    tail
    all
    ;
  inherit (priority)
    dischargeProperties
    filterOverrides
    pushDownProperties
    mkOptionDefault
    ;

  showOption = loc: concatStringsSep "." loc;

  reverse =
    xs:
    let
      n = length xs;
    in
    prelude.genList (i: prelude.elemAt xs (n - 1 - i)) n;

  # Vendored module-convention helper (audit §4 — a ~2-line pure attrset constructor, NOT the
  # `lib.types` machinery): tag a module with its definition site for error provenance.
  setDefaultModuleLocation = file: m: {
    _file = file;
    imports = [ m ];
  };

  # Deep attrset merge (rhs wins at leaves) — for the `_module` pseudo-tree and the final
  # declared-over-freeform config merge (~:433).
  recursiveUpdate =
    lhs: rhs:
    lhs
    // mapAttrs (
      n: v:
      if (lhs ? ${n}) && isAttrs (lhs.${n} or null) && isAttrs v then recursiveUpdate lhs.${n} v else v
    ) rhs;

  # An option-decl LEAF is a `mkOption` descriptor (tagged `_type = "option"` at lib/types.nix:39).
  # Anything else inside the `options` tree is an option-GROUP: a plain attrset of sub-declarations.
  isOptLeaf = v: isAttrs v && (v._type or null) == "option";

  # mergeOptionDecls — combine two option-decl TREES (nixpkgs mergeModules' descent, byte-mode).
  # This is what lets `options.a.b.c = mkOption {…}` build a NESTED tree rather than the old
  # single-level view:
  #   leaf ∪ leaf  = field-union, later wins (as the flat fold always did — e.g. a ref-binding
  #                  module layering `apply` onto an earlier `{ type; default; }`);
  #   group ∪ group = RECURSE (a second module's `options.a.b.d` merges beside `options.a.b.c`);
  #   leaf ⁄ group at the same path = a hard collision (nixpkgs likewise refuses to make an option
  #                  the parent of sub-options) — must throw, never silently `//`-merge.
  # DELIBERATE divergence: nixpkgs' `optionTreeToOption` (modules.nix:895-913) has one sugar case —
  # raw options merged INTO a `submodule`-typed leaf — that byte-mode does not reproduce (out of the
  # den surface; submodule nesting rides the separate `submodule`/`attrsOf` `.merge` path). Byte-mode
  # conservatively throws here rather than risk emitting wrong bytes.
  mergeOptionDecls =
    loc: a: b:
    a
    // mapAttrs (
      k: bv:
      let
        lk = loc ++ [ k ];
      in
      if a ? ${k} then
        let
          av = a.${k};
          aLeaf = isOptLeaf av;
          bLeaf = isOptLeaf bv;
        in
        if aLeaf && bLeaf then
          av // bv
        else if (!aLeaf) && (!bLeaf) then
          mergeOptionDecls lk av bv
        else
          throw "gen-merge: option `${showOption lk}' is declared both as an option and as an option-group (leaf/group collision)"
      else
        bv
    ) b;

  # setAttrByPath [ a b c ] v = { a.b.c = v; } — reshape a freeform def to its full nested path.
  setAttrByPath =
    path: value: if path == [ ] then value else { ${head path} = setAttrByPath (tail path) value; };

  # ── module classification ────────────────────────────────────────────────
  # A module is "structured" if it carries any structural marker; otherwise it is config-shorthand
  # (the whole attrset is config, minus key/_file metadata). Mirrors nixpkgs unifyModuleSyntax.
  # `_module` is NOT a structural marker — it is always a CONFIG path (`config._module`), so a
  # top-level `{ _module.args.x = y; … }` is still config-shorthand (else the whole module would be
  # dropped), and a top-level `_module` on a structured module is folded into its config.
  markers = [
    "imports"
    "options"
    "config"
    "freeformType"
    "disabledModules"
  ];
  isStructured = m: prelude.any (k: m ? ${k}) markers;
  configOf =
    m:
    let
      base =
        if isStructured m then
          (m.config or { })
        else
          builtins.removeAttrs m [
            "key"
            "_file"
            "_module"
          ];
    in
    if m ? _module then
      base // { _module = recursiveUpdate m._module (base._module or { }); }
    else
      base;
  optionsOf = m: m.options or { };
  importsOf =
    m:
    let
      i = m.imports or [ ];
    in
    if isList i then i else [ i ];
  topFreeformOf = m: m.freeformType or null;

  # ── the merge fold (shared by evalModuleTree options + the collection strategies) ──
  # mergeDefs loc type rawDefs :: combine a list of (possibly property-wrapped) defs into one value.
  #   rawDefs :: [{ file; value }]   (value may carry mkMerge/mkIf/mkOverride)
  # Discharge properties → filterOverrides (min-priority wins) → dispatch: a structural type owns
  # its combine via `.merge`; a leaf (gen-types checker, no `.merge`) merges by mergeOneOption then
  # `verify`. This is the (loc,defs) contract the whole engine — and the escape-hatch consumers
  # (spec §1 item 6) — ride.
  mergeDefs =
    loc: type: rawDefs:
    let
      discharged = concatMap (
        d:
        map (x: {
          inherit (d) file;
          inherit (x) value priority;
        }) (dischargeProperties d.value)
      ) rawDefs;
      winners = filterOverrides discharged;
      typeDefs = map (w: { inherit (w) file value; }) winners;
      result =
        if winners == [ ] then
          throw "gen-merge: option `${showOption loc}' has no definitions after priority resolution"
        else if type != null && type ? merge then
          type.merge loc typeDefs
        else
          mergeLeaf loc winners;
    in
    if type != null && type ? verify then
      (
        let
          e = type.verify result;
        in
        if e == null then
          result
        else
          throw "gen-merge: a definition for option `${showOption loc}' is not of the expected type: ${e}"
      )
    else
      result;

  # Leaf combine — one winner passes through; multiple equal-priority winners must be equal
  # (mergeEqualOption), else a conflict. Byte-mode does not deep-merge unknown leaves.
  mergeLeaf =
    loc: winners:
    if length winners == 1 then
      (head winners).value
    else
      let
        vals = map (w: w.value) winners;
        first = head vals;
      in
      if all (v: v == first) vals then
        first
      else
        throw "gen-merge: the option `${showOption loc}' has conflicting definitions";

  # mergeOneOption — the nixpkgs `lib.mergeOneOption` helper: exactly one definition permitted
  # (else throw). Exported for consumers whose custom `(loc, defs)` merges want unique-def semantics
  # (e.g. gen-schema's ref types).
  mergeOneOption =
    loc: defs:
    if defs == [ ] then
      throw "gen-merge: the option `${showOption loc}' is used but not defined"
    else if length defs != 1 then
      throw "gen-merge: the option `${showOption loc}' is defined multiple times, but may only be defined once"
    else
      (head defs).value;

  # An option merge = mergeDefs + default (as a lowest-priority def) + readOnly + apply.
  mergeOption =
    loc: optDecl: rawDefs:
    let
      _ro =
        if (optDecl.readOnly or false) && length rawDefs > 1 then
          throw "gen-merge: the option `${showOption loc}' is read-only, but it is defined ${toString (length rawDefs)} times"
        else
          null;
      withDefault =
        rawDefs
        ++ optional (optDecl ? default) {
          file = "<default>";
          value = mkOptionDefault optDecl.default;
        };
      merged =
        if rawDefs == [ ] && !(optDecl ? default) then
          throw "gen-merge: the option `${showOption loc}' is used but not defined"
        else
          mergeDefs loc (optDecl.type or null) withDefault;
      applied = if optDecl ? apply then optDecl.apply merged else merged;
    in
    builtins.seq _ro applied;

  # ── evalModuleTree — one call = one `evalModules`, one local fixpoint ──────
  evalModuleTree =
    {
      modules,
      specialArgs ? { },
      check ? true,
      prefix ? [ ],
    }:
    let
      modList = if isList modules then modules else [ modules ];

      # Flatten a module (function / __functor / attrset), applying functions by their STATIC
      # formals only (spec §1 item 4 — never force the dynamic `_module.args` spine), and recurse
      # into `imports` (spec §1 item 5). Returns [{ _file; content }] with imports BEFORE own
      # content (own defs win at equal priority / append last — nixpkgs order).
      collectModules =
        callM: mods:
        concatMap (
          m0:
          let
            m = callM m0;
            self = {
              _file = m0._file or (m._file or "<gen-merge>");
              content = m;
            };
            imported = collectModules callM (importsOf m);
          in
          imported ++ [ self ]
        ) mods;

      # Realize config against the option-decl TREE, one path at a time (nixpkgs mergeModules'):
      # a declared LEAF merges via `mergeOption` (the existing per-option behaviour); a declared
      # GROUP recurses; a config key with NO matching declaration is an UNMATCHED def, bubbled up
      # with its FULL (relative) path so the ROOT freeform can absorb it or the orphan check can
      # throw. nixpkgs is strict PER LEVEL, not only at the root — an undeclared key under an
      # intermediate group throws too (a naive recursion that dropped it would diverge). `loc` is
      # RELATIVE to `prefix`; a leaf's absolute option location is `prefix ++ loc ++ [ k ]`, while
      # unmatched paths stay relative (the root reshapes them against `prefix` via `setAttrByPath`).
      #   rawDefs :: [ { file; value } ]   (value: property-wrapped or a plain sub-attrset)
      mergeTree =
        loc: opts: rawDefs:
        let
          # Push config-node properties down one level (nixpkgs pushes at EACH descent, so a nested
          # `a.b = mkIf c { … }' distributes into `b's keys), yielding plain attrsets per module.
          pushed = map (d: {
            inherit (d) file;
            attrs = pushDownProperties d.value;
          }) rawDefs;
          subDefs =
            k:
            concatMap (
              p:
              optional (p.attrs ? ${k}) {
                inherit (p) file;
                value = p.attrs.${k};
              }
            ) pushed;
          cfgKeys = unique (concatMap (p: attrNames p.attrs) pushed);
          undeclaredKeys = filter (k: !(opts ? ${k})) cfgKeys;

          declaredPairs = map (
            k:
            let
              lk = loc ++ [ k ];
            in
            if isOptLeaf opts.${k} then
              {
                name = k;
                value = mergeOption (prefix ++ lk) opts.${k} (subDefs k);
                unmatched = [ ];
              }
            else
              let
                r = mergeTree lk opts.${k} (subDefs k);
              in
              {
                name = k;
                inherit (r) value unmatched;
              }
          ) (attrNames opts);

          # Undeclared config keys at THIS level → unmatched defs carrying their full path + value.
          ownUnmatched = concatMap (
            k:
            map (p: {
              inherit (p) file;
              path = loc ++ [ k ];
              value = p.attrs.${k};
            }) (filter (p: p.attrs ? ${k}) pushed)
          ) undeclaredKeys;
        in
        {
          value = listToAttrs (map (x: { inherit (x) name value; }) declaredPairs);
          unmatched = ownUnmatched ++ concatMap (x: x.unmatched) declaredPairs;
        };

      result = prelude.fix (
        result:
        let
          baseArgs = specialArgs // {
            inherit (result) config options;
          };

          # Apply a module by its declared formals, sourcing each from baseArgs then the dynamic
          # module-args set. Using `functionArgs` (static) is what breaks the spine cycle.
          callM =
            m:
            if isFunction m then
              let
                formals = functionArgs m;
                extra = mapAttrs (
                  name: _:
                  baseArgs.${name} or result.moduleArgs.${name}
                    or (throw "gen-merge: module argument `${name}' is not defined")
                ) formals;
              in
              m (baseArgs // extra)
            else if isAttrs m && m ? __functor then
              callM (m.__functor m)
            else
              m;

          flat = collectModules callM modList;

          # Option DECLARATIONS merge across modules into a nested TREE (nixpkgs mergeOptionDecls):
          # a second module's `options.a.b.d` recurses beside the first's `options.a.b.c` instead of
          # `//`-clobbering the `a.b` group, and a re-declared leaf still field-unions (later wins —
          # gen-schema's ref-binding `apply`-override modules rely on this). One-level before; a tree
          # now, so `options.a.b.c = mkOption {…}` composes den-shaped configs (`options.den.*`).
          allOptions = foldl' (acc: e: mergeOptionDecls prefix acc (optionsOf e.content)) { } flat;

          # Config attrsets (shorthand-aware), config-root properties pushed to keys.
          pushed = map (e: {
            inherit (e) _file;
            attrs = pushDownProperties (configOf e.content);
          }) flat;

          # The `_module` pseudo-tree: deep-merge every module's `_module`, extract args/freeform.
          moduleTree = foldl' (
            acc: p: if p.attrs ? _module then recursiveUpdate acc p.attrs._module else acc
          ) { } pushed;
          moduleArgs = moduleTree.args or { };

          # freeformType is priority-resolved (nixpkgs treats it as an option): a top-level
          # `freeformType` (bare, prio 100) beats a `_module.freeformType = mkDefault …` (prio 1000)
          # — this is how strict.nix's throw-on-unknown default yields to a kind's own freeform.
          freeform =
            let
              candidates =
                filter (f: f != null) (map (e: topFreeformOf e.content) flat)
                ++ optional (moduleTree ? freeformType) moduleTree.freeformType;
              winners = filterOverrides (concatMap dischargeProperties candidates);
            in
            if winners == [ ] then null else (prelude.last winners).value;

          # Definition order is REVERSE flattened-module order — byte-identical to nixpkgs, which
          # collects defs last-module-first (observable in list-typed options: `[a] [b] [c]` merges
          # to `[c b a]`; verified against `lib.evalModules`). Order-independent for scalars
          # (equal-priority ⇒ conflict) and attrsets (`//`), load-bearing only for lists. One reverse
          # here; the per-level descent preserves it (nixpkgs `reverseList` once, then `zipAttrs`).
          pushedRev = reverse pushed;

          # The realizer's def stream: each module's pushed-down config, REVERSED, minus the
          # `_module` pseudo-key (handled above via `moduleTree`; it is not a real config path).
          topDefs = map (p: {
            file = p._file;
            value = builtins.removeAttrs p.attrs [ "_module" ];
          }) pushedRev;

          # Realize the whole config tree against the option-decl tree. Declared names are present
          # lazily (undefined+no-default throws only on access, matching nixpkgs); groups recurse.
          realized = mergeTree [ ] allOptions topDefs;
          declaredConfig = realized.value;

          # Unknown keys — at ANY depth — route as ONE freeformType def-set at the ROOT (nixpkgs
          # freeform), each reshaped to its full nested path so lazyAttrsOf/attrsOf owns the per-key
          # merge. With no freeform they are orphans → the option does not exist → throw (per level).
          _orphanCheck =
            if check && freeform == null && realized.unmatched != [ ] then
              throw "gen-merge: option `${
                showOption (prefix ++ (head realized.unmatched).path)
              }' does not exist (no freeformType to absorb it)"
            else
              null;
          freeformConfig =
            if freeform == null || realized.unmatched == [ ] then
              { }
            else
              freeform.merge prefix (
                map (u: {
                  inherit (u) file;
                  value = setAttrByPath u.path u.value;
                }) realized.unmatched
              );

          # Declared wins over freeform at shared paths (nixpkgs `recursiveUpdate freeform declared`);
          # for the common disjoint-key case this is just `//`.
          config = builtins.seq _orphanCheck (recursiveUpdate freeformConfig declaredConfig);
        in
        {
          inherit config moduleArgs;
          options = allOptions;
        }
      );
    in
    {
      inherit (result) config options;
      # The tree AS a type — lets a parent tree nest this one (submodule recursion / freeform).
      type = {
        name = "moduleTree";
        merge =
          loc: defs:
          (evalModuleTree {
            inherit specialArgs check;
            prefix = loc;
            modules = modList ++ map (d: setDefaultModuleLocation (d.file or "<def>") d.value) defs;
          }).config;
      };
    };
in
{
  inherit
    evalModuleTree
    mergeDefs
    mergeOption
    mergeOneOption
    showOption
    setDefaultModuleLocation
    ;
}
