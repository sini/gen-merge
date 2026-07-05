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
    length
    head
    tail
    all
    ;
  inherit (priority)
    dischargeProperties
    filterOverrides
    filterOverridesRich
    pushDownProperties
    mkOptionDefault
    defaultPriority
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

  # ── fixed-input core marker (design spec §2.5) ────────────────────────────
  # A def value that CARRIES an already-merged subtree: `mkCoreValue { digest; values; }` tags
  # `values` (the by-contract full-merge output for a whole loc) so a consumer (gen-class tier-2)
  # can hand the engine a pre-computed result and skip the discharge/fold/verify spine for that loc.
  # This is a DIFFERENT insertion point from the README's per-option combine-kernel seam (that swaps
  # byte-vs-confluent HOW defs join; this short-circuits WHETHER they are joined at all). Recognised
  # ONLY when `evalModuleTree` runs with `coreShortCircuit = true` — default-off leaves the marker an
  # ordinary attrset value, so the engine is byte-for-byte unchanged (spec §2.5 opt-in constraint).
  mkCoreValue =
    {
      digest,
      values,
    }:
    {
      __coreValue = true;
      inherit digest values;
    };
  isCoreValue = v: isAttrs v && (v.__coreValue or false) == true;

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

  # ── freeform def coalescing (per originating module instance) ──────────────────────────────────
  # nixpkgs' freeformType option receives a FEW WIDE defs — one per module, each carrying that
  # module's WHOLE unmatched-config subtree — so the `attrsOf`/`lazyAttrsOf` key-union and per-key
  # folds run linear in sibling-key count. The realizer instead bubbles undeclared keys up ONE def
  # PER KEY (`mergeTree`'s `ownUnmatched`), so handing them straight to `freeform.merge` would give it
  # n single-key defs → its `foldl' (//)` key-union and per-key `concatMap` both go O(n²). Coalescing
  # rebuilds the per-module shape (byte-identical output): group the unmatched defs by originating
  # MODULE INSTANCE (a threaded index — NOT `_file`: distinct anonymous modules share the
  # `<gen-merge>` fallback file yet must stay SEPARATE defs for priority resolution), then emit one
  # wide def per module in ASCENDING index order. Ascending index = reverse-module order (topDefs is
  # `pushedRev`), which is the order nixpkgs collects defs in (last module first) — load-bearing for
  # list-typed freeform values, order-independent for scalars/attrsets.
  #
  # Within a module the unmatched paths are DISJOINT, so its subtree is assembled in one pass: depth-1
  # keys (the wide-freeform hot path) build via `listToAttrs` — O(width) — and the deeper keys
  # (undeclared UNDER a declared group) fold via `recursiveUpdate`. That fold is O(deep-entries ×
  # subtree-width) (each `recursiveUpdate` copies its LHS), fine only because deeper freeform is BOTH
  # rare AND narrow on the den surface — a WIDE nested freeform group would want the same listToAttrs
  # treatment, but no consumer needs it. A depth-1 head and a deeper head can never collide within one
  # module (a key undeclared HERE is captured whole and never descended; a deeper key rode a DECLARED
  # group), so the two partitions union cleanly.
  buildModuleUnmatched =
    entries:
    let
      flat = filter (u: length u.path == 1) entries;
      deep = filter (u: length u.path > 1) entries;
      flatAttrs = listToAttrs (
        map (u: {
          name = head u.path;
          inherit (u) value;
        }) flat
      );
      deepAttrs = foldl' (acc: u: recursiveUpdate acc (setAttrByPath u.path u.value)) { } deep;
    in
    recursiveUpdate flatAttrs deepAttrs;

  # Extract each module's entries in ASCENDING index order (= reverse-module order) with a one-shot
  # `filter` per module, then build its subtree once. This is O(moduleCount × |unmatched|), but that
  # factor is over the MODULE COUNT (a small, bounded axis — config layers), NOT the freeform width;
  # `filter` + `listToAttrs` are single builtin passes, so the cost stays LINEAR in width (the axis
  # this fix exists to keep linear). A single-pass `foldl'` group-by is NOT an improvement here: with
  # no O(1) cons/insert, accumulating per-module entry lists (`++`) or subtrees (`//`) copies the
  # growing value each step → O(width²) (measured: 27× CPU / 52× alloc at a 4× width step, the very
  # blow-up this fix removes — hidden from a thunk-count metric because the copies are lazy); a
  # sort-first group-by avoids that but adds an O(U log U) term that tips the linear thunk growth. So
  # the per-module `filter` is deliberate, not a missed optimisation.
  coalesceUnmatched =
    moduleCount: unmatched:
    concatMap (
      i:
      let
        entries = filter (u: u.modIndex == i) unmatched;
      in
      optional (entries != [ ]) {
        file = (head entries).file;
        value = buildModuleUnmatched entries;
      }
    ) (prelude.genList (i: i) moduleCount);

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
  # Public (loc,type,rawDefs) contract — NON-short-circuiting, byte-for-byte the pre-kernel fold, so
  # every existing consumer of the exported `mergeDefs` escape hatch (spec §1 item 6) is unchanged.
  # The opt-in fixed-input path is `mergeDefsWith true`, reached ONLY through the evalModuleTree knob.
  #
  # This is the VALUE-ONLY fold — the hot path the structural strategies (attrsOf/listOf/submodule
  # per-element merges) and the escape hatch ride. It allocates NO provenance: the always-on channel
  # (A2 spec §1) is produced by the SEPARATE `mergeDefsRichWith` below, which the realizer invokes ONLY
  # for the top-level DECLARED options, so a config's thousands of structural sub-merges pay nothing
  # for a channel they never surface. The two folds share `mergeLeaf`; their discharge/priority/verify
  # spines are deliberately kept parallel (the provenance suite's value assertions + the oracle guard
  # against drift), because routing the structural hot path through the rich `{ value; prov }` record
  # measurably regresses the collection workloads (a per-element record thrown away unread).
  #
  #   rawDefs :: [{ file; value }]   (value may carry mkMerge/mkIf/mkOverride)
  # Discharge properties → filterOverrides (min-priority wins) → dispatch: a structural type owns its
  # combine via `.merge`; a leaf (gen-types checker, no `.merge`) merges by mergeLeaf then `verify`.
  # With `coreShortCircuit` it additionally honours the fixed-input core marker (spec §2.5), checked
  # BEFORE discharge:
  #   • SOLE core def at this loc  → return its `values` directly, skipping discharge/fold/verify —
  #     by contract already the full-merge output, so the result is byte-identical where the core is
  #     correct (a WRONG core surfaces here as a divergent value; the gate teeth catch it).
  #   • core def + ANY other def   → conservative fall-through: unwrap each core marker to its
  #     `values` as a plain def and run the normal spine (correctness over the skip). Byte-identical
  #     to a config that had supplied `values` in place of the marker.
  mergeDefs = mergeDefsWith false;
  mergeDefsWith =
    coreShortCircuit: loc: type: rawDefs:
    let
      coreDef = head rawDefs;
      soleCore = coreShortCircuit && length rawDefs == 1 && isCoreValue coreDef.value;
      normalized =
        if coreShortCircuit then
          map (d: if isCoreValue d.value then d // { value = d.value.values; } else d) rawDefs
        else
          rawDefs;
      discharged = concatMap (
        d:
        map (x: {
          inherit (d) file;
          inherit (x) value priority;
        }) (dischargeProperties d.value)
      ) normalized;
      winners = filterOverrides discharged;
      typeDefs = map (w: { inherit (w) file value; }) winners;
      result =
        if winners == [ ] then
          throw "gen-merge: option `${showOption loc}' has no definitions after priority resolution"
        else if type != null && type ? merge then
          type.merge loc typeDefs
        else
          mergeLeaf loc winners;
      checked =
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
    in
    if soleCore then coreDef.value.values else checked;

  # mergeDefsRichWith coreShortCircuit loc type rawDefs :: the RICH sibling — `{ value; prov }`, the
  # value plus the merge's PROVENANCE record (A2 spec §1). Used by the realizer path (`mergeOptionWith`)
  # for DECLARED options only. `value` is computed by the SAME discharge/priority/verify spine as
  # `mergeDefsWith` (kept parallel — see the note above); `prov` SHARES this call's `discharged` +
  # `filterOverridesRich` let-bindings (ONE discharge, ONE priority pass per loc). `prov` is a separate
  # lazy attr: an unforced option pays ~one record thunk (never forced), and forcing `prov` alone never
  # forces the merged VALUE (`defs`/`winners`/`priority`/`defaulted` read only def FILES + discharged
  # priorities — the nixpkgs `definitionsWithLocations` analogue).
  #   • defs      — every contributing def post property-discharge, pre priority pass (a property tag
  #                 keeps its originating file; a false-`mkIf` sub-def has already dropped in discharge).
  #                 Per-def `priority` = its `mkOverride` wrapper's number, else the default override 100.
  #   • winners   — the defs the priority pass kept (the merge's actual inputs).
  #   • priority  — the effective (min) priority the filter selected (`highestPrio`).
  #   • defaulted — the synthetic option `default` (`file = "<default>"`, appended by `mergeOptionWith`)
  #                 is the SOLE surviving winner ⇒ nobody else set the option (the `<default>` def won).
  # coreShortCircuit skip: the record is SYNTHESIZED from the marker (core def as sole def + winner at
  # the bare priority, defaulted=false) so the skip stays a skip — the discharge/fold spine never runs.
  mergeDefsRichWith =
    coreShortCircuit: loc: type: rawDefs:
    let
      coreDef = head rawDefs;
      soleCore = coreShortCircuit && length rawDefs == 1 && isCoreValue coreDef.value;
      normalized =
        if coreShortCircuit then
          map (d: if isCoreValue d.value then d // { value = d.value.values; } else d) rawDefs
        else
          rawDefs;
      discharged = concatMap (
        d:
        map (x: {
          inherit (d) file;
          inherit (x) value priority;
        }) (dischargeProperties d.value)
      ) normalized;
      # Value path uses the plain (allocation-free) filterOverrides — SHARED by the prov record's
      # `winners`. The prov record's `priority` reads `filterOverridesRich`'s `highestPrio` LAZILY (only
      # when `.priority` is forced), so an unforced provenance channel never pays for the rich wrapper.
      winners = filterOverrides discharged;
      typeDefs = map (w: { inherit (w) file value; }) winners;
      result =
        if winners == [ ] then
          throw "gen-merge: option `${showOption loc}' has no definitions after priority resolution"
        else if type != null && type ? merge then
          type.merge loc typeDefs
        else
          mergeLeaf loc winners;
      checked =
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
      prov =
        if soleCore then
          {
            defs = [
              {
                inherit (coreDef) file;
                priority = defaultPriority;
              }
            ];
            winners = [ { inherit (coreDef) file; } ];
            priority = defaultPriority;
            defaulted = false;
          }
        else
          {
            defs = map (d: { inherit (d) file priority; }) discharged;
            winners = map (w: { inherit (w) file; }) winners;
            priority = (filterOverridesRich discharged).highestPrio;
            # The `<default>` sentinel is engine-synthesized (never a real `_file`), so it is a safe
            # marker for "the option default supplied the value".
            defaulted = winners != [ ] && all (w: w.file == "<default>") winners;
          };
    in
    {
      value = if soleCore then coreDef.value.values else checked;
      inherit prov;
    };

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

  # An option merge = mergeDefs + default (as a lowest-priority def) + readOnly + apply. `mergeOption`
  # is the public value-only form; `mergeOptionWith coreShortCircuit` is the RICH realizer form
  # (`{ value; prov }`), threading the opt-in kernel into the fold via `mergeDefsRichWith`. The
  # appended `<default>` def (`file = "<default>"`, priority 1500) is what the fold reads back for the
  # record's `defaulted` flag. NOTE: a present `default =` appends a second def, which demotes a lone
  # core def to fall-through — still byte-identical (the plain `values` beats the mkOptionDefault),
  # only without the spine skip.
  #
  # COMMON CASE (no `apply`, no `readOnly` — the bulk of the surface): the rich record is returned
  # STRAIGHT THROUGH — the realizer's value tree reads `.value`, the provenance tree reads `.prov`, and
  # NO extra attrset is allocated per option (the always-on channel's per-leaf cost stays ~1 record,
  # not a re-wrap). Only `apply`/`readOnly` options take the wrapping branch (they transform the value
  # and/or gate on def count, so they re-wrap; `.prov` rides through unchanged, still lazy behind the
  # same `_ro` gate the value forces).
  mergeOption =
    loc: optDecl: rawDefs:
    (mergeOptionWith false loc optDecl rawDefs).value;
  mergeOptionWith =
    coreShortCircuit: loc: optDecl: rawDefs:
    let
      hasApply = optDecl ? apply;
      readOnly = optDecl.readOnly or false;
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
          mergeDefsRichWith coreShortCircuit loc (optDecl.type or null) withDefault;
    in
    if !hasApply && !readOnly then
      merged
    else
      let
        _ro =
          if readOnly && length rawDefs > 1 then
            throw "gen-merge: the option `${showOption loc}' is read-only, but it is defined ${toString (length rawDefs)} times"
          else
            null;
        applied = if hasApply then optDecl.apply merged.value else merged.value;
      in
      {
        value = builtins.seq _ro applied;
        prov = builtins.seq _ro merged.prov;
      };

  # ── evalModuleTree — one call = one `evalModules`, one local fixpoint ──────
  evalModuleTree =
    {
      modules,
      specialArgs ? { },
      check ? true,
      prefix ? [ ],
      # Opt-in fixed-input kernel (spec §2.5). Default off ⇒ ZERO behaviour change — the core marker
      # is treated as an ordinary attrset. Firing scope: the REALIZER path (declared leaf options at
      # any depth, via `mergeOptionWith`). The flag PROPAGATES through the moduleTree-as-type nested
      # eval (:519 below), so a nested tree fires consistently; only structural-type element merges
      # (attrsOf/listOf per-element folds) do NOT short-circuit — they stay byte-identical, never
      # seeing the flag (a user-supplied type closed over the plain `mergeDefs`). This matches the
      # tier-2 firing contract (core projection locs are declared-option leaves supplied by the core
      # module).
      coreShortCircuit ? false,
    }:
    let
      modList = if isList modules then modules else [ modules ];
      # Rich option merge (`{ value; prov }`) — the realizer reads BOTH the value tree and the
      # provenance tree from one shared discharge/priority pass per declared leaf.
      localMergeOptionRich = mergeOptionWith coreShortCircuit;

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
              # A raw path leaf's provenance IS its path string (nixpkgs-parity error location);
              # guard `isPath` first so we never `._file`-select a non-attrset. Otherwise the module
              # carries its own `_file`, else the imported result's, else the engine fallback.
              _file = if builtins.isPath m0 then toString m0 else (m0._file or (m._file or "<gen-merge>"));
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
          # `modIndex` (the originating module instance, threaded from `topDefs`) rides every def so
          # unmatched keys can be coalesced per module at the root — see `coalesceUnmatched`.
          pushed = map (d: {
            inherit (d) file modIndex;
            attrs = pushDownProperties d.value;
          }) rawDefs;
          subDefs =
            k:
            concatMap (
              p:
              optional (p.attrs ? ${k}) {
                inherit (p) file modIndex;
                value = p.attrs.${k};
              }
            ) pushed;
          # key union via attrset fold — a list `unique` is O(k²) in sibling-key count
          cfgKeys = attrNames (foldl' (acc: p: acc // p.attrs) { } pushed);
          undeclaredKeys = filter (k: !(opts ? ${k})) cfgKeys;

          # Each declared name yields BOTH its merged value and its provenance sub-tree from one
          # descent: a declared LEAF → the rich option merge's `{ value; prov }` (prov = the record);
          # a declared GROUP → the recursive subtree's `{ value; prov }` (prov = the sub-tree). Both
          # trees are assembled at this level by the SAME `listToAttrs` pattern, so provenance mirrors
          # config's loc structure attribute-for-attribute.
          declaredPairs = map (
            k:
            let
              lk = loc ++ [ k ];
            in
            if isOptLeaf opts.${k} then
              let
                m = localMergeOptionRich (prefix ++ lk) opts.${k} (subDefs k);
              in
              {
                name = k;
                inherit (m) value prov;
                unmatched = [ ];
              }
            else
              let
                r = mergeTree lk opts.${k} (subDefs k);
              in
              {
                name = k;
                inherit (r) value prov unmatched;
              }
          ) (attrNames opts);

          # Undeclared config keys at THIS level → unmatched defs carrying their full path + value
          # (+ the originating `modIndex`, for per-module coalescing at the root).
          ownUnmatched = concatMap (
            k:
            map (p: {
              inherit (p) file modIndex;
              path = loc ++ [ k ];
              value = p.attrs.${k};
            }) (filter (p: p.attrs ? ${k}) pushed)
          ) undeclaredKeys;
        in
        {
          value = listToAttrs (map (x: { inherit (x) name value; }) declaredPairs);
          prov = listToAttrs (
            map (x: {
              inherit (x) name;
              value = x.prov;
            }) declaredPairs
          );
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
          # A path leaf (`./foo.nix`) — or a path inside another module's `imports` — is `import`ed
          # then re-entered (nixpkgs imports path modules), so a consumer can load a module tree from
          # `(import-tree ./dir).files`, a BARE PATH LIST. `callM` is already self-recursive, so an
          # imported path yielding a function / `__functor` / attrset is handled uniformly below.
          callM =
            m:
            if builtins.isPath m then
              callM (import m)
            else if isFunction m then
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
          # `_module` pseudo-key (handled above via `moduleTree`; it is not a real config path). The
          # `modIndex` (position in reverse-module order) rides each def so the root freeform can
          # coalesce unmatched keys back into one wide def per originating module.
          topDefs = prelude.imap0 (i: p: {
            file = p._file;
            modIndex = i;
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
          # Coalesce the per-key unmatched defs into one wide def per originating module BEFORE
          # `freeform.merge` (see `coalesceUnmatched`) — restores nixpkgs' per-module freeform shape,
          # so `attrsOf`/`lazyAttrsOf` stays linear in sibling-key count (byte-identical output).
          freeformConfig =
            if freeform == null || realized.unmatched == [ ] then
              { }
            else
              freeform.merge prefix (coalesceUnmatched (length topDefs) realized.unmatched);

          # Declared wins over freeform at shared paths (nixpkgs `recursiveUpdate freeform declared`);
          # for the common disjoint-key case this is just `//`.
          config = builtins.seq _orphanCheck (recursiveUpdate freeformConfig declaredConfig);

          # ── provenance (A2 spec §1) ────────────────────────────────────────────────────────────
          # A lazy tree mirroring `config`'s loc structure. Per DECLARED-option loc the rich record
          # `realized.prov` carries (from mergeTree); per FREEFORM loc a REDUCED record built here
          # from `realized.unmatched`. `defs` = the files of the unmatched defs at that loc
          # (winners/priority/defaulted = null — "freeform / not observable", never "no override
          # present"). It reuses `realized.unmatched` — one per-key def per originating module, each
          # carrying its `file`, the SAME structures the value-side freeform coalescing consumes; it
          # does NOT re-walk modules and does NOT force config VALUES (reads only `file`/`path`). It
          # may be OVER-INCLUSIVE: a false-`mkIf`-wrapped freeform def still shows here (the freeform
          # pass, like nixpkgs, discharges per key only inside its own `.merge`, which provenance does
          # not enter). Records are grouped by their (joined) loc then reshaped to the nested attrset
          # via `setAttrByPath` — a depth-1 undeclared key and a deeper one can never collide (a key
          # undeclared HERE is captured whole and never descended; cf. `buildModuleUnmatched`).
          freeformProv =
            let
              byPath = foldl' (
                acc: u:
                let
                  key = showOption u.path;
                in
                acc
                // {
                  ${key} = {
                    inherit (u) path;
                    files = (acc.${key}.files or [ ]) ++ [ { inherit (u) file; } ];
                  };
                }
              ) { } realized.unmatched;
            in
            foldl' (
              acc: k:
              recursiveUpdate acc (
                setAttrByPath byPath.${k}.path {
                  defs = byPath.${k}.files;
                  winners = null;
                  priority = null;
                  defaulted = null;
                }
              )
            ) { } (attrNames byPath);

          # Declared provenance wins over freeform at shared paths (mirrors config's
          # `recursiveUpdate freeform declared`): a declared GROUP's sub-records overlay the freeform
          # records that bubbled through it; a declared LEAF record is never shadowed (a declared key
          # is never also unmatched).
          provenance = recursiveUpdate freeformProv realized.prov;
        in
        {
          inherit config moduleArgs provenance;
          options = allOptions;
        }
      );
    in
    {
      inherit (result) config options provenance;
      # The tree AS a type — lets a parent tree nest this one (submodule recursion / freeform).
      type = {
        name = "moduleTree";
        merge =
          loc: defs:
          (evalModuleTree {
            inherit specialArgs check coreShortCircuit;
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
    mkCoreValue
    # Classification/collection predicates shared with the portable-subset lint (lib/lint.nix) so the
    # lint's view of "declared leaf vs group / config-shorthand / imports / decl-tree merge" cannot
    # DRIFT from the engine's. The export list is EXACTLY what the lint consumes. Additive — the
    # public `lib/default.nix` surface is unchanged.
    isOptLeaf
    configOf
    importsOf
    mergeOptionDecls
    ;
}
