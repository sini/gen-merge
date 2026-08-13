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

  # An option-decl LEAF is a `mkOption` descriptor (tagged `_type = "option"` by `lib/types.nix` `mkOption`).
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

  # Merge two TYPES through the `functor`/`typeMerge` protocol the library already ships
  # (lib/types.nix), guarded on both halves. nixpkgs assumes every type it meets carries the full
  # protocol; gen-merge meets types that do not — a gen-types PARAMETRIC leaf (`enum`, `struct`,
  # `union`) reaches the unified namespace as a bare constructor and is never protocol-completed, so
  # it carries no `functor`. A missing half answers "not mergeable" rather than aborting on a missing
  # attribute. This is the ONE binding both strata that ask the question consult — the ELEMENT
  # stratum (a container's `binOp`, lib/types.nix `elemTypeFunctor`) and the DECLARATION stratum
  # (`redeclareDecl` below) — so the two cannot drift into answering it differently.
  #
  # A NON-MOUNTABLE operand answers "not mergeable" BEFORE the protocol halves are read, and this
  # ordering is load-bearing rather than defensive. The tree-as-a-type (`evalModuleTree`'s `.type`,
  # below) now carries `typeMerge`/`functor` as NAMED REFUSALS — reading either says "this is not an
  # option type" — but "do these two types merge?" is a question with a true answer here, and it is
  # `null`: they do not. Returning the value keeps the declaration stratum's own refusal, which names
  # BOTH types and every declaring file, in place of a refusal that would name only the tree.
  mergeTypes =
    a: b:
    if (a ? nonMountable) || (b ? nonMountable) then
      null
    else if a ? typeMerge && b ? functor then
      a.typeMerge b.functor
    else
      null;

  # The declaring SITES at one option loc, in authored module order — the entries whose own
  # `options` tree carries `loc` as a LEAF, each keeping the `idx` it had in the module fold. The
  # index is what lets a shadow record name the module that actually contributed the field being
  # shadowed rather than the n-th declarer of the option. A direct path lookup per module —
  # O(modules × depth), never a tree walk — which is what makes it affordable both on the refusal
  # path and behind the shadow record, each of which reads it lazily.
  declaringSitesAt =
    entries: loc:
    let
      declaresLeaf =
        opts: path:
        if path == [ ] then
          isOptLeaf opts
        else
          isAttrs opts
          && !(isOptLeaf opts)
          && opts ? ${head path}
          && declaresLeaf opts.${head path} (tail path);
    in
    filter (e: declaresLeaf e.options loc) entries;

  # redeclareDecl — the ENGINE's answer when one option loc is declared by two modules.
  #
  # A DECLARATION MERGE CONSULTS THE TYPE ALGEBRA THE LIBRARY ALREADY SHIPS. When both declarations
  # carry a `type`, the merged declaration's type is `mergeTypes`' answer about the pair; `null` —
  # "not mergeable" — is a NAMED REFUSAL carrying the option path and the declaring files. This is
  # the one place on the declaration path that did not consult the protocol, and the measured cost
  # was a record disagreeing with itself: one declaration's descriptor surviving beside the OTHER's
  # type, no error and no warning. Routing here is why that is no longer expressible — the only way
  # a merged declaration acquires a type is through a merge that must return one. The predicate is
  # not invented here: it ships as the advisory lint kind `type-merge` (lib/lint.nix), whose own
  # finding text is a standing admission that the library knew the answer and declined to give it.
  #
  # THE NON-TYPE FIELDS STAY RIGHT-BIASED, and the ground is ADR-0029: positional authority is the
  # substrate's, and this fold is an ORDERED fold over the authored module order — a later
  # declaration is a later contribution, not a stronger one. gen-schema's ref-binding modules are the
  # deliberate consumer: a module layering `apply` onto an earlier typed leaf carries no `type` of
  # its own, so it never reaches the algebra above.
  #
  # AN ORDERED BIAS IS A RULE ONLY WHILE THE LOSER STAYS REACHABLE. Bracha & Cook 1990 keep the
  # overridden parent behind `super`; Leijen 2005's scoped labels retain a shadowed field "both in
  # the value and in the type", against free extension where "the previous value is overwritten,
  # after which it is no longer accessible". So a merge that actually shadows a field records what
  # it shadowed, oldest first, under `overridden` — the declaration stratum's provenance, beside the
  # definition stratum's on the result.
  #
  # BOUNDARY, stated because the rule does not reach it: a field whose value is REFLECTED INTO AN
  # IDENTITY is not made safe here. Those sit under ADR-0016's option-set-closure precondition, and
  # enforcing it belongs to the minting spec, not to this engine. What this guarantees is narrower:
  # the merged record's TYPE is the algebra's answer about both declarations, never one of them
  # picked in silence.
  redeclareDecl =
    sitesAt: modIndex: lk: av: bv:
    let
      merged = av // bv;
      # PRESENCE, never value equality: deciding "did B restate this field" by comparison would
      # force declaration values nothing has asked for. `_type` is the metadata every option record
      # carries — identical by construction, so never a shadow.
      shadowed = filter (k: k != "_type" && bv ? ${k}) (attrNames av);
      sites = sitesAt lk;
      # `av` is an ACCUMULATION of every earlier module that declared `lk`, and `file` names the one
      # that most recently contributed to it — the last declaring site before this merge. It is NOT
      # "the file that declared every field in the record": a module that only ADDS a field shadows
      # nothing and records no entry, yet its contribution is what a later module goes on to shadow,
      # and that entry must name IT rather than whoever declared the option first. Indexing the site
      # list by how many entries have accumulated says otherwise and is wrong for exactly that shape
      # — shadow events and declaring modules are different counts. `<unknown-file>` where there is
      # no earlier site (a decl tree assembled outside the module fold): a sentinel in the shape of
      # `<default>`/`<def>`, never a guess.
      earlier = filter (s: s.idx < modIndex) sites;
      overridden = (av.overridden or [ ]) ++ [
        {
          file = if earlier == [ ] then "<unknown-file>" else (prelude.last earlier).file;
          declaration = builtins.removeAttrs av [ "overridden" ];
        }
      ];
      # `overridden` appears ONLY where a declaration really was shadowed: a layering module that
      # merely ADDS fields leaves the record exactly what the plain union produced.
      kept = if shadowed == [ ] then merged else merged // { inherit overridden; };
    in
    if (av ? type) && (bv ? type) then
      let
        mergedType = mergeTypes av.type bv.type;
      in
      if mergedType == null then
        throw "gen-merge: option `${showOption lk}' is declared with types that do not merge (`${av.type.name}' and `${bv.type.name}'); declared in ${
          concatStringsSep ", " (map (s: s.file) sites)
        }"
      else
        kept // { type = mergedType; }
    else
      kept;

  # mergeOptionDecls — combine two option-decl TREES (nixpkgs mergeModules' descent, byte-mode).
  # This is what lets `options.a.b.c = mkOption {…}` build a NESTED tree rather than the old
  # single-level view:
  #   leaf ∪ leaf  = `onRedeclare` — see below;
  #   group ∪ group = RECURSE (a second module's `options.a.b.d` merges beside `options.a.b.c`);
  #   leaf ⁄ group at the same path = a hard collision (nixpkgs likewise refuses to make an option
  #                  the parent of sub-options) — must throw, never silently `//`-merge.
  # `onRedeclare lk av bv` is a REQUIRED formal, not a defaulted hook: the tree walk knows the shape
  # of a redeclaration and nothing about what it means, and the two callers genuinely disagree. The
  # engine passes `redeclareDecl`; the portable-subset lint passes the plain field-union, because a
  # lint that ABORTED on the redeclaration it exists to report could never report it. Making the
  # caller state it keeps that divergence one legible argument rather than a fork of the descent.
  # DELIBERATE divergence: nixpkgs' `optionTreeToOption` has one sugar case —
  # raw options merged INTO a `submodule`-typed leaf — that byte-mode does not reproduce (out of the
  # den surface; submodule nesting rides the separate `submodule`/`attrsOf` `.merge` path). Byte-mode
  # conservatively throws here rather than risk emitting wrong bytes.
  mergeOptionDecls =
    onRedeclare: loc: a: b:
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
          onRedeclare lk av bv
        else if (!aLeaf) && (!bLeaf) then
          mergeOptionDecls onRedeclare lk av bv
        else
          throw "gen-merge: option `${showOption lk}' is declared both as an option and as an option-group (leaf/group collision)"
      else
        bv
    ) b;

  # setAttrByPath [ a b c ] v = { a.b.c = v; } — reshape a freeform def to its full nested path.
  setAttrByPath =
    path: value: if path == [ ] then value else { ${head path} = setAttrByPath (tail path) value; };

  # ── list/path helpers for the warm re-eval path (design spec §§1-3) ─────────
  # `drop n` / `take n` (gen-prelude ships neither) — index-based, no `++` accumulation.
  drop =
    n: xs:
    let
      l = length xs;
    in
    prelude.genList (i: prelude.elemAt xs (n + i)) (if l > n then l - n else 0);
  take =
    n: xs:
    let
      l = length xs;
      m = if n < l then n else l;
    in
    prelude.genList (i: prelude.elemAt xs i) (if m > 0 then m else 0);
  # getAttrByPath [ a b c ] s = s.a.b.c — LAZY attrpath selection (never forces the selected value;
  # the warm splice reuses prev's memoized leaf thunk, forced only on demand — spec §2).
  getAttrByPath = path: attrs: foldl' (acc: k: acc.${k}) attrs path;

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
            # Defensive: `callM` consumes the `pureModule` wrapper before its content is recorded, so
            # the marker never reaches config keys — strip it belt-and-braces so a hand-built shorthand
            # carrying the key cannot leak it into config.
            "__pureModule"
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

  # ── source-class classifier (design spec §0.3 / §3) ────────────────────────
  # Tag a module with the CLASS of its PRE-application source. The class is decided on `m0` (before
  # `callM`), because `callM` applies function and `__functor` modules with the WHOLE
  # `specialArgs // extra` set — nixpkgs application semantics, which byte-mode keeps — so any function
  # module can reach `config` regardless of its visible formals, and the post-application content is
  # always a plain attrset that no longer reveals whether config was reachable.
  #
  # Consequently `builtins.functionArgs` CANNOT prove a function module clean: `args@{ genSchema, ... }:
  # args.config` reports only `genSchema` yet the `@`-binding captures the full argument set, and a bare
  # lambda (`args: args.config`) reports `{ }` — either reads `config` despite its visible formals. So a
  # function module is DIRTY BY DEFAULT; `pureModule` is the author's explicit clean assertion (§5).
  #   • attrset (no `__functor`, no `__pureModule`)  → "attrset"   — no body, cannot read anything.
  #   • path                                          → import it, classify the RESULT.
  #   • `__pureModule`-marked wrapper                 → "marked-pure" — tags THIS entry only; the
  #                                                     module's own `imports` classify independently.
  #   • everything else (functions, bare lambdas,     → "dirty".
  #     `__functor` attrsets without the marker)
  classifyModule =
    m0:
    if builtins.isPath m0 then
      classifyModule (import m0)
    else if isAttrs m0 then
      if m0 ? __pureModule then
        "marked-pure"
      else if m0 ? __functor then
        "dirty"
      else
        "attrset"
    else
      "dirty";

  # pureModule (design spec §3 / §5) — the author's clean-module assertion. Wraps a function module in
  # the marker attrset `classifyModule` reads BEFORE `callM` applies it (`callM` applies `__functor`
  # attrsets, so a bare function's cleanliness would be invisible post-application). Contract (§5): the
  # wrapped function reads ONLY its declared formals and EVERY formal resolves from `specialArgs` — the
  # engine TRUSTS the marker. HAZARD (non-local): a formal is unsafe if another module can shadow its
  # NAME into `_module.args`, making it fixpoint-derived rather than specialArgs-sourced — a lying marker
  # then reuses stale values silently (README §pureModule spells out the blast radius). The tag
  # classifies this wrapper's own content entry marked-pure; entries reached through the module's
  # `imports` classify independently.
  pureModule = f: {
    __pureModule = true;
    __functor = self: f;
  };

  # ── module collection (import-expanding), shared by the fixpoint + the warm edited-tail count ──────
  # Flatten a module (function / __functor / attrset / path), applying it via the caller's `callM`, and
  # recurse into `imports` (spec §1 item 5). Returns [{ _file; content; srcClass }] with imports BEFORE
  # own content (own defs win at equal priority / append last — nixpkgs order). `srcClass` is decided on
  # the PRE-application `m0` (design spec §3) and stays LAZY (the cold path never forces it). Hoisted to
  # module scope so `evalModuleTree` can flatten `editedModules` with the SAME machinery it flattens the
  # full list with — the warm path derives the EDITED tail-count from `length (collectModules callM
  # editedModules)`, never trusting a caller-supplied count (imports expansion is config-dependent).
  collectModules =
    callM: mods:
    concatMap (
      m0:
      let
        m = callM m0;
        self = {
          # A raw path leaf's provenance IS its path string (nixpkgs-parity error location); guard
          # `isPath` first so we never `._file`-select a non-attrset. Otherwise the module carries its
          # own `_file`, else the imported result's, else the engine fallback.
          _file = if builtins.isPath m0 then toString m0 else (m0._file or (m._file or "<gen-merge>"));
          content = m;
          srcClass = classifyModule m0;
        };
        imported = collectModules callM (importsOf m);
      in
      imported ++ [ self ]
    ) mods;

  # ── warm re-eval decision layer (design spec §§1-2) ─────────────────────────
  # The opt-in warm path reuses the previous eval's declared-leaf values/provenance for locs PROVABLY
  # untouched by an edit (an appended module list) and re-merges the rest inside the normal fixpoint.
  # `warmDecide` is the PURE decision half (no splicing): given the flattened module list + the EDITED
  # tail-count + the merged decl tree, it computes the dirty footprint (which declared leaves an edit
  # can perturb), the coarse freeform-reuse flag, and the disabledModules refusal. `mergeTree` consumes
  # `footprintPaths` to gate per-leaf splicing (spec §2). Testable in isolation through the core seam.

  # Declared LEAVES of ONE option-decl tree — walk to `isOptLeaf` (typed registries / scalar leaves
  # included; untyped groups recurse), each loc beside the DESCRIPTOR declared there. One descent
  # with two views: `declLeafPaths` below is its loc projection (the granularity of both the
  # footprint and the splice gate), and the deprecation report reads the same entries' descriptors.
  # Two descents would be two answers to "which locs are declared leaves" that can drift apart —
  # the same reason the portable-subset lint consumes the engine's own predicates rather than its
  # own copies. Only the SPINE is walked: an entry's `opt` is the descriptor thunk, unforced here.
  declLeafEntries =
    tree:
    let
      go =
        loc: t:
        concatMap (
          k:
          let
            v = t.${k};
            lk = loc ++ [ k ];
          in
          if isOptLeaf v then
            [
              {
                path = lk;
                opt = v;
              }
            ]
          else if isAttrs v then
            go lk v
          else
            [ ]
        ) (attrNames t);
    in
    go [ ] tree;

  # Declared-leaf locs of ONE option-decl tree — the loc projection of the walk above.
  declLeafPaths = tree: map (e: e.path) (declLeafEntries tree);

  # DEF footprint of one module's config, guided by the merged decl tree — the lint's discharge-based
  # descent (lib/lint.nix `descend`), but recording PATHS, not order-probes: it pushes config-node
  # properties down at each DECLARED-GROUP level and STOPS at a declared leaf (records `onDecl = true`)
  # or an undeclared key (records `onDecl = false` — a freeform contribution). It NEVER forces a leaf
  # value — only the config SPINE (keys), bounded by the module's structural size (spec §2: acceptable,
  # a dirty/edited module re-merges anyway). A def landing on a declared GROUP that is not an attrset
  # (a type error the cold path would throw on) is conservatively recorded as `onDecl` rather than
  # descended, so the footprint stays total.
  moduleDefFootprint =
    allOptions: content:
    let
      descend =
        opts: loc: attrs:
        concatMap (
          k:
          let
            lk = loc ++ [ k ];
            v = attrs.${k};
          in
          if (opts ? ${k}) && !(isOptLeaf opts.${k}) then
            let
              pv = pushDownProperties v;
            in
            if isAttrs pv then
              descend opts.${k} lk pv
            else
              [
                {
                  onDecl = true;
                  path = lk;
                }
              ]
          else if opts ? ${k} then
            [
              {
                onDecl = true;
                path = lk;
              }
            ]
          else
            [
              {
                onDecl = false;
                path = lk;
              }
            ]
        ) (attrNames attrs);
      rootAttrs = builtins.removeAttrs (pushDownProperties (configOf content)) [ "_module" ];
    in
    descend allOptions [ ] rootAttrs;

  # `warmDecide { flat; editedCount; allOptions }` — the reusability predicate as a footprint pass.
  #   • EDITED  = the tail-`editedCount` entries of `flat` (collectModules is concatMap + flatten
  #               distributes over ++, and the appended list is a strict suffix, so tail-k = the
  #               flattened edited entries — an EDITED attrset module is still edited, its defs re-merge).
  #   • CLEAN   = non-edited entries whose `srcClass` is attrset / marked-pure (config-independent).
  #   • DIRTY   = every other non-edited entry (`srcClass == "dirty"`).
  # The DIRTY FOOTPRINT = the union, over DIRTY ∪ EDITED entries, of decl paths (`declLeafPaths` of the
  # entry's own `options`) and def paths landing on declared leaves (`moduleDefFootprint`). A declared
  # leaf is REUSABLE iff it is OUTSIDE this set (spec §2 — outside it, both the decl set and the def set
  # at the loc come only from CLEAN modules, so the merge inputs are identical to the previous eval).
  # FREEFORM is coarse (soundness-forced, spec §2): reuse the whole prev freeform layer iff (a) NO
  # dirty/edited entry contributes an unmatched (freeform) def path AND (b) NO edited entry contributes
  # a freeformType candidate at EITHER site (top-level `freeformType` or `_module.freeformType`) — an
  # edited freeformType flips the priority-resolved winner and changes EVERY freeform loc while naming
  # none of them. disabledModules on any edited entry ⇒ refuse warm (it would disable a clean base
  # module invisibly to the footprint — the same failure shape). Each footprint record keeps a `reason`
  # for the decision trace (spec §4).
  warmDecide =
    {
      flat,
      editedCount,
      allOptions,
    }:
    let
      n = length flat;
      headLen = if n > editedCount then n - editedCount else 0;
      editedEntries = drop headLen flat;
      nonEdited = take headLen flat;
      isCleanEntry = e: e.srcClass == "attrset" || e.srcClass == "marked-pure";
      cleanEntries = filter isCleanEntry nonEdited;
      dirtyEntries = filter (e: !(isCleanEntry e)) nonEdited;

      # One entry's footprint + freeform contributions, reason-tagged (`reasonOf kind` — "decl"/"def").
      footOf =
        reasonOf: e:
        let
          declPaths = map (p: {
            path = p;
            reason = reasonOf "decl";
          }) (declLeafPaths (optionsOf e.content));
          df = moduleDefFootprint allOptions e.content;
          defPaths = concatMap (
            r:
            if r.onDecl then
              [
                {
                  inherit (r) path;
                  reason = reasonOf "def";
                }
              ]
            else
              [ ]
          ) df;
          free = concatMap (
            r:
            if r.onDecl then
              [ ]
            else
              [
                {
                  inherit (r) path;
                  reason = "freeform-dirty ${e._file}";
                }
              ]
          ) df;
        in
        {
          footprint = declPaths ++ defPaths;
          inherit free;
        };

      dirtyF = map (
        e: footOf (kind: if kind == "decl" then "dirty-decl ${e._file}" else "dirty-def ${e._file}") e
      ) dirtyEntries;
      editedF = map (e: footOf (_kind: "edited-def") e) editedEntries;
      allF = dirtyF ++ editedF;
      footprint = concatMap (x: x.footprint) allF;
      footprintPaths = map (r: r.path) footprint;
      freeContribs = concatMap (x: x.free) allF;

      editedFreeformType = prelude.any (
        e: (topFreeformOf e.content != null) || ((configOf e.content)._module.freeformType or null != null)
      ) editedEntries;
      reuseAllFreeform = freeContribs == [ ] && !editedFreeformType;
      disabledRefusal = prelude.any (e: e.content ? disabledModules) editedEntries;
    in
    {
      inherit
        footprint
        footprintPaths
        freeContribs
        reuseAllFreeform
        disabledRefusal
        ;
      modules = {
        clean = map (e: e._file) cleanEntries;
        dirty = map (e: e._file) dirtyEntries;
        edited = map (e: e._file) editedEntries;
      };
    };

  # nixpkgs' EMPTY-DEFINITION rule (modules.nix `mergeDefinitions`: `else if type.emptyValue ? value
  # then type.emptyValue.value`). With no surviving definition the type gets to supply a value before
  # this is an error, and only a type declaring none is an error. A container is empty-able —
  # `attrsOf`/`lazyAttrsOf`/`submodule` → `{ }`, `listOf` → `[ ]`, `nullOr` → `null` — while every leaf
  # (and `raw`/`anything`/`deferredModule`/`either`) declares no `emptyValue.value` and still throws.
  #
  # Two distinct ways to arrive with nothing, both of which nixpkgs answers here: an option that was
  # never defined at all, and an option every one of whose definitions was discharged away — `mkIf
  # false` as the sole def. `emptyValue` is what separates "a container nobody added to", which is
  # legitimately empty, from "a value nobody supplied", which is a mistake.
  emptyValueOr =
    type: err:
    if type != null && (type.emptyValue or { }) ? value then type.emptyValue.value else throw err;
  # Whether `emptyValueOr` would yield rather than throw — lets the realizer decline to short-circuit an
  # undefined option so the ONE empty-value site stays inside the fold.
  hasEmptyValue = type: type != null && (type.emptyValue or { }) ? value;

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
          emptyValueOr type "gen-merge: option `${showOption loc}' has no definitions after priority resolution"
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
  # lazy attr: an unforced option pays ~one record thunk (never forced).
  # FORCING CONTRACT: reading ANY field of the record (`defs`/`winners`/`priority`/`defaulted`) forces
  # this loc's contributing defs to WHNF — the record reads `discharged`, and `dischargeProperties`
  # branches on `isAttrs`, so a bare-`throw` def fires even on a plain `.defs` read (the SAME discharge
  # the value path runs to resolve priorities). What it does NOT force is the merged VALUE: the
  # structural `.merge` / leaf `verify` / `apply` live on the value path (`checked`), never reached by a
  # prov read. So provenance forces WHO-defined-what to WHNF, never the resolved value. (Weaker than
  # nixpkgs `definitionsWithLocations`, which forces nothing — byte-mode discharges eagerly for priority.)
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
          emptyValueOr type "gen-merge: option `${showOption loc}' has no definitions after priority resolution"
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
        # An empty-able type is NOT an error when undefined — fall through to the fold, whose
        # `winners == [ ]` arm is the single place `emptyValue` is consulted (nixpkgs answers both
        # arrivals at one site too). Only a type with no `emptyValue.value` short-circuits to the throw.
        if rawDefs == [ ] && !(optDecl ? default) && !(hasEmptyValue (optDecl.type or null)) then
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
      # ── opt-in warm re-eval (design spec §§1-4) ────────────────────────────────────────────────
      # `warmFrom` = the PREVIOUS `evalModuleTree` result (its `config`/`provenance`/`freeformConfig`/
      # `freeformProv` ARE the memo — no new table); `editedModules` = the appended module LIST (the
      # engine flattens it internally, deriving the EDITED tail-count itself). Default null/[ ] ⇒ ZERO
      # behaviour change (the `coreShortCircuit` precedent): the decision is never forced, `mergeTree`
      # takes the cold branch, freeform re-merges cold. Warm SPLICES declared-leaf values/provenance
      # for locs OUTSIDE the dirty footprint (§2), re-merging the rest in the normal fixpoint; a leaf's
      # spliced value IS prev's memoized thunk (byte-identical by the predicate). Fires only here (the
      # top eval); the nested moduleTree-as-type merge stays COLD (a boundary, like provenance's).
      warmFrom ? null,
      editedModules ? [ ],
    }:
    let
      modList = if isList modules then modules else [ modules ];
      # Rich option merge (`{ value; prov }`) — the realizer reads BOTH the value tree and the
      # provenance tree from one shared discharge/priority pass per declared leaf.
      localMergeOptionRich = mergeOptionWith coreShortCircuit;

      # Realize config against the option-decl TREE, one path at a time (nixpkgs mergeModules'):
      # a declared LEAF merges via `mergeOption` (the existing per-option behaviour); a declared
      # GROUP recurses; a config key with NO matching declaration is an UNMATCHED def, bubbled up
      # with its FULL (relative) path so the ROOT freeform can absorb it or the orphan check can
      # throw. nixpkgs is strict PER LEVEL, not only at the root — an undeclared key under an
      # intermediate group throws too (a naive recursion that dropped it would diverge). `loc` is
      # RELATIVE to `prefix`; a leaf's absolute option location is `prefix ++ loc ++ [ k ]`, while
      # unmatched paths stay relative (the root reshapes them against `prefix` via `setAttrByPath`).
      #   rawDefs :: [ { file; value } ]   (value: property-wrapped or a plain sub-attrset)
      # Signature is `warm: loc: opts: rawDefs` — `warm` is the FIRST positional (threaded unchanged
      # through the descent), described last here only because it is the warm-path add-on.
      # `warm` = the warm-splice context `{ active; footprintPaths; prevConfig; prevProv }` (or
      # `{ active = false; }`), threaded through the descent. At a declared LEAF whose ABSOLUTE loc is
      # OUTSIDE `footprintPaths`, warm SPLICES `getAttrByPath` of prev's `config`/`provenance` — lazy
      # attrpath selection, never forcing the reused thunk (spec §2). SPLICE AT LEAVES ONLY: `prev.config`
      # is `recursiveUpdate freeform declared`, so a whole untyped-GROUP splice would capture stale
      # freeform descendants when the freeform plane re-merges; at an `isOptLeaf` loc the prev value is
      # declared-only (freeform never wins a declared leaf), so leaf-granularity splicing is sound —
      # untyped declared groups recurse and splice THEIR leaves.
      mergeTree =
        warm: loc: opts: rawDefs:
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
              abs = prefix ++ lk;
            in
            if isOptLeaf opts.${k} then
              if warm.active && !(prelude.elem abs warm.footprintPaths) then
                # REUSABLE — outside the dirty footprint: splice prev's leaf value + provenance record
                # (the same memoized thunks). `getAttrByPath` is lazy: an unforced prev leaf stays
                # unforced, a forced one is free. Byte-identical to the cold merge by the §2 predicate
                # (both the decl set and the def set at this loc come only from CLEAN modules).
                {
                  name = k;
                  value = getAttrByPath abs warm.prevConfig;
                  prov = getAttrByPath abs warm.prevProv;
                  unmatched = [ ];
                }
              else
                let
                  m = localMergeOptionRich abs opts.${k} (subDefs k);
                in
                {
                  name = k;
                  inherit (m) value prov;
                  unmatched = [ ];
                }
            else
              let
                r = mergeTree warm lk opts.${k} (subDefs k);
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
            inherit (result) options;
            # Modules see the `_module`-bearing view so `config._module.args` resolves (nixpkgs
            # parity); the returned `result.config` stays `_module`-free.
            config = result.moduleConfig;
            inherit prefix;
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
          # `//`-clobbering the `a.b` group. A RE-DECLARED leaf goes to `redeclareDecl` — the type
          # algebra answers, the non-type fields keep their ordered bias, and what the bias shadowed
          # stays reachable. gen-schema's ref-binding `apply`-override modules carry no `type` of
          # their own, so the algebra never reaches them. One-level before; a tree now, so
          # `options.a.b.c = mkOption {…}` composes den-shaped configs (`options.den.*`).
          #
          # `declEntries` carries the provenance the tree walk itself cannot see: each module's own
          # options root beside the file that declared it and its POSITION in the fold. It is read
          # only through `sitesAt` — on a refusal, or when a shadow record's `file` is read — so the
          # happy path never touches it. The position is what a shadow record needs to name its
          # contributor; the fold therefore hands each step its own index rather than one shared
          # rule. The locs the walk hands over are PREFIXED (the fold's `loc` IS `prefix`) while
          # these trees are not, hence the `drop`.
          declEntries = prelude.imap0 (i: e: {
            idx = i;
            file = e._file;
            options = optionsOf e.content;
          }) flat;
          sitesAt = lk: declaringSitesAt declEntries (drop (length prefix) lk);
          allOptions = foldl' (
            acc: e: mergeOptionDecls (redeclareDecl sitesAt e.idx) prefix acc e.options
          ) { } declEntries;

          # ── warm decision + splice context (design spec §§1-2) ─────────────────────────────────
          # EDITED tail-count from the engine's OWN flatten of `editedModules` (imports expansion is
          # config-dependent, so a caller count is untrusted). `decision` is LAZY — the eval PATH is
          # zero-cost when the knob is off: the cold path (`warmFrom == null`) never forces `decision`
          # (`warmActive` short-circuits on the null check), so no classification/footprint runs. (An
          # explicit read of `.warmDecision.modules` on a cold result DOES force classification — the
          # trace is data on demand, consistent with the `reused`/`remerged` cost note below.) Warm is
          # REFUSED (cold fallback) when an edited entry carries `disabledModules` (§2 guard).
          editedCount = if editedModules == [ ] then 0 else length (collectModules callM editedModules);
          decision = warmDecide { inherit flat editedCount allOptions; };
          warmActive = warmFrom != null && !decision.disabledRefusal;
          warmCtx =
            if warmActive then
              {
                active = true;
                inherit (decision) footprintPaths;
                prevConfig = warmFrom.config;
                prevProv = warmFrom.provenance;
              }
            else
              { active = false; };
          # Reuse the WHOLE prev freeform layer iff the coarse flag holds (§2, soundness-forced: a
          # single edited freeformType flips every freeform loc). Else re-merge cold. Byte-identical
          # either way when the flag holds; the flag exists to keep the SKIP sound.
          reuseFreeform = warmActive && decision.reuseAllFreeform;

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
          realized = mergeTree warmCtx [ ] allOptions topDefs;
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
          # An unmatched def has THREE dispositions and no fourth: a `freeformType` absorbs it (below),
          # `check` refuses it (above), or — with neither — it is not merged into `config` at all. The
          # third is the one that returns neither a value nor a named refusal, and it is why this channel
          # exists — but the report is NOT scoped to it. Every unmatched def the freeform plane did not
          # absorb is REPORTED here, the refused ones included: the report's extension is exactly
          # `_orphanCheck`'s, so under `check = true` the same defs are listed while `config` throws.
          # Always on a result sibling, never inside `config`: `check = false`'s whole purpose is that the
          # merged value does NOT grow the key, and a report living there would change what the flag
          # produces instead of describing it.
          #
          # `check` does not gate the report — whether the engine tells the truth about what it consumed
          # is not a checking question — while the freeform plane does, because there the defs ARE
          # merged and nothing was dropped.
          #
          # By construction, not a new tracking layer: this is `realized.unmatched` (the same records
          # `coalesceUnmatched` and `freeformProvCold` read) minus its `value`s. Names and originating
          # files are already carried; the VALUES are deliberately dropped, so reading the report forces
          # no def. Inheriting that list inherits its reach: like `freeformProvCold`'s records the report
          # may be OVER-INCLUSIVE — a false-`mkIf`-wrapped def still shows here, because properties are
          # discharged per key only inside `freeform.merge`, which this pass does not enter. That is the
          # report↔refusal correspondence holding rather than leaking: the same def under `check = true`
          # is refused, and a discharge filter here would desynchronise the two.
          #
          # Paths are absolute against `prefix`, like the refusal message above, and are CAPTURE
          # paths — the first undeclared name on each branch (`mergeTree`'s `ownUnmatched`). An
          # undeclared key is captured with its whole subtree, since with no declaration nothing says
          # where the option path ends and an attrset VALUE begins; a path here therefore means "this
          # loc and everything beneath it was not merged".
          undeclared =
            if freeform == null then
              map (u: {
                path = prefix ++ u.path;
                inherit (u) file;
              }) realized.unmatched
            else
              [ ];
          # Coalesce the per-key unmatched defs into one wide def per originating module BEFORE
          # `freeform.merge` (see `coalesceUnmatched`) — restores nixpkgs' per-module freeform shape,
          # so `attrsOf`/`lazyAttrsOf` stays linear in sibling-key count (byte-identical output).
          freeformConfigCold =
            if freeform == null || realized.unmatched == [ ] then
              { }
            else
              freeform.merge prefix (coalesceUnmatched (length topDefs) realized.unmatched);
          # Warm: reuse prev's whole freeform layer (byte-identical when `reuseFreeform`), skipping the
          # `freeform.merge` re-run; else the cold layer. The cold thunk stays unforced under reuse.
          freeformConfig = if reuseFreeform then warmFrom.freeformConfig else freeformConfigCold;

          # Declared wins over freeform at shared paths (nixpkgs `recursiveUpdate freeform declared`);
          # for the common disjoint-key case this is just `//`.
          #
          # The RETURNED/embedded `config` stays `_module`-free, exactly like nixpkgs — its
          # `(evalModules).config` strips `_module`, so the parity oracle and every consumer that reads
          # the merged value never sees it.
          config = builtins.seq _orphanCheck (recursiveUpdate freeformConfig declaredConfig);

          # The MODULE-VISIBLE config (`baseArgs.config`, ~:888) re-surfaces `_module.args` as a
          # readable path, matching nixpkgs (inside a module `config._module.args` resolves; the
          # returned config drops it). Consumers read the WHOLE map to enumerate args dynamically:
          # gen-schema's `mkInstanceType` sets `config._module.args.${kind} = config` and den's
          # `resolvedCtxModule` reads `config._module.args` to build the entity resolution context (it
          # can't enumerate `...` function args). ONLY `.args` (not the `_module.freeformType` gen-merge
          # consumes internally), and ONLY when a module set an arg — else `config` is used unchanged.
          moduleConfig = if moduleArgs == { } then config else config // { _module.args = moduleArgs; };

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
          freeformProvCold =
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
          # Warm: the freeform provenance layer rides the same reuse decision as its config layer.
          freeformProv = if reuseFreeform then warmFrom.freeformProv else freeformProvCold;

          # Declared provenance wins over freeform at shared paths (mirrors config's
          # `recursiveUpdate freeform declared`): a declared GROUP's sub-records overlay the freeform
          # records that bubbled through it; a declared LEAF record is never shadowed (a declared key
          # is never also unmatched).
          provenance = recursiveUpdate freeformProv realized.prov;

          # ── deprecated declared types ──────────────────────────────────────────────────────────
          # `deprecationMessage` is one of the 14 protocol fields lib/types.nix stamps onto every
          # completed type, and it was the one field this engine STORED and never read. A stored
          # field nobody consults is not a neutral placeholder: it makes a protocol-conformance
          # check that asserts PRESENCE pass while the BEHAVIOUR the field exists for is absent, so
          # a deprecated type declared here was indistinguishable from an undeprecated one. The
          # reference engine's answer is `warnDeprecation` (nixpkgs lib/modules.nix), which reports
          # the type's NAME, the option LOC and the DECLARING FILES; those are the four data this
          # record carries, from the same source field.
          #
          # ON THE RESULT, NOT ON STDERR, and that is a mechanism decision rather than a taste one:
          # Nix's eval cache swallows `trace`/`warn` output, so a printed deprecation is present on
          # the first eval and gone on every later one — a report that disappears when the answer is
          # reused reports nothing. A field on the result is the shape that needs no new vocabulary
          # and that a consumer cannot silently drop.
          #
          # THE GROUND IS PRESENCE-VS-BEHAVIOUR, DELIBERATELY NOT "a foreign mount needs it": whether
          # a gen type ever enters a nixpkgs options tree is a separate, contested question (see
          # lib/default.nix), and this report is legible either way — it is gen-merge telling the
          # truth about gen-merge's OWN declarations.
          #
          # SERIALISABLE BY CONSTRUCTION — `type` is the type's NAME, never the type VALUE. A report
          # is something a consumer prints, diffs or hands on; a type value carries functions, so a
          # record holding one could not survive `toJSON` at all.
          #
          # SCOPE, one eval: the declared leaves of THIS tree. A `submodule`'s inner options are
          # declared in a NESTED `evalModuleTree` that runs INSIDE the type's `merge`, and `merge`
          # returns the merged VALUE — byte-compat pins that shape, so the nested eval has no way to
          # hand its report back alongside the value it was called for. That is what makes one eval
          # the scope here; it is NOT that the nested view is unreachable. A consumer that wants it
          # re-derives it at the DECLARATION stratum, which the protocol already exposes: the type's
          # `getSubModules` are the sub-modules and `getSubOptions` is the nested decl tree, so
          # `evalModuleTree { modules = ty.getSubModules; }` yields the nested records without
          # touching `merge` at all. Worth knowing before reaching for it: those re-derived records
          # report `declarations = [ "<gen-merge>" ]`, because sub-modules carry no `_file` — which
          # is a reason for the parent not to fold that view into its own report rather than a
          # reason it cannot. Stamping the field is this engine's obligation; composing the strata
          # belongs to whoever composes the results (the same boundary `provenance` and the warm
          # path state for nested evals).
          #
          # LAZINESS: reading this forces each declared leaf's TYPE — that is where the field lives —
          # and no DEFINITION value; leaving it unread costs nothing. `declarations` is a per-record
          # thunk over the existing `sitesAt`, so the common case (no deprecated type) never looks a
          # declaring site up.
          deprecations =
            let
              record =
                e:
                let
                  ty = e.opt.type or null;
                  loc = prefix ++ e.path;
                in
                {
                  path = loc;
                  # `or null` on both: an option may carry no `type` at all (gen-schema's ref-binding
                  # `apply`-override modules), and a type that never reached protocol completion (a
                  # bare parametric gen-types constructor) carries no `deprecationMessage` — neither
                  # is deprecated, and neither may abort the report.
                  type = ty.name or null;
                  message = ty.deprecationMessage or null;
                  declarations = map (s: s.file) (sitesAt loc);
                };
            in
            filter (d: d.message != null) (map record (declLeafEntries allOptions));

          # ── decision trace (design spec §4) — the memoization DECISION, always-on data on the warm
          # path (the eval computes the partition anyway). Consumed by gen-flake's `override` (formatted
          # into its `trace`). Laziness contract: `mode`/`modules` are cheap (classification only);
          # `reused`/`remerged` are O(declared-locs) SPINE-forcing when read (they enumerate the loc
          # partition — never leaf values). Cold (`warmFrom == null` or a disabledModules refusal) ⇒
          # nothing spliced ⇒ `reused = [ ]`, `remerged = { }`, with the cold `reason` stated.
          warmDecision =
            let
              reusableLeaves = filter (l: !(prelude.elem l decision.footprintPaths)) (declLeafPaths allOptions);
              remergedList = decision.footprint ++ (if reuseFreeform then [ ] else decision.freeContribs);
              remerged = foldl' (
                acc: r:
                acc
                // {
                  ${showOption r.path} = acc.${showOption r.path} or r.reason;
                }
              ) { } remergedList;
            in
            {
              mode = if warmActive then "warm" else "cold";
              reason =
                if warmFrom == null then
                  "no warmFrom (cold)"
                else if decision.disabledRefusal then
                  "disabledModules on an edited module (warm refused)"
                else
                  null;
              reused = if warmActive then map showOption reusableLeaves else [ ];
              remerged = if warmActive then remerged else { };
              inherit (decision) modules;
            };
        in
        {
          inherit
            config
            moduleConfig
            moduleArgs
            provenance
            undeclared
            deprecations
            freeformConfig
            freeformProv
            warmDecision
            ;
          options = allOptions;
        }
      );
    in
    {
      inherit (result)
        config
        options
        provenance
        # The unmatched definitions this eval did not merge into `config`, the REFUSED ones included —
        # `check` does not gate it (see above) — empty whenever a freeformType absorbed them, and empty
        # for a fully-declared config.
        undeclared
        # The declared options of this eval whose TYPE carries a `deprecationMessage`, each with the
        # message, the type's name and the files that declared the option — empty when no declared
        # type is deprecated, which is the ordinary case.
        deprecations
        # Freeform layers exposed as internal memo fields (public surface = the five above):
        # a CHAINED warm re-eval reuses `warmFrom.freeformConfig`/`freeformProv` directly (spec §2).
        freeformConfig
        freeformProv
        # The memoization decision trace (spec §4); `mode = "cold"` on a plain compose (no warmFrom).
        warmDecision
        ;
      # The tree AS a type — lets a parent tree nest this one (submodule recursion / freeform). Nested
      # evals are always COLD (no `warmFrom` threaded) — a documented boundary, like provenance's.
      #
      # ── NON-MOUNTABLE, AND IT SAYS SO ────────────────────────────────────────────────────────────
      # This is a NESTING SEAM, not an `optionType`. It answers two of the fourteen protocol fields,
      # and they are the two that make a value LOOK like an option type — a name and a merge is what
      # a reader checks by eye. They are NOT the fields a foreign engine reads first: measured, the
      # first protocol field a real `lib.evalModules` forces is `getSubModules` (`fixupOptionType`),
      # and neither `name` nor `merge` is forced before the abort. So the shape invites a mount it
      # cannot serve: handed to a real `lib.evalModules` it used to die inside the CONSUMER on a
      # missing attribute — an interpreter error naming a nixpkgs line, uncatchable by the caller.
      #
      # Completing the protocol is the wrong repair. The boundary is the EVAL, not the repo
      # (ADR-0014), and what crosses a gen boundary is plain data (ADR-0023) — a mounted option type
      # is neither, so completion would build the bridge the law removes. Every unimplemented field
      # therefore RETURNS A NAMED REFUSAL rather than an interpreter error, and the mount is refused
      # at the consumer's first real read of the protocol instead of aborting inside it. Making the
      # tree mountable for real is CROSSING work, and it belongs on that chain, not here; nothing is
      # deleted meanwhile, because the nesting seam below is a shipped capability.
      #
      # Each of the twelve unanswered fields is DISPOSED OF EXPLICITLY — a missing attribute is a
      # decision no one wrote down, and it is what made the abort unnamed:
      #
      #   * THREE ARE ANSWERED TRUTHFULLY, and their answers are the ones this engine's own readers
      #     already derive from absence (`or null` / `or { }`), so nothing internal changes: a tree
      #     is not deprecated, it supplies no value when a nesting option goes undefined, and it
      #     wraps no element TYPE. Supplying them opens no mount: they are answers, not capabilities.
      #     `deprecationMessage` additionally closes the consumer's one remaining DIRECT (non-`or`)
      #     read of this type — the read that would abort UNCATCHABLY rather than refuse. The refusal
      #     does not depend on it: with the field removed the mount still refuses catchably, because
      #     the field forced first is `getSubModules`, which is read through `or`.
      #   * EIGHT REFUSE BY NAME. None is read by this engine on a declared leaf's type, so the
      #     refusals are reachable only from outside; `typeMerge`/`functor` are additionally fenced
      #     at `mergeTypes` above, which owes a value.
      #   * `_type` IS DELIBERATELY ABSENT, and it is the one field a refusal would make worse. A
      #     consumer that ASKS (`lib.isType "option-type"`) reads it through `or null` and gets a
      #     correct `false` today; a throwing tombstone would turn the one working negative answer
      #     into an abort. Absence is the answer here, and `nonMountable` is what states it.
      type =
        let
          # The refusal names the field the caller reached for, so the message identifies WHICH
          # protocol read was refused rather than only that something was.
          refuse =
            field:
            throw "gen-merge: `moduleTree' is not an option type and does not answer `${field}'; it is this engine's own nesting seam, and mounting it in a foreign module system is a crossing this library does not open (ADR-0014: the boundary is the eval; ADR-0023: what crosses is plain data)";
        in
        {
          name = "moduleTree";
          merge =
            loc: defs:
            (evalModuleTree {
              inherit specialArgs check coreShortCircuit;
              prefix = loc;
              modules = modList ++ map (d: setDefaultModuleLocation (d.file or "<def>") d.value) defs;
            }).config;

          # THE MARK. Presence is the predicate — testing it forces nothing — and the value carries
          # the reason, so a consumer that finds it needs no other document to know what to do.
          nonMountable = "`moduleTree' is gen-merge's own nesting seam, not an option type: it answers `name' and `merge', and refuses the rest of the option-type protocol by name. Mounting a tree in a foreign module system is crossing work (ADR-0014, ADR-0023), not a gap in this type";

          # Answered, and true of a tree.
          deprecationMessage = null;
          emptyValue = { };
          nestedTypes = { };

          # Refused, by name.
          check = refuse "check";
          description = refuse "description";
          descriptionClass = refuse "descriptionClass";
          functor = refuse "functor";
          getSubModules = refuse "getSubModules";
          getSubOptions = refuse "getSubOptions";
          substSubModules = refuse "substSubModules";
          typeMerge = refuse "typeMerge";
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
    # `pureModule` (design spec §3 / §5) — the author's clean-module assertion; wraps a function module
    # in the `{ __pureModule = true; __functor = …; }` shape `classifyModule` reads pre-application.
    pureModule
    # Classification/collection predicates shared with the portable-subset lint (lib/lint.nix) so the
    # lint's view of "declared leaf vs group / config-shorthand / imports / decl-tree merge" cannot
    # DRIFT from the engine's. The export list is EXACTLY what the lint consumes. Additive — the
    # public `lib/default.nix` surface is unchanged.
    isOptLeaf
    configOf
    importsOf
    mergeOptionDecls
    # The guarded pair-merge of two TYPES. It lives here rather than in lib/types.nix because the
    # DECLARATION stratum asks the same question as the ELEMENT stratum, and one binding is what
    # keeps their answers identical; lib/types.nix consumes it back through this seam.
    mergeTypes
    # `classifyModule` (design spec §3) — the source-class predicate threaded onto every collected
    # entry as `srcClass`; shared with the warm re-eval path and the classify suite.
    classifyModule
    # Warm re-eval decision layer (design spec §§1-2) — `collectModules` (the import-expanding flatten,
    # hoisted so `editedModules` flattens with the same machinery) + the pure `warmDecide` predicate and
    # its footprint helpers. On the internal core seam only; the splice EXECUTION rides `evalModuleTree`.
    collectModules
    warmDecide
    declLeafPaths
    moduleDefFootprint
    ;
}
