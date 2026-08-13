# Portable-subset lint — flag modules that use constructs OUTSIDE gen-merge's byte-mode surface.
#
# gen-merge reproduces `lib.evalModules` OUTPUT byte-for-byte only over the primitive den's surface
# reduces to (README "The 7-item merge primitive" + "The priority subset"). A module reaching for a
# construct the byte-mode engine deliberately does NOT implement will diverge silently or throw. This
# lint makes the claim "this module runs on gen-merge and `lib.evalModules` byte-identically"
# mechanically verifiable: it statically flags the known boundaries.
#
#   1. order-pass          — a def carrying an `_type = "order"` marker (`mkOrder`/`mkBefore`/`mkAfter`).
#                            nixpkgs sorts order-defs by `priority` before merge; gen-merge's priority
#                            subset drops that pass (README "The priority subset"), so the marker is
#                            carried as an ordinary value and silently mis-orders.
#   2. options-introspection — a module FUNCTION whose formals include `options`. Byte-mode `.options`
#                            is a minimal descriptor map (the merged decl tree), not the reference
#                            `options` structure (no per-node `_type`/`loc`/`declarations`).
#   3. type-merge          — the same option loc DECLARED (with a `type`) in more than one module.
#                            On the TYPE the two engines agree: both route the pair through
#                            `type.typeMerge` (a functor over two `optionType`s) and refuse when it
#                            answers null. They part on the OTHER fields — nixpkgs refuses the
#                            redeclaration outright when both declarations carry any of
#                            `default`/`example`/`description`/`apply` (its `bothHave` guard, which
#                            fires ahead of the functor), where gen-merge right-biases them under a
#                            stated rule. The flag is therefore an OVER-APPROXIMATION: it fires on
#                            every typed redeclaration, and only the field-colliding ones diverge.
#   4. function-to         — an option `type` named `functionTo`, intentionally omitted from the type
#                            surface (7-item primitive item 7 — guard functions are carried as data).
#   +. unverifiable        — a `type` record too deeply nested to walk within the fixed fuel. A
#                            portability lint must FAIL toward reject, never silently accept an
#                            undecidable input, so exhaustion is surfaced (not swallowed).
#
# ── the forcing contract (a static walk that inherits the ENGINE's forcing profile) ──────────────
# The lint reuses the engine's own classification + property machinery (lib/modules.nix predicates +
# lib/priority.nix `dischargeProperties`/`pushDownProperties`), so it forces EXACTLY what the engine
# forces and no more — it is TOTAL on portable inputs. Concretely:
#   • order-pass is decided by descending the merged option-decl tree like the realizer (`mergeTree`):
#     properties are pushed down per level and defs are DISCHARGED at declared leaves, so an
#     `mkIf false { … }` branch drops (its content is NEVER forced) and a data leaf's payload is only
#     forced to WHNF (the `_type` probe), never deep-walked — the engine's exact profile. The walk
#     STOPS at declared leaves: an order marker buried inside a structural-typed leaf value
#     (attrsOf/listOf/submodule element defs) rides that strategy's own `mergeDefs` and is out of the
#     static scope. Two further out-of-surface order-marker shapes are likewise NOT flagged (both
#     zero-use on the den surface, named here so the boundary is airtight): (1) an order marker AT a
#     declared-GROUP node (`grp = mkBefore { … }` where `grp` is a group, not a leaf) —
#     `pushDownProperties` does not distribute an `order` marker, so the descent treats its
#     `_type`/`priority`/`content` as child keys and never probes it as a marker; (2) an order marker
#     nested MORE than one level under a freeform/undeclared key (`free = { sub = mkAfter […]; }`) —
#     the undeclared def is discharged and only its TOP value probed for `_type = "order"`, so a
#     marker a level deeper is unseen. Option DEFAULTS are NOT force-inspected (the engine realizes a
#     default lazily, on access; a `default = throw "must set"` must stay portable) — order-pass is
#     decided on config DEFS only.
#   • the lint NEVER applies a module function (a body's options/config/imports need the `config`
#     fixpoint, which it must not force — may throw, and catching throws is disallowed in pure eval;
#     cf. the engine binding modules by static formals only, spec §1 item 4). So a FUNCTION module is
#     opaque except for its formals ⇒ only construct 2 is decidable on it; 1/3/4 are decided on attrset
#     modules, `import`ed path leaves, and the attrset modules reached through `imports`. Attrset
#     modules cannot reference `config` (no formals), so their `mkIf` conditions are static — the lint
#     discharging them is sound.
#   • a submodule's `getSubModules` is a SEPARATE nested eval — its inner modules are not walked (lint
#     them by passing them to `lint` directly). `type` records are read (`.name`/`nestedTypes`), never
#     applied. functionTo's value-side variant (a bare function at a data leaf) needs the config→option
#     matching the fixpoint provides, so it is detected via the type NAME only.
# A finding is `{ kind; loc; file; detail }` (`file` = the def/decl provenance; a LIST of files for
# `type-merge`); `lint` returns the full list (empty ⇒ portable).
{
  prelude,
  priority,
  core,
}:
let
  inherit (prelude)
    isAttrs
    isList
    isFunction
    functionArgs
    concatMap
    map
    filter
    attrNames
    attrValues
    foldl'
    concatStringsSep
    optional
    length
    any
    ;
  inherit (priority) dischargeProperties pushDownProperties;
  inherit (core)
    isOptLeaf
    configOf
    importsOf
    mergeOptionDecls
    ;

  showLoc = concatStringsSep ".";
  mkFinding = kind: loc: file: detail: {
    inherit
      kind
      loc
      file
      detail
      ;
  };
  isOrderMarker = v: isAttrs v && (v._type or null) == "order";

  # ── module collection (import-expanding, function-OPAQUE), _file tracked as core.collectModules ──
  # Path leaves are `import`ed (pure); an attrset module contributes its `imports` recursively; a
  # function (or `__functor`) module is an OPAQUE leaf. `file` mirrors modules.nix:321 exactly (a path's
  # provenance IS its path string, else the module's `_file`, else the engine fallback).
  collect =
    mods:
    concatMap (
      m0:
      let
        m = if builtins.isPath m0 then import m0 else m0;
        file = if builtins.isPath m0 then toString m0 else (m0._file or (m._file or "<gen-merge>"));
      in
      if isFunction m then
        [
          {
            fn = true;
            module = m;
            inherit file;
          }
        ]
      else if isAttrs m then
        if m ? __functor then
          [
            {
              fn = true;
              module = m;
              inherit file;
            }
          ]
        else
          [
            {
              fn = false;
              module = m;
              inherit file;
            }
          ]
          ++ collect (importsOf m)
      else
        [ ]
    ) mods;

  # ── option-decl leaves of one module (loc + descriptor), via the engine's `isOptLeaf` ──
  optionLeaves =
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
                loc = lk;
                leaf = v;
              }
            ]
          else if isAttrs v then
            go lk v
          else
            [ ]
        ) (attrNames t);
    in
    go [ ] tree;

  # ── construct 4: a `type` record that (recursively) names `functionTo` ─────
  # Reads only structural fields (`name`, the `nestedTypes` introspection alias the strategies carry —
  # lib/types.nix; the redundant bare `elemType` is a duplicate of `nestedTypes.elemType`, so it is not
  # re-walked). Fuel-bounded; exhaustion (a type deeper than `typeWalkDepth`) is REPORTED, not swallowed
  # (a portability lint must not silently accept an undecidable type). Returns `{ hit; exhausted }`.
  typeWalkDepth = 32;
  subTypes = t: attrValues (t.nestedTypes or { });
  scanType =
    fuel: t:
    if !(isAttrs t) then
      {
        hit = false;
        exhausted = false;
      }
    else if (t.name or null) == "functionTo" then
      {
        hit = true;
        exhausted = false;
      }
    else if fuel <= 0 then
      {
        hit = false;
        exhausted = true;
      }
    else
      let
        subs = map (scanType (fuel - 1)) (subTypes t);
      in
      {
        hit = any (r: r.hit) subs;
        exhausted = any (r: r.exhausted) subs;
      };

  lint =
    { modules }:
    let
      modList = if isList modules then modules else [ modules ];
      collected = collect modList;
      attrsetEntries = filter (e: !e.fn) collected;

      # ── construct 2: a function module whose formals include `options` ──
      optionsArgFindings =
        e:
        if e.fn && isFunction e.module && ((functionArgs e.module) ? options) then
          [
            (mkFinding "options-introspection" [ ] e.file
              "a module function takes an `options` formal; the byte-mode `.options` is a minimal descriptor map, not the reference-engine `options` structure"
            )
          ]
        else
          [ ];

      # ── construct 4 (+ unverifiable): per-module option-type findings ──
      typeFindings =
        e:
        concatMap (
          l:
          if l.leaf ? type then
            let
              r = scanType typeWalkDepth l.leaf.type;
            in
            if r.hit then
              [
                (mkFinding "function-to" l.loc e.file
                  "option type names `functionTo`, which is intentionally omitted from the byte-mode type surface"
                )
              ]
            else if r.exhausted then
              [
                (mkFinding "unverifiable" l.loc e.file
                  "option type nests deeper than the lint's type-walk fuel (${toString typeWalkDepth}); cannot decide `functionTo` — treated as non-portable rather than silently accepted"
                )
              ]
            else
              [ ]
          else
            [ ]
        ) (optionLeaves (e.module.options or { }));

      # ── construct 1: order markers in CONFIG defs, guided by the merged decl tree (mergeTree-style) ──
      # The engine's own declaration merge — the same descent, the same leaf/group collision throw —
      # with the ONE argument the engine and the lint genuinely disagree on: what a REDECLARED leaf
      # means. The engine consults the type algebra and refuses when it answers "not mergeable"; here
      # it is the plain field-union, because a lint that ABORTED on the redeclaration it exists to
      # report (`type-merge`, below) could never report it. The divergence is deliberate, it is this
      # argument, and everything else about the two views stays shared.
      allOptions = foldl' (
        acc: e:
        mergeOptionDecls (
          _lk: av: bv:
          av // bv
        ) [ ] acc (e.module.options or { })
      ) { } attrsetEntries;
      # config defs, one per attrset module, pushed once at the root; `_module` is the engine's pseudo-
      # tree (modules.nix:470 strips it from the realizer), never an order-bearing config path.
      rootPushed = map (e: {
        inherit (e) file;
        attrs = builtins.removeAttrs (pushDownProperties (configOf e.module)) [ "_module" ];
      }) attrsetEntries;
      descend =
        opts: loc: pushed:
        let
          keys = attrNames (foldl' (acc: p: acc // (if isAttrs p.attrs then p.attrs else { })) { } pushed);
          childDefs =
            k:
            concatMap (
              p:
              optional (p.attrs ? ${k}) {
                inherit (p) file;
                value = p.attrs.${k};
              }
            ) pushed;
        in
        concatMap (
          k:
          let
            lk = loc ++ [ k ];
            defs = childDefs k;
          in
          if (opts ? ${k}) && !(isOptLeaf opts.${k}) then
            # declared GROUP → push each child value down one level, recurse
            descend opts.${k} lk (
              map (d: {
                inherit (d) file;
                attrs = pushDownProperties d.value;
              }) defs
            )
          else
            # declared LEAF or UNDECLARED (freeform/orphan) → discharge each def (WHNF, condition-aware),
            # flag a def whose discharged values include an order marker. Never descends past here.
            concatMap (
              d:
              if any isOrderMarker (map (x: x.value) (dischargeProperties d.value)) then
                [
                  (mkFinding "order-pass" lk d.file
                    "def carries an order marker (`mkOrder`/`mkBefore`/`mkAfter`, `_type = \"order\"`); the order pass is outside the byte-mode surface"
                  )
                ]
              else
                [ ]
            ) defs
        ) keys;
      orderFindings = descend allOptions [ ] rootPushed;

      # ── construct 3: an option loc declared with a `type` in >1 module — attrset-fold group, files kept ──
      typedLeaves = concatMap (
        e:
        map (l: {
          inherit (l) loc;
          inherit (e) file;
        }) (filter (l: l.leaf ? type) (optionLeaves (e.module.options or { })))
      ) attrsetEntries;
      byLoc = foldl' (
        acc: x:
        let
          key = showLoc x.loc;
          prev =
            acc.${key} or {
              inherit (x) loc;
              files = [ ];
            };
        in
        acc
        // {
          ${key} = {
            inherit (prev) loc;
            files = prev.files ++ [ x.file ];
          };
        }
      ) { } typedLeaves;
      typeMergeFindings = concatMap (
        v:
        optional (length v.files >= 2) (
          mkFinding "type-merge" v.loc v.files
            "option `${showLoc v.loc}' is declared with a type in more than one module; on the TYPE the engines agree (both combine the declarations through a `typeMerge' functor and refuse when it answers null), but the reference engine ALSO refuses the redeclaration outright when both declarations carry any of `default'/`example'/`description'/`apply' (its `bothHave' guard, ahead of the functor), where gen-merge right-biases those fields — so a field-colliding pair is accepted here and rejected there"
        )
      ) (attrValues byLoc);

      perModule = concatMap (
        e: (optionsArgFindings e) ++ (if e.fn then [ ] else typeFindings e)
      ) collected;
    in
    perModule ++ orderFindings ++ typeMergeFindings;
in
{
  inherit lint;
}
