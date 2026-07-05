# Portable-subset lint — flag modules that use constructs OUTSIDE gen-merge's byte-mode surface.
#
# gen-merge reproduces `lib.evalModules` OUTPUT byte-for-byte only over the primitive den's surface
# reduces to (README "The 7-item merge primitive" + "The priority subset"). A module that reaches for
# a construct the byte-mode engine deliberately does NOT implement will either diverge silently or
# throw. This lint makes the claim "this module runs on gen-merge and `lib.evalModules` byte-identically"
# mechanically verifiable: it statically flags the four known boundaries.
#
#   1. order pass          — defs tagged `_type = "order"` (`mkOrder`/`mkBefore`/`mkAfter`). nixpkgs
#                            sorts order-defs by `priority` before the merge; gen-merge's priority
#                            subset drops that whole pass (README "The priority subset"), so an order
#                            marker is carried as an ordinary value and silently mis-orders.
#   2. options-introspection — a module FUNCTION whose declared formals include `options`. The
#                            byte-mode `.options` is a minimal descriptor map (the merged option-decl
#                            tree), NOT the nixpkgs `options` structure (no `_type`/`loc`/`declarations`
#                            per node), so a module introspecting `options` may observe a different shape.
#   3. typeMerge reliance  — the same option loc DECLARED (with a `type`) in more than one module.
#                            nixpkgs combines the two declarations through `type.typeMerge` (a functor
#                            over two `optionType`s); gen-merge's `mergeOptionDecls` field-unions the
#                            descriptors (later wins), never invoking a typeMerge functor — divergent
#                            whenever the two types are not the same.
#   4. functionTo          — an option `type` named `functionTo`. `functionTo` is intentionally omitted
#                            from the byte-mode type surface (README §7 — consumers wrap guard functions
#                            as data); a `functionTo` leaf has no gen-merge strategy.
#
# ── the honest detection boundary (a STATIC walk) ────────────────────────────────────────────────
# The lint inspects module VALUES without evaluating them: it walks attrset modules' `options`/`config`
# trees, reads option `type` records, and reads module-function FORMALS via `builtins.functionArgs`. It
# does NOT apply module functions — a module function's body (its options/config/imports) is invisible
# until applied against the `config` fixpoint, which the lint must not force (it may throw, and catching
# throws is not permitted in pure eval; cf. the engine binding modules by static formals only, spec §1
# item 4). Consequences, by construct:
#   • a FUNCTION module is opaque except for its formals ⇒ only construct 2 (options-arg) is decidable
#     on it; constructs 1/3/4 inside a function body are NOT seen.
#   • constructs 1/3/4 are decided on ATTRSET modules (and `import`ed path leaves, and the attrset
#     modules reached through `imports`).
#   • a submodule's `getSubModules` is a SEPARATE nested eval — its inner modules are not walked here
#     (lint them by passing them to `lint` directly). Option `type` records are treated as leaves whose
#     `.name`/`nestedTypes`/`elemType` are read for the functionTo check, never applied/merged.
#   • functionTo's value-side variant (a bare function supplied at a data leaf) needs the config→option
#     matching the fixpoint provides, so it is detected via the type NAME only, not the def value.
# A finding is a `{ kind; loc; detail }` attrset; `lint` returns the full list (empty ⇒ portable).
{ prelude }:
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
    concatStringsSep
    optional
    length
    any
    unique
    ;

  showLoc = concatStringsSep ".";
  mkFinding = kind: loc: detail: { inherit kind loc detail; };

  # ── module collection (import-expanding, function-OPAQUE) ──────────────────
  # Flatten the module list the way the engine's `collectModules` sees it, but WITHOUT applying any
  # module function (the static-walk boundary above). Path leaves are `import`ed (pure); an attrset
  # module contributes its `imports` recursively; a function (or `__functor`) module is an OPAQUE leaf.
  # Each entry is tagged `fn` so the analyzers know the detection boundary at that node.
  importsOf =
    m:
    let
      i = m.imports or [ ];
    in
    if isList i then i else [ i ];
  collect =
    mods:
    concatMap (
      m0:
      let
        m = if builtins.isPath m0 then import m0 else m0;
      in
      if isFunction m then
        [
          {
            fn = true;
            module = m;
          }
        ]
      else if isAttrs m then
        # A `__functor` attrset is applied like a function ⇒ opaque leaf (formals unreadable cheaply).
        if m ? __functor then
          [
            {
              fn = true;
              module = m;
            }
          ]
        else
          [
            {
              fn = false;
              module = m;
            }
          ]
          ++ collect (importsOf m)
      else
        [ ]
    ) mods;

  # ── option-decl tree walk ──────────────────────────────────────────────────
  # An option-decl LEAF is a descriptor tagged `_type = "option"` (lib/types.nix `mkOption`); anything
  # else inside the tree is a GROUP (a plain attrset of sub-declarations) — mirrors core's `isOptLeaf`.
  isOptLeaf = v: isAttrs v && (v._type or null) == "option";
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
  # Reads only structural fields (`name`, and the `nestedTypes`/`elemType` introspection aliases the
  # gen-merge strategies carry, lib/types.nix); never applies `.merge`/`.check`. Fuel-bounded against a
  # pathologically self-referential type record.
  subTypes = t: (attrValues (t.nestedTypes or { })) ++ optional (t ? elemType) t.elemType;
  namesFunctionTo =
    fuel: t:
    fuel > 0
    && isAttrs t
    && ((t.name or null) == "functionTo" || any (namesFunctionTo (fuel - 1)) (subTypes t));

  # ── construct 1: an `_type = "order"` marker anywhere in a def value ───────
  # Walks a config (or option-default) def value for order markers. Descends the priority-property
  # wrappers (`merge`/`if`/`override`) at the SAME loc (they do not change an option's location), and
  # plain attrset config subtrees by key; any OTHER `_type` (e.g. an opaque den `__configThunk`, or an
  # unexpected `option`) is treated as opaque and NOT descended (never forced further). NB this forces
  # the def value to WHNF at each node — a deliberately poisoned lazy config is outside the lint's domain.
  orderWalk =
    loc: v:
    if !(isAttrs v) then
      [ ]
    else
      let
        ty = v._type or null;
      in
      if ty == "order" then
        [
          (mkFinding "order-pass" loc
            "def carries an order marker (`mkOrder`/`mkBefore`/`mkAfter`, `_type = \"order\"`); the order pass is outside the byte-mode surface"
          )
        ]
      else if ty == "merge" then
        concatMap (orderWalk loc) (v.contents or [ ])
      else if ty == "if" then
        orderWalk loc (v.content or { })
      else if ty == "override" then
        orderWalk loc (v.content or { })
      else if ty != null then
        [ ]
      else
        concatMap (k: orderWalk (loc ++ [ k ]) v.${k}) (attrNames v);

  # config projection (mirrors core's `configOf`, sans nixpkgs): a structured module's `config`, else
  # the whole shorthand attrset minus key/_file/_module metadata.
  configMarkers = [
    "imports"
    "options"
    "config"
    "freeformType"
    "disabledModules"
  ];
  isStructured = m: any (k: m ? ${k}) configMarkers;
  configOf =
    m:
    if isStructured m then
      (m.config or { })
    else
      builtins.removeAttrs m [
        "key"
        "_file"
        "_module"
      ];

  # ── per-attrset-module findings (constructs 1 + 4) ─────────────────────────
  moduleFindings =
    m:
    let
      leaves = optionLeaves (m.options or { });
      orderInConfig = orderWalk [ ] (configOf m);
      orderInDefaults = concatMap (
        l: if l.leaf ? default then orderWalk l.loc l.leaf.default else [ ]
      ) leaves;
      functionTo = concatMap (
        l:
        if (l.leaf ? type) && namesFunctionTo 32 l.leaf.type then
          [
            (mkFinding "function-to" l.loc
              "option type names `functionTo`, which is intentionally omitted from the byte-mode type surface"
            )
          ]
        else
          [ ]
      ) leaves;
    in
    orderInConfig ++ orderInDefaults ++ functionTo;

  # ── construct 2: a function module whose formals include `options` ─────────
  optionsArgFindings =
    e:
    if e.fn && isFunction e.module && (functionArgs e.module ? "options") then
      [
        (mkFinding "options-introspection" [ ]
          "a module function takes an `options` formal; the byte-mode `.options` is a minimal descriptor map, not the reference-engine `options` structure"
        )
      ]
    else
      [ ];

  # ── construct 3: an option loc declared with a `type` in more than one module ──
  typedLocsOf =
    module: map (l: l.loc) (filter (l: l.leaf ? type) (optionLeaves (module.options or { })));

  lint =
    { modules }:
    let
      modList = if isList modules then modules else [ modules ];
      collected = collect modList;

      perModule = concatMap (
        e: (optionsArgFindings e) ++ (if e.fn then [ ] else moduleFindings e.module)
      ) collected;

      # A loc typed in ≥2 attrset modules ⇒ a typeMerge reliance. List-value equality groups the locs
      # (each module contributes a loc at most once — an attrset has no duplicate keys), so a count ≥2
      # is exactly "declared in >1 module". O(n²) in the typed-loc count, which is small.
      allTyped = concatMap (e: if e.fn then [ ] else typedLocsOf e.module) collected;
      repeatedTyped = filter (loc: length (filter (x: x == loc) allTyped) >= 2) (unique allTyped);
      typeMerge = map (
        loc:
        mkFinding "type-merge" loc
          "option `${showLoc loc}' is declared with a type in more than one module; the reference engine combines the declarations through a `typeMerge` functor, gen-merge field-unions them (later type wins)"
      ) repeatedTyped;
    in
    perModule ++ typeMerge;
in
{
  inherit lint;
}
