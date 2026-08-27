# Priority / property algebra — the byte-mode subset.
#
# Design spec §1 (priority handling) + §7 (the grepped subset). den + the gen corpus use only
# `mkDefault` / `mkForce` / `mkMerge` / `mkIf` (+ the implicit `mkOptionDefault` from a plain
# `default =`). We therefore implement ONE override rule — lowest priority-number wins, ties merge —
# over the four anchor constructors (all instances of the general `mkOverride N`) plus the two def
# combinators `mkMerge` / `mkIf`. The exotic named overrides are deliberately absent: zero uses
# across the surface (spec §7).
#
# ★ THE ORDER PASS IS NO LONGER ABSENT, and this header used to say the opposite. It said
# `mkOrder`/`mkBefore`/`mkAfter` were deliberately left out and that adding them later was
# demand-driven (phased-path §7 D3). THE DEMAND ARRIVED: a consumer told that its list-valued
# definitions accumulate across files asks next in what order, and nixpkgs' answer is `mkOrder`.
#
# ★★ AND THE MISSING PASS WAS A MISSING UNWRAP, so this closes a leak rather than only adding a
# feature. An order marker is an attrset carrying `_type`, so `isProperty` accepts it,
# `dischargeProperties` matches none of its three branches, and the `else` arm hands the WHOLE
# MARKER ATTRSET on as the value — nixpkgs' own `dischargeProperties` has no `"order"` branch
# either, because `sortProperties` is what unwraps it. With no such pass, a single `mkBefore "x"`
# reached a permissively-typed option as the literal
# `{ _type = "order"; priority = 500; content = "x"; }` (measured at this repo before the pass
# landed), and three order-marked list defs aborted uncatchably on `expected a list but found a set`.
#
# Priority numbers match nixpkgs exactly so a def carrying a nixpkgs-authored `mkForce`/`mkDefault`
# resolves identically:
#   bare def (unspecified) .......... 100   (defaultOverridePriority)
#   mkForce ......................... 50
#   mkOverride N .................... N
#   mkDefault ....................... 1000
#   mkOptionDefault (a `default =`) . 1500
{ prelude }:
let
  inherit (prelude)
    isAttrs
    concatMap
    foldl'
    filter
    map
    mapAttrs
    attrNames
    sort
    ;

  defaultPriority = 100;
  # The ORDER axis's default, and it is a DIFFERENT number line from `defaultPriority` above.
  # nixpkgs: mkBefore 500 < defaultOrderPriority 1000 < mkAfter 1500.
  defaultOrderPriority = 1000;

  # ── constructors ──────────────────────────────────────────────────────────
  mkOverride = priority: content: {
    _type = "override";
    inherit priority content;
  };
  mkOptionDefault = mkOverride 1500;
  mkDefault = mkOverride 1000;
  mkForce = mkOverride 50;

  mkMerge = contents: {
    _type = "merge";
    inherit contents;
  };

  mkIf = condition: content: {
    _type = "if";
    inherit condition content;
  };

  # The order constructors. gen-merge's property correspondence is TOTAL — it exports a constructor
  # for every `_type` it interprets — so interpreting `"order"` carries these with it rather than
  # leaving a property the engine can read and no consumer can write.
  mkOrder = priority: content: {
    _type = "order";
    inherit priority content;
  };
  mkBefore = mkOrder 500;
  mkAfter = mkOrder 1500;

  isProperty = v: isAttrs v && v ? _type;
  isOrderMarker = v: isAttrs v && (v._type or null) == "order";

  # ── dischargeProperties : a (possibly-wrapped) def value → [{ priority; value }] ──
  # Flattens mkMerge, resolves mkIf (false ⇒ contributes nothing), and stamps mkOverride's
  # priority onto every discharged sub-def. A property-free value is a bare def at priority 100.
  dischargeProperties =
    v:
    if isProperty v then
      if v._type == "merge" then
        concatMap dischargeProperties v.contents
      else if v._type == "if" then
        (if v.condition then dischargeProperties v.content else [ ])
      else if v._type == "override" then
        # Stamp the override priority but keep `content` LAZY — do NOT recurse into it. nixpkgs
        # `dischargeProperties` never descends into an mkOverride's content (its override case is the
        # bare `[ def ]` fall-through); the priority is read off the wrapper and the value is forced
        # only if this def wins `filterOverrides`. Recursing here forced every override-wrapped def —
        # including a LOSING option default whose body throws (den's host `intoAttr` default
        # `{…}.${config.class}` for `class == "droid"`), which must be dropped, not evaluated.
        [
          {
            inherit (v) priority;
            value = v.content;
          }
        ]
      else
        [
          {
            priority = defaultPriority;
            value = v;
          }
        ]
    else
      [
        {
          priority = defaultPriority;
          value = v;
        }
      ];

  # ── filterOverrides : keep only the defs of minimum priority-number (highest precedence) ──
  # nixpkgs' override pass. Ties (equal min priority) are all kept and merged downstream, in
  # stable list order (the order pass is intentionally omitted — spec §7).
  filterOverrides =
    defs:
    if defs == [ ] then
      [ ]
    else
      let
        minPrio = foldl' (m: d: if d.priority < m then d.priority else m) (prelude.head defs).priority defs;
      in
      filter (d: d.priority == minPrio) defs;

  # ── filterOverridesRich : the override pass exposing the selected priority alongside the winners ──
  # The nixpkgs `filterOverrides'` analogue (winners PLUS the `highestPrio` it resolved). The
  # provenance channel (lib/modules.nix) reads `highestPrio` for a loc's record `priority`. This is a
  # SEPARATE impl, NOT `filterOverrides = (filterOverridesRich defs).winners`: the value path (every
  # structural per-element merge, the freeform pass) calls `filterOverrides` per loc, and routing it
  # through the `{ winners; highestPrio }` wrapper would allocate a throwaway record per element —
  # measurably regressing the collection perf workloads. So `filterOverrides` keeps its direct,
  # allocation-free form and this rich variant is used only (lazily) where `highestPrio` is wanted.
  filterOverridesRich =
    defs:
    if defs == [ ] then
      {
        winners = [ ];
        highestPrio = null;
      }
    else
      let
        minPrio = foldl' (m: d: if d.priority < m then d.priority else m) (prelude.head defs).priority defs;
      in
      {
        winners = filter (d: d.priority == minPrio) defs;
        highestPrio = minPrio;
      };

  # ── sortProperties : the ORDER pass — strip the `mkOrder` wrapper, THEN sort ──
  # nixpkgs `lib/modules.nix` `sortProperties`. It runs LAST of the three passes, on the defs
  # `filterOverrides` kept, and it does two things in one step: unwrap every order marker to its
  # `content`, and stable-sort every def by its order priority.
  #
  # ★★★ `priority` IS OVERLOADED ACROSS TWO AXES AND THE FIELD NAME HIDES IT — this is the one
  # hazard in the pass. `dischargeProperties` above stamps the OVERRIDE priority (100 by default,
  # `mkForce` 50, …) onto EVERY def; the order axis is a different number line entirely
  # (`defaultOrderPriority` 1000, `mkBefore` 500, `mkAfter` 1500). nixpkgs' own `strip` OVERWRITES
  # `priority` with the order number and gets away with it only because the pass order is
  # discharge → filterOverrides → sortProperties: override filtering has already consumed the
  # override priority by the time the order priority lands on top of it.
  #
  # ★★ TWO CONSEQUENCES, AND THE SECOND IS WHAT DEFUSES THE FIRST:
  #   1. **Under nixpkgs' SHAPE the pass order is not negotiable.** Sorting before `filterOverrides`
  #      hands the override pass the ORDER numbers as if they were override numbers: it keeps only
  #      the minimum, one definition survives, and `mkBefore`/`mkAfter` silently become an override.
  #      Measured by seeding exactly that — nixpkgs' `strip` plus a reordered spine — against
  #      `mkBefore [a]` · `[b]` · `mkAfter [c]`, which collapses to `[ "b" ]`. No type catches it;
  #      the three-element ordering cell in ci/tests/parity-surface.nix is what does.
  #   2. **This impl does NOT overwrite `priority`, so the overload is gone rather than managed.**
  #      A VERBATIM port of nixpkgs' `strip`/`compare` is WRONG HERE anyway, because the two engines'
  #      inputs differ: nixpkgs' plain defs reach the pass UNSTAMPED, so
  #      `def.priority or defaultOrderPriority` correctly reads 1000 for them, while gen-merge's
  #      plain defs already carry the stamped override 100 — the same expression finds 100 and sorts
  #      every plain def BEFORE a `mkBefore`. Measured by seeding the verbatim port: `[ "b" "a" "c" ]`
  #      where nixpkgs gives `[ "a" "b" "c" ]`. The order key therefore rides its OWN field,
  #      `orderPriority`, and the override `priority` survives the pass untouched. The extra field is
  #      inert downstream — every consumer of a winner record projects `file`/`value` — and keeping
  #      it beats a second map over the defs to strip it.
  #      ★ SCOPED HONESTLY: because `priority` is left alone, this pass is in fact ROBUST to being
  #      run before `filterOverrides` — the seed in (1) reds only with nixpkgs' `strip` restored.
  #      It still runs LAST, both to stay readable against the nixpkgs spine it reproduces and
  #      because "read `priority` after the sort and it still means the override axis" is a property
  #      worth keeping true rather than one worth relying on nobody testing.
  #
  # `sort` is stable, so a marker-free def list (every key `defaultOrderPriority`) comes back in the
  # order it went in: on the fast path this pass is the identity permutation.
  sortProperties =
    defs:
    let
      strip =
        def:
        if isOrderMarker def.value then
          def
          // {
            value = def.value.content;
            orderPriority = def.value.priority;
          }
        else
          def // { orderPriority = defaultOrderPriority; };
    in
    sort (a: b: a.orderPriority < b.orderPriority) (map strip defs);

  # ── pushDownProperties : distribute a config-root property into its keys ──────
  # `config = mkIf c { a = 1; }` must behave as `{ a = mkIf c 1; }` (nixpkgs pushDownProperties):
  # the property is pushed to each key BEFORE per-option def collection. Returns a plain attrset
  # keyed by option name, each value possibly still property-wrapped (resolved later by discharge).
  pushDownProperties =
    v:
    if isProperty v then
      if v._type == "merge" then
        foldl' mergeConfigAttrs { } (map pushDownProperties v.contents)
      else if v._type == "if" then
        mapAttrs (_: val: mkIf v.condition val) (pushDownProperties v.content)
      else if v._type == "override" then
        mapAttrs (_: val: mkOverride v.priority val) (pushDownProperties v.content)
      else
        v
    else
      v;

  # Combine two config attrsets; a key present in both becomes an mkMerge of the two.
  mergeConfigAttrs =
    a: b:
    a
    // (
      let
        bNames = attrNames b;
      in
      builtins.listToAttrs (
        map (k: {
          name = k;
          value =
            if a ? ${k} then
              mkMerge [
                a.${k}
                b.${k}
              ]
            else
              b.${k};
        }) bNames
      )
    );
in
{
  inherit
    mkOverride
    mkOptionDefault
    mkDefault
    mkForce
    mkMerge
    mkIf
    mkOrder
    mkBefore
    mkAfter
    isProperty
    isOrderMarker
    dischargeProperties
    filterOverrides
    filterOverridesRich
    sortProperties
    pushDownProperties
    defaultPriority
    defaultOrderPriority
    ;
}
