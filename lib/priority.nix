# Priority / property algebra — the byte-mode subset.
#
# Design spec §1 (priority handling) + §7 (the grepped subset). den + the gen corpus use only
# `mkDefault` / `mkForce` / `mkMerge` / `mkIf` (+ the implicit `mkOptionDefault` from a plain
# `default =`). We therefore implement ONE override rule — lowest priority-number wins, ties merge —
# over the four anchor constructors (all instances of the general `mkOverride N`) plus the two def
# combinators `mkMerge` / `mkIf`. The nixpkgs ORDER pass (`mkOrder`/`mkBefore`/`mkAfter`) and the
# exotic named overrides are deliberately absent: zero uses across the surface (spec §7). Adding the
# order pass later is demand-driven (phased-path §7 D3).
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
    ;

  defaultPriority = 100;

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

  isProperty = v: isAttrs v && v ? _type;

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
    isProperty
    dischargeProperties
    filterOverrides
    filterOverridesRich
    pushDownProperties
    defaultPriority
    ;
}
