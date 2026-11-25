# A RE-HOMED NIXPKGS `either` / `oneOf` REFUSES AN AD-HOC v2 MEMBER AS NIXPKGS' `either` REFUSES IT (ADR-0039 rule (2),
# narrow application; den-hoag-58ja3). `homedAt` rebuilds a nixpkgs `either` stating a gen nesting element over gen's own
# `either`; a member caught by `adHocChecked` (v2, its constructor's coherent `check` replaced, no module set stated) is
# then folded by `adHocFold`, as nixpkgs' `either` refuses it through its v2 coherence check. The reaching cells WIDEN
# the member's check (`_: true`), so the check admits a definition the member's own v2 merge does not: before the
# gate, the union served such a definition through its other member, where nixpkgs refuses it. A member stating a module
# set, or a container over one, keeps `adHocChecked`'s exemption and is served as it was (Artemis F-B, 2026-11-25), and
# the gate reads the same rule, so a union whose only incoherent member states a module set opens no gate at all.
# Each cell reads gen's engine and the all-nixpkgs twin (`gt.*` as `np.*`, nixpkgs' `evalModules`) in the same cell.
# The refusal TEXT, and the adjacent coherent member's text, are pinned on the error plane
# (`tests-error.nix`, `either-ad-hoc-rehome`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  np = nl.types;
  # eng: "gen" (gm.evalModuleTree, gm.mkOption), "np" (nixpkgs' evalModules over the same records) or "twin"
  run =
    eng: t: v:
    let
      mods = [
        { options.x = (if eng == "gen" then gm else nl).mkOption { type = t; }; }
        { x = v; }
      ];
      r =
        if eng == "gen" then
          (gm.evalModuleTree { } mods).config.x
        else
          (nl.evalModules { modules = mods; }).config.x;
      o = builtins.tryEval (builtins.deepSeq r r);
    in
    if o.success then o.value else "REFUSED";
  sub =
    gt: mk:
    gt.submodule {
      key = "either-ad-hoc-rehome-sub";
      options.a = mk {
        type = np.int;
        default = 0;
      };
      options.b = mk {
        type = np.int;
        default = 0;
      };
    };
  gSub = sub gm.types gm.mkOption;
  npSub = sub np nl.mkOption;
  widen = t: t // { check = _: true; };
  pSub = v: !(builtins.isAttrs v) || (v.a or 0) != 2;
  narrow = t: t // { check = v: t.check v && pSub v; };
  # the gen engine's union and its twin: the widened `listOf int` beside the gen submodule (`either` or `oneOf`)
  unionOf =
    comb: K: s: m:
    if comb == "either" then
      K.either m s
    else
      K.oneOf [
        m
        s
      ];
  pair = comb: m: {
    gen = run "gen" (unionOf comb np gSub (m np)) { a = 1; };
    twin = run "twin" (unionOf comb np npSub (m np)) { a = 1; };
  };
  # a gen freeform host under nixpkgs' engine: the union is gen's to fold wherever the host is
  freeform =
    K: s: m:
    K.submodule { freeformType = K.attrsOf (np.either (m np) s); };
in
{
  flake.tests.either-ad-hoc-rehome = {
    # (i) SERVE -> TWIN-REFUSE: the widened member admits `{ a = 1; }`, its v2 merge rejects it, and the union refuses as
    # the twin does, where it once served `{ a = 1; b = 0; }` through the submodule
    test-a-widened-member-of-a-re-homed-either-is-refused-as-the-twin-refuses = {
      expr = pair "either" (K: widen (K.listOf K.int));
      expected = {
        gen = "REFUSED";
        twin = "REFUSED";
      };
    };
    # (iii) the same through `oneOf`, which nixpkgs builds as an `either`
    test-a-widened-member-of-a-re-homed-one-of-is-refused-as-the-twin-refuses = {
      expr = pair "oneOf" (K: widen (K.listOf K.int));
      expected = {
        gen = "REFUSED";
        twin = "REFUSED";
      };
    };
    # (iii) the route through a gen freeform host evaluated by nixpkgs' engine
    test-a-widened-member-under-a-gen-freeform-host-is-refused-on-nixpkgs-engine = {
      expr = {
        np = run "np" (freeform gm.types gSub (K: widen (K.listOf K.int))) {
          k = {
            a = 1;
          };
        };
        twin = run "twin" (freeform np npSub (K: widen (K.listOf K.int))) {
          k = {
            a = 1;
          };
        };
      };
      expected = {
        np = "REFUSED";
        twin = "REFUSED";
      };
    };
    # the adjacent negative: the same union over the member's own coherent check serves through the submodule
    test-control-the-coherent-member-of-a-re-homed-either-serves = {
      expr = pair "either" (K: K.listOf K.int);
      expected = {
        gen = {
          a = 1;
          b = 0;
        };
        twin = {
          a = 1;
          b = 0;
        };
      };
    };
    # (iv) THE MODULE-SET GUARD: an ad-hoc copy of a container over a module set, gen's or nixpkgs', keeps
    # `adHocChecked`'s exemption at a re-homed `either` and is served, as it is on main (Artemis F-B: held, not licensed)
    test-an-ad-hoc-gen-container-over-a-module-set-at-a-re-homed-either-is-served = {
      expr = run "gen" (np.either (narrow (gm.types.nullOr gSub)) np.str) { a = 1; };
      expected = {
        a = 1;
        b = 0;
      };
    };
    test-an-ad-hoc-nixpkgs-container-over-a-gen-module-set-at-a-re-homed-either-is-served = {
      expr = run "gen" (np.either (narrow (np.nullOr gSub)) np.str) { a = 1; };
      expected = {
        a = 1;
        b = 0;
      };
    };
    # beside a widened member that does open the gate, the module-set member is still exempt: a definition only it
    # takes is served through it
    test-a-module-set-member-beside-an-opened-gate-keeps-its-exemption = {
      expr = run "gen" (np.either (narrow (gm.types.nullOr gSub)) (widen (np.listOf np.int))) { a = 1; };
      expected = {
        a = 1;
        b = 0;
      };
    };
    # the native boundary: the same predicate stated with `addCheck` is served
    test-control-an-add-check-container-over-a-module-set-at-a-re-homed-either-is-served = {
      expr = run "gen" (np.either (np.addCheck (gm.types.nullOr gSub) pSub) np.str) { a = 1; };
      expected = {
        a = 1;
        b = 0;
      };
    };
  };
}
