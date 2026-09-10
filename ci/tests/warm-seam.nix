# The plane seam (design spec §3 O1) — the DECISION genuinely governs the SPLICE, in both
# directions. Every other cell in `warm.nix` runs over the shipped `genMerge` (the real gen-memo
# plane); this file substitutes an ADVERSARIAL plane through `genMergeWithMemo` (the `genMergeWith`
# precedent, `ci/flake.nix:74`) and reads the splice's behaviour off it directly, so a landing that
# accepted `memo` as a formal but kept deciding reuse from its own local footprint set — never
# calling `memo.warmDecision` at all — cannot pass unnoticed: neither substituted plane would move
# the outcome under that regression, which is exactly what these two cells are built to catch.
#
# `genMergeWithMemo`'s substitute matches `gen-memo`'s own `warmDecision` SIGNATURE
# (`{ accessor; prior }: seeds: { isClean; reusable; identitiesHeld; }` — `lib/warm.nix`) so the seam
# is exercised at the real call shape gen-merge uses, not a private bypass. `reusable` is never read
# by gen-merge's own consumption, so a constant stub is sound there. `identitiesHeld` IS read on every
# warm re-compose, and it is stubbed permissively here on purpose: this file's subject is the splice
# gate, these fixtures mint no instances, and a real plane would answer the same empty moved set over
# them. The refusal's own arms are in `warm.nix`, over the shipped plane.
{ genMergeWithMemo, ... }:
let
  # Arm 1 — a plane that answers "everything is dirty", unconditionally. If the splice gate really
  # asks this plane, NOTHING is reusable and the whole tree remerges — byte-equal to cold by
  # construction (the merge is deterministic), but with an EMPTY `reused` set rather than whatever
  # the real footprint would have allowed.
  alwaysDirty = {
    warmDecision =
      { accessor, prior }:
      seeds: {
        isClean = _nid: false;
        reusable = null;
        identitiesHeld = _: [ ];
      };
  };
  # Arm 2 — a plane that answers "everything is clean", unconditionally, even a location an edit
  # just touched. If the splice gate really asks this plane, the EDITED leaf still gets spliced from
  # the PRIOR (stale) value rather than re-merged — the adversarial-in-the-other-direction reading:
  # a landing that ignored the plane and kept its own (correct) local dirtiness check would instead
  # report the freshly edited value here, which is precisely the regression this arm catches.
  alwaysClean = {
    warmDecision =
      { accessor, prior }:
      seeds: {
        isClean = _nid: true;
        reusable = null;
        identitiesHeld = _: [ ];
      };
  };

  gmDirty = genMergeWithMemo alwaysDirty;
  gmClean = genMergeWithMemo alwaysClean;

  # TWO declared leaves: `a` is edited (`mkForce "ea"` over base "av" — the same shape `warm.nix`'s
  # `test-decl-side-dirtiness` uses, for the same reason: an edit that MOVES a value the engine has
  # already merged once, so warm and cold can disagree about which value survives), `b` stays
  # UNTOUCHED. `b` is what makes BOTH arms discriminate against a regression that accepted `memo`
  # but kept deciding reuse from its own local footprint instead of calling the plane: a local
  # footprint would (correctly, on its own terms) call `b` reusable and `a` dirty regardless of what
  # either substituted plane claims, so it disagrees with `alwaysDirty` on `b` (arm 1) and with
  # `alwaysClean` on `a` (arm 2) — the plane's say-so has to be the thing that decides, not a
  # fallback computation that happens to often agree with it.
  mkFixture =
    gm:
    let
      base = [
        {
          options.a = gm.mkOption { type = gm.types.str; };
          options.b = gm.mkOption { type = gm.types.str; };
        }
        {
          _file = "ca";
          a = "av";
          b = "bv";
        }
      ];
      edited = [
        {
          _file = "edit";
          a = gm.mkForce "ea";
        }
      ];
      coldOf = mods: gm.evalModuleTree { modules = mods; };
      warmOf =
        b: e:
        gm.evalModuleTree {
          modules = b ++ e;
          warmFrom = coldOf b;
          editedModules = e;
        };
    in
    {
      inherit base edited;
      w = warmOf base edited;
      c = coldOf (base ++ edited);
    };

  dirtyFx = mkFixture gmDirty;
  cleanFx = mkFixture gmClean;
in
{
  flake.tests.warm-seam = {
    # Arm 1 (isClean = _: false): nothing is reusable, and the always-remerge result is still
    # byte-equal to cold (the merge itself is deterministic — the plane only gates the SPLICE).
    test-plane-always-dirty-reuses-nothing = {
      expr = {
        reused = dirtyFx.w.warmDecision.reused;
        byte = builtins.toJSON dirtyFx.w.config == builtins.toJSON dirtyFx.c.config;
      };
      expected = {
        reused = [ ];
        byte = true;
      };
    };

    # Arm 2 (isClean = _: true): the plane's say-so is trusted even over an edit — warm `a` reads
    # the PRIOR "av", not the freshly edited "ea" a correct local footprint would have re-merged to.
    test-plane-always-clean-splices-the-edit = {
      expr = cleanFx.w.config.a;
      expected = "av";
    };
  };
}
