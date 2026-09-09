# The location id is injective (design spec §3 O4 / §2.1). `options."a.b".c` and `options.a."b.c"`
# are TWO distinct declared leaves whose DISPLAY name (`showOption` — the dot-join, `lib/modules.nix`)
# collides: both read "a.b.c". The bipartite contribution relation's node ids must not collide the
# same way, or an edit to one leaks reuse-unsoundness onto the other (over-approximating dirty is
# sound; UNDER-approximating it, by merging two locations' dirtiness into one, is not). Only `"a.b".c`
# is edited here; `a."b.c"` stays untouched and must still be independently reusable.
#
# THE DISCRIMINATING CONJUNCT IS `reused`, NOT `byte`/`edited`/`untouched`: a non-injective (dot-join)
# node id ALSO produces a byte-identical config (the merge re-runs correctly either way — only the
# SPLICE's reuse bookkeeping is affected) and the same edited/untouched leaf VALUES, so those three
# hold on both the correct and the broken arm and cannot tell them apart. Only `reused` (the internal
# reuse-decision's OWN evidence) collapses to `[ ]` on a dot-joined id, because the collision makes
# the clean leaf indistinguishable from its dirty namesake and the whole merged node reads dirty.
{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkForce;
  t = gm.types;
  opt = gm.mkOption { type = t.str; };

  base = [
    {
      options."a.b".c = opt;
      options.a."b.c" = opt;
    }
    {
      _file = "base";
      "a.b".c = "dirty-base";
      a."b.c" = "clean-base";
    }
  ];
  edited = [
    {
      _file = "edit";
      "a.b".c = mkForce "dirty-edited";
    }
  ];
  coldOf = mods: evalModuleTree { modules = mods; };
  warmOf =
    b: e:
    evalModuleTree {
      modules = b ++ e;
      warmFrom = coldOf b;
      editedModules = e;
    };

  w = warmOf base edited;
  c = coldOf (base ++ edited);
in
{
  flake.tests.warm-locid = {
    test-injective-location-id-survives-a-colliding-display-name = {
      expr = {
        reused = w.warmDecision.reused;
        remergedKeys = builtins.attrNames w.warmDecision.remerged;
        byte = builtins.toJSON w.config == builtins.toJSON c.config;
        edited = w.config."a.b".c;
        untouched = w.config.a."b.c";
      };
      expected = {
        # The clean leaf (`a."b.c"`) is reusable; its edited namesake is not — the discriminating
        # conjunct (see file header).
        reused = [ "a.b.c" ];
        # OQ-2's accepted residual: the DISPLAY join still collides at publication (one string
        # standing for two distinct locations, in opposite buckets) — this is a companion reading,
        # not the discriminator.
        remergedKeys = [ "a.b.c" ];
        byte = true;
        edited = "dirty-edited";
        untouched = "clean-base";
      };
    };
  };
}
