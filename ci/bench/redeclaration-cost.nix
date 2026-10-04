# WHAT ONE OPTION DECLARED IN n MODULES COSTS, AGAINST n OPTIONS DECLARED ONCE EACH (den-hoag-f010k).
#
# Arms, each over n modules:
#   leafN    n modules each declare one `str` option, and one module defines them all (the per-module
#            tax every declaring module pays: the trie, the guard's spine, the value fold)
#   sameN    every module declares the SAME `str` option `p`, and one module defines it (the per-loc
#            redeclaration fold on top of that tax)
#   sameOv   sameN, reading `length options.p.overridden` (the published shadow provenance)
#   provSame a freeform tree, one undeclared key defined by all n modules, `provenance` deepSeq'd
#   provDist the same, n distinct undeclared keys
#
# ★ MARGINAL, NOT TOTAL: `redeclaration-cost.sh` runs each arm at two sizes, so a fixed set-up
# overhead cancels. `sameN − leafN` is what a redeclaration costs beyond declaring.
#
# RUN (per arm; the sweep, with its bounds, is `redeclaration-cost.sh`):
#   nix-instantiate --eval --strict --json --argstr arm sameN --argstr n 64 ./ci/bench/redeclaration-cost.nix
{
  arm ? "sameN",
  n ? "64",
}:
let
  fromLock =
    name:
    let
      lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
      node = lock.nodes.${name}.locked;
    in
    builtins.fetchTree {
      inherit (node)
        type
        owner
        repo
        rev
        narHash
        ;
    };
  prelude = import "${fromLock "gen-prelude"}/lib";
  genTypes = import "${fromLock "gen-types"}" { inherit prelude; };
  genMemo = import "${fromLock "gen-memo"}" { inherit prelude; };
  genScope = import "${fromLock "gen-scope"}" { inherit prelude; };
  gm = import ../../lib {
    inherit prelude;
    types = genTypes;
    memo = genMemo;
    scope = genScope;
  };
  t = gm.types;

  count = builtins.fromJSON n;
  each = f: builtins.genList f count;
  same =
    each (_: {
      options.p = gm.mkOption { type = t.str; };
    })
    ++ [ { config.p = "v"; } ];
  freeform = defs: gm.evalModuleTree { } ([ { freeformType = t.attrsOf t.str; } ] ++ defs);
in
if arm == "leafN" then
  let
    names = each (i: "o${toString i}");
    r = gm.evalModuleTree { } (
      each (i: {
        options."o${toString i}" = gm.mkOption { type = t.str; };
      })
      ++ [
        {
          config = builtins.listToAttrs (
            each (i: {
              name = "o${toString i}";
              value = "v${toString i}";
            })
          );
        }
      ]
    );
    vs = map (k: r.config.${k}) names;
  in
  builtins.deepSeq vs (builtins.length vs)
else if arm == "sameN" then
  (gm.evalModuleTree { } same).config.p
else if arm == "sameOv" then
  builtins.length (gm.evalModuleTree { } same).options.p.overridden
else if arm == "provSame" then
  builtins.deepSeq
    (freeform (
      each (i: {
        config.u = "v${toString i}";
      })
    )).provenance
    count
else if arm == "provDist" then
  builtins.deepSeq
    (freeform (
      each (i: {
        config."u${toString i}" = "v";
      })
    )).provenance
    count
else
  throw "unknown arm"
