# WHAT THE RESERVATION SCOPE COSTS PER SCOPED ENTRY (`__reservedKeys`, den-hoag-8x97u).
#
# The off-scope path (no `__reservedKeys` anywhere in a tree, which is every tree but a schema kind
# entry's) is gated by the hub perf bench, and allocates nothing per entry. The hub bench reaches no
# scoped entry, so the SCOPED path is measured here: two arms import the SAME n modules, each writing
# one declared option, through an importer that is plain (`plain`) or carries a reservation of 22
# names, the size of gen-schema's and gen-aspects' union (`scoped`). Neither arm writes a reserved
# name, so both resolve to the same config and the counter difference is the scope's own work.
#
# ★ THE ROW IS `nrThunks`, NAMED; no cpu row is read. ★ MARGINAL, NOT TOTAL: each arm runs at two
# sizes, so a fixed set-up overhead cancels and what is left is what one more scoped entry costs.
#
# RUN (per arm; the sweep, with its bound, is `reserved-scope-cost.sh`):
#   nix-instantiate --eval --strict --json --argstr arm scoped --argstr n 64 ./ci/bench/reserved-scope-cost.nix
{
  arm ? "scoped",
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

  idx = builtins.genList (i: i) (builtins.fromJSON n);
  reservation = {
    names = builtins.listToAttrs (
      builtins.genList (i: {
        name = "r${toString i}";
        value = "reserved r${toString i}";
      }) 22
    );
    exempt = [
      [ "kind" ]
      [
        "__mint"
        "minted"
      ]
    ];
  };
  children = map (i: { "o${toString i}" = i; }) idx;
  importer =
    if arm == "plain" then
      { imports = children; }
    else if arm == "scoped" then
      {
        __reservedKeys = reservation;
        imports = children;
      }
    else
      throw "unknown arm";
in
(gm.evalModuleTree { } [
  {
    options = builtins.listToAttrs (
      map (i: {
        name = "o${toString i}";
        value = gm.mkOption {
          type = gm.types.int;
          default = 0;
        };
      }) idx
    );
  }
  importer
]).config
