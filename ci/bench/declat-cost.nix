# WHAT A SEED'S DECLARATION ADDRESS COSTS PER ELEMENT (den-hoag-mg94o).
#
# An element type E (a submodule with `inner : listOf E`) whose `nests.entry` records the `declAt`
# it is handed, as ci/tests/declaration-address.nix's `elemWith`. Arms:
#   flag = true   E declares `nests.declAt`, and the read forces every element's address
#   flag = false  the same trees with E unflagged: the floor, where no address is derived
# Shapes, each over n:
#   depth   one module, `xs` = n chains, each `d` elements deep
#   spread  n modules, module i defines `hosts."h<i>".xs = [ <chain d> ]`: the root's `hosts`
#           group holds n definitions
#   fan     n modules, each defines `hosts.h.xs = [ <chain d> ]`: one host's `xs` group holds n
#           definitions
# Both arms return the count of addresses read, so they agree on the value.
#
# RUN (per arm; the sweep, with its bounds, is `declat-cost.sh`):
#   nix-instantiate --eval --strict --json --argstr shape depth --argstr flag true \
#     --argstr d 2 --argstr n 200 ./ci/bench/declat-cost.nix
{
  shape ? "depth",
  flag ? "true",
  d ? "1",
  n ? "100",
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
  depth = builtins.fromJSON d;
  elemWith =
    _:
    let
      sub = t.submodule [
        {
          options.seen = gm.mkOption {
            type = t.listOf t.anything;
            default = [ ];
          };
          options.inner = gm.mkOption {
            type = t.listOf (elemWith null);
            default = [ ];
          };
        }
      ];
      nests = sub.nests;
    in
    t.defineType (
      sub
      // {
        nests =
          nests
          // {
            entry = x: {
              imports = [ (nests.entry { inherit (x) file value; }) ];
              config.seen = [ (x.declAt or null) ];
            };
          }
          // (if flag == "true" then { declAt = true; } else { });
      }
    );
  E = elemWith null;
  chain = k: if k > 1 then { inner = [ (chain (k - 1)) ]; } else { };
  hostT = t.submodule {
    options.xs = gm.mkOption {
      type = t.listOf E;
      default = [ ];
    };
  };
  decls = {
    options.xs = gm.mkOption {
      type = t.listOf E;
      default = [ ];
    };
    options.hosts = gm.mkOption {
      type = t.attrsOf hostT;
      default = { };
    };
  };
  mods =
    if shape == "depth" then
      [ { xs = builtins.genList (_: chain depth) count; } ]
    else if shape == "spread" then
      builtins.genList (i: { hosts."h${toString i}".xs = [ (chain depth) ]; }) count
    else if shape == "fan" then
      builtins.genList (_: { hosts.h.xs = [ (chain depth) ]; }) count
    else
      throw "unknown shape";
  cfg = (gm.evalModuleTree { } ([ decls ] ++ mods)).config;
  walk = e: e.seen ++ builtins.concatMap walk e.inner;
  all = builtins.concatMap walk (
    cfg.xs ++ builtins.concatMap (h: h.xs) (builtins.attrValues cfg.hosts)
  );
in
builtins.deepSeq all (builtins.length all)
