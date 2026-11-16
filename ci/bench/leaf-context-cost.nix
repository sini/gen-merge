# WHAT THE LEAF FOLD'S CONTEXT UNION COSTS, AND WHAT THE OUTPUT SLOT OVER `raw` COSTS AGAINST ITS TWIN.
#
# Two families of arm, swept with bounds by `leaf-context-cost.sh`:
#
#   slot / twin  one freeform `lazyAttrsOf T` on nixpkgs' `lib.evalModules`, W keys each defined by N modules,
#                the whole config forced. `slot` is the README's output slot over `raw`
#                (`../tests/_fixtures/output-slot-over-raw.nix`); `twin` is the same law in nixpkgs'
#                vocabulary alone, `mergeEqualOption` at the leaf (`../tests/_fixtures/output-slot-relatives.nix`).
#                Shapes, per key per definition:
#                  leaf     an equal scalar            list   a one-element list
#                  attrs    a disjoint one-key set     drv    one shared derivation record
#                  drvFresh a separately built derivation record of one outPath
#                  str      an equal plain string      strCtx an equal string carrying one context
#                  strMix   an equal string, alternately with and without its context (the union adds one)
#                  deep     an equal scalar at depth D under nested attrsets
#   len          one `str` option defined N times by one string of 2^L characters carrying a context, on
#                nixpkgs' engine (`np`, the exported `leafFold`) or gen-merge's (`gen`, `mergeLeaf`). Shapes
#                `ctx` (every definition carries it) and `mix` (alternately with and without). The strings
#                are built once, outside the fold, so every N pays them alike.
#
# RUN (per arm; the sweep, with its bounds, is `leaf-context-cost.sh`):
#   nix-instantiate --eval --strict --json --argstr arm slot --argstr shape strMix --argstr w 200 --argstr n 3 ./ci/bench/leaf-context-cost.nix
{
  arm ? "slot",
  shape ? "leaf",
  w ? "200",
  n ? "3",
  d ? "1",
  site ? "np",
  len ? "12",
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
  ciLock = builtins.fromJSON (builtins.readFile ../flake.lock);
  lib = import "${builtins.fetchTree ciLock.nodes.${ciLock.nodes.root.inputs.nixpkgs}.locked}/lib";
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
  slot = import ../tests/_fixtures/output-slot-over-raw.nix {
    inherit lib;
    genMerge = gm;
  };
  inherit
    (import ../tests/_fixtures/output-slot-relatives.nix {
      inherit lib genTypes;
      genMerge = gm;
    })
    npTwin
    ;

  W = builtins.fromJSON w;
  N = builtins.fromJSON n;
  D = builtins.fromJSON d;
  L = builtins.fromJSON len;

  ctxS = builtins.toFile "leaf-context-cost" "c";
  odd = j: j - (j / 2) * 2 == 1;
  freeform =
    t:
    let
      keys = builtins.genList (i: "k${toString i}") W;
      nest = k: v: if k == 0 then v else { l = nest (k - 1) v; };
      # the shape is selected once per evaluation, so no arm pays a per-key selection
      val =
        {
          leaf = _: 7;
          list = j: [ j ];
          attrs = j: { "a${toString j}" = j; };
          drv = _: {
            type = "derivation";
            outPath = "/nix/store/aaaa-d";
            name = "d";
          };
          drvFresh =
            j:
            {
              type = "derivation";
              outPath = "/nix/store/aaaa-d";
              name = "d";
              inherit j;
            }
            // {
              j = 0;
            };
          str = _: "s";
          strCtx = _: ctxS;
          strMix = j: if odd j then builtins.unsafeDiscardStringContext ctxS else ctxS;
          deep = _: nest D 7;
        }
        .${shape};
      defs = builtins.genList (j: { config = lib.genAttrs keys (_: val j); }) N;
      c =
        (lib.evalModules {
          modules = [ { config._module.freeformType = lib.types.lazyAttrsOf t; } ] ++ defs;
        }).config;
      v = removeAttrs c [ "_module" ];
    in
    builtins.deepSeq v (builtins.length (builtins.attrNames v));

  # 2^L characters by doubling, so the fixture holds no large list
  long =
    let
      dbl = k: s: if k == 0 then s else dbl (k - 1) (s + s);
      withCtx = builtins.toFile "leaf-context-len" "a" + dbl L "x";
      plain = builtins.unsafeDiscardStringContext withCtx;
      strs = builtins.genList (
        i: if shape == "ctx" then withCtx else (if odd i then plain else withCtx)
      ) N;
      m = [
        { options.x = (if site == "np" then lib else gm).mkOption { type = gm.types.str; }; }
      ]
      ++ map (v: { config.x = v; }) strs;
      x =
        if site == "np" then
          (lib.evalModules { modules = m; }).config.x
        else
          (gm.evalModuleTree { } m).config.x;
    in
    # the served string is read whole, and the reading is its context-entry count: 1
    builtins.seq (builtins.deepSeq strs null) (
      builtins.seq (builtins.stringLength x) (
        builtins.length (builtins.attrNames (builtins.getContext x))
      )
    );
in
if arm == "slot" then
  freeform slot
else if arm == "twin" then
  freeform npTwin
else if arm == "len" then
  long
else
  throw "unknown arm"
