# The output slot's relatives, read beside it by `../output-slot-over-raw.nix`:
#   npTwin    the same law in nixpkgs' vocabulary alone, `lib.mergeEqualOption` at the leaf (the reference)
#   dungeon   dungeon's `lib/outputs.nix` `leaf` (at 569cc91), verbatim but for its binding name
#   den       den v1's `nix/lib/aspects/fx/edges/route.nix` `mergeableType` (at 9bdfbc21), verbatim but for
#             its binding name
# and the mutants each cell family is driven red by, each the slot with one arm changed:
#   noMint    a construction rebuilt per key, as both consumers do (no `? __mint` guard)
#   drvKeys   a derivation rebuilt per key like any attrset (no `isDerivation` guard)
#   strict    nixpkgs' strict `attrsOf` in place of `lazyAttrsOf`
#   serveHead the leaf serves the head and never refuses
{
  lib,
  genMerge,
  genTypes,
}:
let
  mk =
    name: attrsArm: leaf:
    let
      self = lib.mkOptionType {
        inherit name;
        merge =
          loc: defs:
          let
            vs = map (d: d.value) defs;
          in
          if builtins.all builtins.isList vs then
            builtins.concatLists vs
          else if builtins.all attrsArm vs then
            (lib.types.lazyAttrsOf self).merge loc defs
          else
            leaf loc defs;
      };
    in
    self;
  plain = v: builtins.isAttrs v && !lib.isDerivation v && !(v ? __mint);
in
rec {
  # spelled as the slot is (not through `mk`), so the cost sweep prices the slot against a reference of its
  # own shape
  npTwin = lib.mkOptionType {
    name = "npTwin";
    merge =
      loc: defs:
      let
        vs = map (d: d.value) defs;
      in
      if builtins.all builtins.isList vs then
        builtins.concatLists vs
      else if builtins.all (v: builtins.isAttrs v && !lib.isDerivation v) vs then
        (lib.types.lazyAttrsOf npTwin).merge loc defs
      else
        lib.mergeEqualOption loc defs;
  };
  dungeon = lib.mkOptionType {
    name = "denOutput";
    merge =
      loc: defs:
      let
        vs = map (d: d.value) defs;
      in
      if builtins.all (v: builtins.isAttrs v && !lib.isDerivation v) vs then
        (lib.types.lazyAttrsOf dungeon).merge loc defs
      else if builtins.all builtins.isList vs then
        builtins.concatLists vs
      else
        genMerge.mergeDefs loc genTypes.any defs;
  };
  den = lib.mkOptionType {
    name = "mergeable";
    description = "auto-merged value (attrsets merge, lists concatenate, scalars must agree)";
    merge =
      loc: defs:
      let
        values = map (d: d.value) defs;
        first = builtins.head values;
        allLists = builtins.all builtins.isList values;
        allMergeableAttrs = builtins.all (v: builtins.isAttrs v && !(lib.isDerivation v)) values;
      in
      if builtins.length defs == 1 then
        first
      else if allLists then
        builtins.concatLists values
      else if allMergeableAttrs then
        (lib.types.lazyAttrsOf den).merge loc defs
      else if builtins.all (v: v == first) values then
        first
      else
        throw "den: the option `${lib.showOption loc}' has conflicting definitions from multiple aspects";
  };
  noMint = mk "noMint" (v: builtins.isAttrs v && !lib.isDerivation v) genMerge.types.raw.merge;
  drvKeys = mk "drvKeys" (v: builtins.isAttrs v && !(v ? __mint)) genMerge.types.raw.merge;
  strict =
    let
      self = lib.mkOptionType {
        name = "strict";
        merge =
          loc: defs:
          let
            vs = map (d: d.value) defs;
          in
          if builtins.all builtins.isList vs then
            builtins.concatLists vs
          else if builtins.all plain vs then
            (lib.types.attrsOf self).merge loc defs
          else
            genMerge.types.raw.merge loc defs;
      };
    in
    self;
  serveHead = mk "serveHead" plain (_: defs: (builtins.head defs).value);
}
