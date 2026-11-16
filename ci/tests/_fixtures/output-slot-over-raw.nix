# The README's "An output slot that merges by shape, over `raw`" spelling, VERBATIM between the two marker
# lines: `../output-slot-over-raw.nix` asserts the block is in README.md byte for byte, so the recipe a
# consumer copies and the type these cells mount cannot drift apart unseen. `lib` is nixpkgs' lib and
# `genMerge` is gen-merge's `lib`; the slot is mounted in nixpkgs' `lib.evalModules` and on gen-merge's
# engine alike.
{ lib, genMerge }:
let
  # README-BEGIN
  # nixpkgs-facing: `lib` is nixpkgs' lib, `genMerge` is gen-merge's flake `lib` output; the name is the consumer's
  slot = lib.mkOptionType {
    name = "slot";
    merge =
      loc: defs:
      let
        vs = map (d: d.value) defs;
      in
      if builtins.all builtins.isList vs then
        builtins.concatLists vs
      else if builtins.all (v: builtins.isAttrs v && !lib.isDerivation v && !(v ? __mint)) vs then
        (lib.types.lazyAttrsOf slot).merge loc defs
      else
        genMerge.types.raw.merge loc defs;
  };
  # README-END
in
slot
