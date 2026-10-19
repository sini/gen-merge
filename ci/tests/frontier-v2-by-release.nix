# WHETHER A NIXPKGS CONSTRUCTOR SHIPS A `merge.v2` IS A FACT OF THE RELEASE, READ OFF THE RECORD (den-hoag-wsbgz).
#
# `frontierOf` does not walk a container whose constructor ships a v2 merge while the record states none: that record
# is a `//` override of the fold. It read "ships one" from a per-constructor table column, true for `nullOr`, which
# is false on nixos-25.11 and nixos-26.05 (their `nullOr` has a v1 merge). A stock 26.05 `nullOr` below a stock
# `submodule` was then taken for an override, its element was not walked, and a gen copy's `verify` there was
# silently dropped: `submodule { y : nullOr C }`, C rejecting 7, served `{ y = 7; }` where the locked release's
# `nullOr` refuses it (ADR-0039: a drop in gen's engine is gen's; ADR-0025 item 1).
#
# The suite's nixpkgs ships a v2 `nullOr`, so `nullOr2605` is nixos-26.05's own constructor (lib/types.nix at
# 26f4107e47e3, `nullOr`), copied over the locked lib's helpers. The cells read the gen engine over it and over the
# locked `nullOr`, and the overrides the clause exists for, whose readings this change keeps: a merge override (told
# by the check nixpkgs marks `isV2MergeCoherent`, and by the rebuild where the functor rebuilds its constructor) and a
# merge-and-check override (told by the rebuild alone).
#
# RED, evaluated at gen-merge 4e0c06f: `test-a-2605-nullOr-below-a-submodule-is-walked` reads `true` (served).
# Without the rebuild arm the merge-and-check override is refused. The coherence arm keeps a `coercedTo` override
# unwalked, whose functor rebuilds no `coercedTo`; no value read here moves without it.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  lib = nixpkgsLib;
  t = lib.types;
  inherit (builtins) deepSeq tryEval;
  accepted = v: (tryEval (deepSeq v v)).success;
  nullOr2605 =
    elemType:
    lib.mkOptionType rec {
      name = "nullOr";
      description = "null or ${
        lib.types.optionDescriptionPhrase (class: class == "noun" || class == "conjunction") elemType
      }";
      descriptionClass = "conjunction";
      check = x: x == null || elemType.check x;
      merge =
        loc: defs:
        let
          nulls = builtins.filter (def: def.value == null) defs;
        in
        if nulls == [ ] then
          elemType.merge loc defs
        else if builtins.length nulls == builtins.length defs then
          null
        else
          throw "The option `${lib.showOption loc}` is defined both null and not null, in ${lib.options.showFiles (lib.options.getFiles defs)}.";
      emptyValue = {
        value = null;
      };
      getSubOptions = elemType.getSubOptions;
      getSubModules = elemType.getSubModules;
      substSubModules = m: nullOr2605 (elemType.substSubModules m);
      # `elemTypeFunctor name { inherit elemType; }`, which the locked lib does not export: the locked `nullOr`'s
      functor = (t.nullOr elemType).functor // {
        type = payload: nullOr2605 payload.elemType;
      };
      nestedTypes.elemType = elemType;
    };
  # a gen copy rejecting 7
  C = gm.types.int // {
    verify = v: if v == 7 then "rejected by the copy" else gm.types.int.verify v;
  };
  # the gen engine's `config.x.y` over `submodule { y : T }`, y defined as `v`
  y =
    T: v:
    (gm.evalModuleTree { } [
      {
        options.x = lib.mkOption {
          type = t.submodule { options.y = lib.mkOption { type = T; }; };
        };
      }
      { config.x.y = v; }
    ]).config.x.y;
  mergeOverride = T: T // { merge = l: d: T.merge l d; };
  checkOverride =
    T:
    mergeOverride T
    // {
      check = x: T.check x;
    };
in
{
  flake.tests.frontier-v2-by-release = {
    # the release's fact, as the fixture states it: no v2, no coherent check, and a rebuild stating no v2
    test-the-2605-nullOr-ships-no-v2 = {
      expr =
        let
          r = nullOr2605 C;
        in
        [
          (r.merge ? v2)
          (r.check.isV2MergeCoherent or false)
          ((r.functor.type r.functor.payload).merge ? v2)
        ];
      expected = [
        false
        false
        false
      ];
    };
    test-a-2605-nullOr-below-a-submodule-is-walked = {
      expr = accepted (y (nullOr2605 C) 7);
      expected = false;
    };
    test-a-2605-nullOr-below-a-submodule-serves-an-accepted-value = {
      expr = y (nullOr2605 C) 3;
      expected = 3;
    };
    # live control: the locked release's `nullOr` ships a v2 merge, and was walked before
    test-the-locked-nullOr-below-a-submodule-is-walked = {
      expr = accepted (y (t.nullOr C) 7);
      expected = false;
    };
    # a merge override over a v2 `nullOr` is not walked: its fold serves (the check states coherence)
    test-a-merge-override-of-a-v2-nullOr-is-not-walked = {
      expr = y (mergeOverride (t.nullOr C)) 7;
      expected = 7;
    };
    # an override of the check too is told by the functor's rebuild
    test-a-merge-and-check-override-of-a-v2-nullOr-is-not-walked = {
      expr = y (checkOverride (t.nullOr C)) 7;
      expected = 7;
    };
  };
}
