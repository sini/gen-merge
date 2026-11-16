# THE LEAF FOLD KEEPS THE STRING CONTEXTS IT COLLAPSES. `==` ignores string context, so an `==`-equal
# string collapse whose definitions differ in context serves the head with the UNION of every definition's
# context, as Nix's own concatenation does (ADR-0034's quotient rule). The decision stays `==`'s. The fold
# is one at two sites, `lib/modules.nix` `mergeLeaf` (gen's engine) and `lib/interface.nix` `leafFold`
# (what the export publishes to nixpkgs' engine), and every gen leaf that folds by it carries the union.
#
# ★ THE GRID IS THE MOVE'S CENSUS. Every gen leaf arm and its nixpkgs twin, eight cells, both engines
# (`np` = nixpkgs' `lib.evalModules`, `gen` = `genMerge.evalModuleTree`). A reading is the served string's
# context-entry count, prefixed `TEXT:` where the served text is not the definitions' (a concatenating
# fold), or REFUSED. Cells list definitions in module order.
#
# Where gen departs from nixpkgs here it keeps a strict SUPERSET of nixpkgs' context on the same `==`
# decision: nixpkgs' `mergeEqualOption` keeps the head's context, a value that silently drops a dependency
# edge, so parity's silent-value exception and the quotient rule together decide gen's value. Unmoved:
# the concatenating folds (gen `unspecified`, a check-only `mkOptionType`, nixpkgs `lines`), which already
# carry every context, and the per-key `==` collapse of `attrs` and of a check-only attrset fold, which
# keeps one definition's context as nixpkgs' `attrs` does (an open defect, not this fold).
#
# RED, measured on all three evaluators: the fold that serves the head unchanged (gen-merge before the
# union) moves 88 readings, the 11 union rows × `ctxThenPlain`, `twoContexts`, `threeOneCtx`,
# `threeContexts` × both engines (0→1, 1→2, 1→3), and nothing else. `ctxAlone`, `plainThenCtx`,
# `plainAlone` and `bothPlain` are controls: they read alike on both folds.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  lib = nixpkgsLib;
  inherit (builtins)
    toFile
    unsafeDiscardStringContext
    appendContext
    getContext
    attrNames
    length
    tryEval
    deepSeq
    isString
    isAttrs
    ;
  a = toFile "merge-leaf-a" "a";
  b = toFile "merge-leaf-b" "b";
  c = toFile "merge-leaf-c" "c";
  plain = unsafeDiscardStringContext a;
  # the text of `a`, carrying only `b`'s (or `c`'s) context
  aWithB = appendContext plain {
    ${unsafeDiscardStringContext b} = {
      path = true;
    };
  };
  aWithC = appendContext plain {
    ${unsafeDiscardStringContext c} = {
      path = true;
    };
  };
  cells = {
    ctxAlone = [ a ];
    plainAlone = [ plain ];
    ctxThenPlain = [
      a
      plain
    ];
    plainThenCtx = [
      plain
      a
    ];
    twoContexts = [
      a
      aWithB
    ];
    threeOneCtx = [
      plain
      a
      plain
    ];
    threeContexts = [
      a
      aWithB
      aWithC
    ];
    bothPlain = [
      plain
      plain
    ];
  };
  gt = genMerge.types;
  nt = lib.types;
  # how a cell's string is placed in a definition, and read back from the value
  direct = {
    put = s: s;
    get = v: v;
  };
  key = {
    put = s: { k = s; };
    get = v: v.k;
  };
  read =
    v:
    if isString v then
      (if v == plain then "" else "TEXT:") + toString (length (attrNames (getContext v)))
    else
      "shape:" + builtins.typeOf v;
  run =
    eng: arm: vs:
    let
      mo = if eng == "np" then lib.mkOption else genMerge.mkOption;
      m = [ { options.x = mo { type = arm.t; }; } ] ++ map (v: { config.x = arm.w.put v; }) vs;
      cfg =
        if eng == "np" then
          (lib.evalModules { modules = m; }).config
        else
          (genMerge.evalModuleTree { } m).config;
      r = tryEval (deepSeq cfg.x (arm.w.get cfg.x));
    in
    if r.success then read r.value else "REFUSED";

  # the law's rows: the union; nixpkgs' head-only collapse; a concatenating fold; the per-key `==` collapse
  # that keeps the last definition's context; and a fold refusing every second definition
  union = {
    ctxAlone = "1";
    plainAlone = "0";
    ctxThenPlain = "1";
    plainThenCtx = "1";
    twoContexts = "2";
    threeOneCtx = "1";
    threeContexts = "3";
    bothPlain = "0";
  };
  headOnly = union // {
    ctxThenPlain = "0";
    twoContexts = "1";
    threeOneCtx = "0";
    threeContexts = "1";
  };
  concatenated = lib.mapAttrs (n: v: if length cells.${n} > 1 then "TEXT:" + v else v) union;
  perKey = headOnly // {
    ctxThenPlain = "1";
    plainThenCtx = "0";
  };
  refusedAfterOne = lib.mapAttrs (n: v: if length cells.${n} > 1 then "REFUSED" else v) union;

  arms = {
    gen-raw = {
      t = gt.raw;
      w = direct;
      law = union;
    };
    gen-str = {
      t = gt.str;
      w = direct;
      law = union;
    };
    gen-string = {
      t = gt.string;
      w = direct;
      law = union;
    };
    gen-path = {
      t = gt.path;
      w = direct;
      law = union;
    };
    gen-anything = {
      t = gt.anything;
      w = direct;
      law = union;
    };
    gen-anything-key = {
      t = gt.anything;
      w = key;
      law = union;
    };
    gen-attrsOf-str = {
      t = gt.attrsOf gt.str;
      w = key;
      law = union;
    };
    gen-lazyAttrsOf-str = {
      t = gt.lazyAttrsOf gt.str;
      w = key;
      law = union;
    };
    gen-nullOr-str = {
      t = gt.nullOr gt.str;
      w = direct;
      law = union;
    };
    gen-either-str-int = {
      t = gt.either gt.str gt.int;
      w = direct;
      law = union;
    };
    gen-enum = {
      t = gt.enum "e" [ plain ];
      w = direct;
      law = union;
    };
    gen-unspecified = {
      t = gt.unspecified;
      w = direct;
      law = concatenated;
    };
    gen-mkOptionType-checkonly = {
      t = genMerge.mkOptionType {
        name = "chk";
        check = isString;
      };
      w = direct;
      law = concatenated;
    };
    gen-attrs-key = {
      t = gt.attrs;
      w = key;
      law = perKey;
    };
    gen-mkOptionType-checkonly-key = {
      t = genMerge.mkOptionType {
        name = "chkA";
        check = isAttrs;
      };
      w = key;
      law = perKey;
    };
    np-raw = {
      t = nt.raw;
      w = direct;
      law = refusedAfterOne;
    };
    np-str = {
      t = nt.str;
      w = direct;
      law = headOnly;
    };
    np-path = {
      t = nt.path;
      w = direct;
      law = headOnly;
    };
    np-anything = {
      t = nt.anything;
      w = direct;
      law = headOnly;
    };
    np-anything-key = {
      t = nt.anything;
      w = key;
      law = headOnly;
    };
    np-attrsOf-str = {
      t = nt.attrsOf nt.str;
      w = key;
      law = headOnly;
    };
    np-nullOr-str = {
      t = nt.nullOr nt.str;
      w = direct;
      law = headOnly;
    };
    np-either-str-int = {
      t = nt.either nt.str nt.int;
      w = direct;
      law = headOnly;
    };
    np-enum = {
      t = nt.enum [ plain ];
      w = direct;
      law = headOnly;
    };
    np-unspecified = {
      t = nt.unspecified;
      w = direct;
      law = concatenated;
    };
    np-lines = {
      t = nt.lines;
      w = direct;
      law = concatenated;
    };
    np-mkOptionType-checkonly = {
      t = lib.mkOptionType {
        name = "chk";
        check = isString;
      };
      w = direct;
      law = concatenated;
    };
    np-attrs-key = {
      t = nt.attrs;
      w = key;
      law = perKey;
    };
    np-mkOptionType-checkonly-key = {
      t = lib.mkOptionType {
        name = "chkA";
        check = isAttrs;
      };
      w = key;
      law = perKey;
    };
  };
in
{
  flake.tests.merge-leaf = lib.mapAttrs' (
    an: arm:
    lib.nameValuePair "test-${an}-string-context" {
      expr = lib.genAttrs [ "np" "gen" ] (eng: lib.mapAttrs (_: run eng arm) cells);
      expected = {
        np = arm.law;
        gen = arm.law;
      };
    }
  ) arms;
}
