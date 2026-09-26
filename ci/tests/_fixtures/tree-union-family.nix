# The class a tree-as-union-member can open: every member-taking combinator of `types` (the census in
# `ci/tests-error.nix` `tree-type.test-the-family-covers-the-member-taking-census` keeps this list
# honest), at depth 1 and depth 2, the binary ones in both member orders, over the tree-as-a-type `T`.
# 90 constructions, each with two definitions: a module attrset and a string.
#
# `gen` folds a construction in gen-merge's own eval, `reference` folds the SAME construction built
# from nixpkgs' types over nixpkgs' own `(evalModules …).type`, and `mount` hands the gen-merge
# construction to a real nixpkgs `lib.evalModules`. The first two are parity (inside gen's eval union
# membership is not mounting); the last is the foreign face.
{ genMerge, nixpkgsLib }:
let
  ts = genMerge.types;
  tree = genMerge.evalModuleTree {
    modules = [
      {
        options.a = genMerge.mkOption {
          type = ts.int;
          default = 0;
        };
      }
    ];
  };
  referenceTree = nixpkgsLib.evalModules {
    modules = [
      {
        options.a = nixpkgsLib.mkOption {
          type = nixpkgsLib.types.int;
          default = 0;
        };
      }
    ];
  };
  # `of` is the combinator the form applies, which is what the census compares against.
  forms = {
    eitherL = {
      of = "either";
      mk = ts: x: ts.either x ts.str;
      wrap = v: v;
    };
    eitherR = {
      of = "either";
      mk = ts: x: ts.either ts.str x;
      wrap = v: v;
    };
    oneOfL = {
      of = "oneOf";
      mk =
        ts: x:
        ts.oneOf [
          x
          ts.str
        ];
      wrap = v: v;
    };
    oneOfR = {
      of = "oneOf";
      mk =
        ts: x:
        ts.oneOf [
          ts.str
          x
        ];
      wrap = v: v;
    };
    nullOr = {
      of = "nullOr";
      mk = ts: x: ts.nullOr x;
      wrap = v: v;
    };
    # nixpkgs has no `option`; its reference side is `nullOr`, which is what gen's `option` is.
    option = {
      of = "option";
      mk = ts: x: (ts.option or ts.nullOr) x;
      wrap = v: v;
    };
    listOf = {
      of = "listOf";
      mk = ts: x: ts.listOf x;
      wrap = v: [ v ];
    };
    attrsOf = {
      of = "attrsOf";
      mk = ts: x: ts.attrsOf x;
      wrap = v: { k = v; };
    };
    lazyAttrsOf = {
      of = "lazyAttrsOf";
      mk = ts: x: ts.lazyAttrsOf x;
      wrap = v: { k = v; };
    };
  };
  names = builtins.attrNames forms;
  # Keyed `outer.inner` for depth 2, the key the measured mount table uses.
  constructions =
    builtins.mapAttrs (_: f: { inherit (f) mk wrap; }) forms
    // builtins.listToAttrs (
      builtins.concatMap (
        o:
        map (i: {
          name = "${o}.${i}";
          value = {
            mk = ts: x: forms.${o}.mk ts (forms.${i}.mk ts x);
            wrap = v: forms.${o}.wrap (forms.${i}.wrap v);
          };
        }) names
      ) names
    );
  definitions = {
    module = {
      a = 5;
    };
    string = "hello";
  };
  at =
    evalModules: mkOption: type: def:
    (evalModules {
      modules = [
        { options.s = mkOption { inherit type; }; }
        { config.s = def; }
      ];
    }).config.s;
in
{
  inherit forms constructions definitions;
  T = tree.type;
  gen = at genMerge.evalModuleTree genMerge.mkOption;
  foreign = at nixpkgsLib.evalModules nixpkgsLib.mkOption;
  cells = builtins.concatMap (
    c:
    map (d: {
      construction = c;
      definition = d;
      gen = constructions.${c}.mk ts tree.type;
      reference = constructions.${c}.mk nixpkgsLib.types referenceTree.type;
      value = constructions.${c}.wrap definitions.${d};
    }) (builtins.attrNames definitions)
  ) (builtins.attrNames constructions);
}
