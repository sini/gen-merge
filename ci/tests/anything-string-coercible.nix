# `anything` takes a STRING-COERCIBLE SET as nixpkgs' `stringCoercibleSet` (den-hoag-z9m0f): a set with
# `outPath` or `__toString` (a derivation, a `toDerivation` record, a served option record) is carried
# WHOLE when defined once, refused when defined twice or more (equal ones too), and refused beside a
# definition of any other type. nixpkgs' `anything.merge` reads it so (`getType`, `mergeOneOption`).
#
# The arm used to be absent, so such a set took the attrset arm's per-key rebuild: one definition was
# rebuilt (a function-carrying derivation stopped equalling itself on Nix and Determinate; a throwing
# `outPath`, a throwing `__toString` or a throwing sibling field threw at the slot, because the per-key
# `? _type` test forces every key), and two or more were served as a per-key union (`all` doubled, a
# derivation with an attrset's extra keys, two derivations whose `outPath` throws).
#
# ★ EACH CELL STATES nixpkgs AS ITS REFERENCE AND RUNS IT, through two shapes: the option's own type
# (`anything`) and an element of `attrsOf anything` (gen-schema's instance freeform). A cell whose gen arm
# moves reds; so does one whose nixpkgs arm moves on a bump.
#
# The refusals' TEXTS are `ci/tests-error.nix`, `anything-string-coercible`; these cells pin verdicts and
# the projections a carried value serves.
#
# RED: the arm reverted (the string-coercible branch of `mergeAnythingDefs` removed) serves every `refused`
# cell, throws in `throwing-*` and `tostring-*`, refuses `option-record-once`, and gives `whole = false`
# in `function-carrying-once` on Nix and Determinate. Lix compares a rebuilt closure equal, so that one
# cell cannot see the rebuild there; the `throwing-*` cells see it on all three.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  np = nixpkgsLib;
  drv =
    name:
    derivation {
      inherit name;
      # a literal: nix-unit evaluates purely, so `builtins.currentSystem` is missing
      system = "x86_64-linux";
      builder = "/bin/sh";
    };
  p = drv "zg-p";
  q = drv "zg-q";
  # function-carrying: `==` on a rebuilt closure is false on Nix and Determinate
  pf = p // {
    g = x: x + 1;
  };
  # one `outPath`, another field
  px = p // {
    meta.extra = true;
  };
  pt = p // {
    outPath = throw "zg-outpath";
  };
  op = {
    outPath = "/nix/store/11111111111111111111111111111111-zg-op";
    k = 1;
  };
  ts = {
    __toString = _: "zg-ts";
    k = 1;
  };
  tsLazy = {
    __toString = _: "zg-ts";
    bad = throw "zg-lazy-field";
  };
  tsBoom = {
    __toString = throw "zg-tostring";
    k = 1;
  };
  mintS = {
    __mint.minted = "zg-ms";
    __toString = _: "m";
    k = 1;
  };
  # the type marker alone is not string-coercible: the ordinary arm, unmoved
  tyOnly = {
    type = "derivation";
    k = 1;
  };
  A.extra = 1;
  # gen's own served option record: string-coercible through `__toString`, no `__mint`
  gOpt =
    (genMerge.evalModuleTree { } [
      {
        options.o = genMerge.mkOption {
          type = genMerge.types.str;
          default = "x";
        };
      }
    ]).options.o;

  shapes = L: {
    anything = L.types.anything;
    attrsOf = L.types.attrsOf L.types.anything;
  };
  wrap = s: v: if s == "anything" then v else { x = v; };
  unwrap = s: v: if s == "anything" then v else v.x;
  modules =
    L: s: defs:
    [ { options.o = L.mkOption { type = (shapes L).${s}; }; } ]
    ++ map (v: { config.o = wrap s v; }) defs;
  gen = s: defs: unwrap s (genMerge.evalModuleTree { } (modules genMerge s defs)).config.o;
  nixpkgs = s: defs: unwrap s (np.evalModules { modules = modules np s defs; }).config.o;
  ok = x: (builtins.tryEval (builtins.seq x true)).success;
  both = s: defs: read: {
    gen = read (gen s defs);
    nixpkgs = read (nixpkgs s defs);
  };

  # refused on both engines: the slot's value does not evaluate
  refused = {
    drv-twice = [
      p
      p
    ];
    drv-three-times = [
      p
      p
      p
    ];
    outpath-only-twice = [
      op
      op
    ];
    tostring-only-twice = [
      ts
      ts
    ];
    two-derivations = [
      p
      q
    ];
    one-outpath-different-fields = [
      p
      px
    ];
    drv-then-attrset = [
      p
      A
    ];
    attrset-then-drv = [
      A
      p
    ];
    throwing-outpath-twice = [
      pt
      pt
    ];
    minted-coercible-twice = [
      mintS
      mintS
    ];
    option-record-twice = [
      gOpt
      gOpt
    ];
  };
  refusedCells =
    s:
    builtins.listToAttrs (
      map (n: {
        name = "test-${s}-${n}-is-refused";
        value = {
          expr = both s refused.${n} ok;
          expected = {
            gen = false;
            nixpkgs = false;
          };
        };
      }) (builtins.attrNames refused)
    );

  # served on both engines, read through the projections the carried value owes
  served = {
    # carried whole: `removeAttrs [ "type" ]` defeats derivation `==`'s outPath shortcut
    function-carrying-once = {
      defs = [ pf ];
      read = v: {
        whole = removeAttrs v [ "type" ] == removeAttrs pf [ "type" ];
        drvPath = v.drvPath == p.drvPath;
      };
      want = {
        whole = true;
        drvPath = true;
      };
    };
    # the key set reads; `outPath` throws only on demand
    throwing-outpath-once = {
      defs = [ pt ];
      read = v: {
        names = builtins.attrNames v;
        outPath = ok v.outPath;
      };
      want = {
        names = builtins.attrNames pt;
        outPath = false;
      };
    };
    tostring-lazy-field-once = {
      defs = [ tsLazy ];
      read = v: {
        names = builtins.attrNames v;
        str = "${v}";
        bad = ok v.bad;
      };
      want = {
        names = [
          "__toString"
          "bad"
        ];
        str = "zg-ts";
        bad = false;
      };
    };
    tostring-throws-once = {
      defs = [ tsBoom ];
      read = v: {
        names = builtins.attrNames v;
        k = v.k;
        str = ok "${v}";
      };
      want = {
        names = [
          "__toString"
          "k"
        ];
        k = 1;
        str = false;
      };
    };
    option-record-once = {
      defs = [ gOpt ];
      read = v: {
        names = builtins.attrNames v;
        str = "${v}";
        value = v.value;
      };
      want = {
        names = builtins.attrNames gOpt;
        str = "${gOpt}";
        value = "x";
      };
    };
    # LIVE CONTROLS, unmoved by the arm: one definition, and the type marker without `outPath`
    drv-once = {
      defs = [ p ];
      read = v: {
        names = builtins.attrNames v;
        outPath = v.outPath == p.outPath;
      };
      want = {
        names = builtins.attrNames p;
        outPath = true;
      };
    };
    minted-coercible-once = {
      defs = [ mintS ];
      read = v: v.k;
      want = 1;
    };
    type-marker-only-beside-an-attrset = {
      defs = [
        tyOnly
        A
      ];
      read = v: v;
      want = tyOnly // A;
    };
  };
  servedCells =
    s:
    builtins.listToAttrs (
      map (n: {
        name = "test-${s}-${n}-is-served";
        value = {
          expr = both s served.${n}.defs served.${n}.read;
          expected = {
            gen = served.${n}.want;
            nixpkgs = served.${n}.want;
          };
        };
      }) (builtins.attrNames served)
    );
in
{
  flake.tests.anything-string-coercible =
    refusedCells "anything"
    // refusedCells "attrsOf"
    // servedCells "anything"
    // servedCells "attrsOf";
}
