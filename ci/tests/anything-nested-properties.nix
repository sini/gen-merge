# `anything` discharges a property marker at a NESTED key, as nixpkgs' `anything` does (den-hoag-15wnx).
#
# Its attrset arm used to recurse per key through itself and never through the engine's spine, so an
# `mkIf`/`mkMerge`/`mkOverride` below the top level was carried into the value as data (`{ _type = "if";
# condition; content; }`) at rc 0: an `mkIf false`'s content was served. Only a definition's own top-level
# marker was discharged, by the option holding it. The arm now takes nixpkgs' `(attrsOf anything).merge`:
# each key's definitions take the spine (discharge, `filterOverrides`, `sortProperties`), and a key whose
# every definition discharges to nothing is DROPPED, value and key set alike.
#
# ★ EACH CELL STATES nixpkgs AS ITS REFERENCE AND RUNS IT. One fixture is written with each engine's own
# constructors and evaluated by both, `genMerge.evalModuleTree` and `nixpkgsLib.evalModules`, and the cell
# pins the two readings to one literal. A cell whose gen arm moves reds; so does one whose nixpkgs arm moves
# on a bump, which is the reference changing under the claim rather than gen-merge drifting from it.
#
# ★ THREE SHAPES PER CASE, because the marker reaches `anything`'s arm through each: the option's own type
# (`anything`), and an element of `attrsOf anything` and of `lazyAttrsOf anything` (gen-schema's instance
# freeform is the first of those). The containers' own key sets are not the subject; the element's are.
#
# RED: the arm reverted to `mapAttrs (k: mergeAnythingDefs (loc ++ [ k ]))` gives the marker as data in
# `ifTrue1`/`merge1`/`ifFalse*`/`mergeEmpty`, and a refusal in `force1`/`default1`/`ifFalseScalar`.
# The laziness half (a strict key set forces a definition beside the one read) is `ci/tests-error.nix`,
# `anything-nested-properties`, because both engines throw there.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  np = nixpkgsLib;
  # one fixture, written with constructor set `L`
  fx = L: {
    ifTrue1 = [
      { d = "G"; }
      { sub = L.mkIf true { d = "S"; }; }
    ];
    merge1 = [
      { d = "G"; }
      {
        sub = L.mkMerge [
          { e = "E"; }
          { d = "S"; }
        ];
      }
    ];
    # an override at a nested key, against a sibling definition's plain value at that key
    force1 = [
      { sub.d = "R"; }
      { sub.d = L.mkForce "S"; }
    ];
    default1 = [
      { sub.d = "R"; }
      { sub.d = L.mkDefault "S"; }
    ];
    # a scalar under `mkIf false`, at a key a sibling definition also defines
    ifFalseScalar = [
      { d = "G"; }
      { d = L.mkIf false "S"; }
    ];
    # an all-discharged key beside a sibling: the key is dropped
    ifFalse1 = [
      { d = "G"; }
      { sub = L.mkIf false { d = "S"; }; }
    ];
    # the same with one definition: nothing is left
    ifFalse1one = [ { sub = L.mkIf false { d = "S"; }; } ];
    # depth 2: the parent stays, empty
    ifFalse2 = [
      { d = "G"; }
      { a.sub = L.mkIf false { d = "S"; }; }
    ];
    # an `mkMerge` whose every member discharges
    mergeEmpty = [
      { d = "G"; }
      { sub = L.mkMerge [ (L.mkIf false { e = "E"; }) ]; }
    ];
    # a scalar under `mkIf false` one level down: its parent is still defined, and empty
    ifFalseLeaf = [
      { d = "G"; }
      { sub.x = L.mkIf false 1; }
    ];
    # LIVE CONTROL: no marker anywhere, served alike before and after
    plain1 = [
      { d = "G"; }
      { sub.d = "S"; }
    ];
  };
  shapes = L: {
    anything = L.types.anything;
    attrsOf = L.types.attrsOf L.types.anything;
    lazyAttrsOf = L.types.lazyAttrsOf L.types.anything;
  };
  wrap = s: v: if s == "anything" then v else { x = v; };
  unwrap = s: v: if s == "anything" then v else v.x;
  modules =
    L: s: n:
    [ { options.o = L.mkOption { type = (shapes L).${s}; }; } ]
    ++ map (v: { config.o = wrap s v; }) (fx L).${n};
  # the value, and the key set where the case's subject is a key (depth 2 reads `a`'s)
  view =
    s: n: c:
    let
      v = unwrap s c.o;
    in
    {
      inherit v;
      keys = builtins.attrNames (if n == "ifFalse2" then v.a else v);
    };
  gen = s: n: view s n (genMerge.evalModuleTree { } (modules genMerge s n)).config;
  nixpkgs = s: n: view s n (np.evalModules { modules = modules np s n; }).config;
  # the reference value of each case, which is nixpkgs' (both arms are pinned to it)
  ref = {
    ifTrue1 = {
      v = {
        d = "G";
        sub.d = "S";
      };
      keys = [
        "d"
        "sub"
      ];
    };
    merge1 = {
      v = {
        d = "G";
        sub = {
          d = "S";
          e = "E";
        };
      };
      keys = [
        "d"
        "sub"
      ];
    };
    force1 = {
      v.sub.d = "S";
      keys = [ "sub" ];
    };
    default1 = {
      v.sub.d = "R";
      keys = [ "sub" ];
    };
    ifFalseScalar = {
      v.d = "G";
      keys = [ "d" ];
    };
    ifFalse1 = {
      v.d = "G";
      keys = [ "d" ];
    };
    ifFalse1one = {
      v = { };
      keys = [ ];
    };
    ifFalse2 = {
      v = {
        a = { };
        d = "G";
      };
      keys = [ ];
    };
    mergeEmpty = {
      v.d = "G";
      keys = [ "d" ];
    };
    ifFalseLeaf = {
      v = {
        d = "G";
        sub = { };
      };
      keys = [
        "d"
        "sub"
      ];
    };
    plain1 = {
      v = {
        d = "G";
        sub.d = "S";
      };
      keys = [
        "d"
        "sub"
      ];
    };
  };
  cells =
    s:
    builtins.listToAttrs (
      map (n: {
        name = "test-${s}-${n}";
        value = {
          expr = {
            gen = gen s n;
            nixpkgs = nixpkgs s n;
          };
          expected = {
            gen = ref.${n};
            nixpkgs = ref.${n};
          };
        };
      }) (builtins.attrNames ref)
    );
in
{
  flake.tests.anything-nested-properties = cells "anything" // cells "attrsOf" // cells "lazyAttrsOf";
}
