# THE EMPTY VALUE IS THE ONE NIXPKGS READS: the `emptyValue` of the record nixpkgs KEEPS (den-hoag-omf1j). With
# no surviving definition nixpkgs reads `type.emptyValue` (`mergeDefinitions`' `mergedValue`) off the declared
# option's record after `fixupOptionType` (one declaration: `substSubModules` over `getSubModules` where that is
# non-null) or after `mergeOptionDecls`' `typeMerge` (two declarations: the functor's rebuild). So a `//` over
# `emptyValue` is honoured on a record nixpkgs keeps and dropped on one it rebuilds, and a `//` over gen's own
# `whenEmpty` is not nixpkgs' field and moves nothing.
#
# Each cell reads gen's engine and nixpkgs' `lib.evalModules` over the same declarations in the same run, and states
# the value both must hold: a refusal reads "<R>". Every cell but the controls moved with this unit.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  nt = nixpkgsLib.types;
  try =
    e:
    let
      r = builtins.tryEval (builtins.deepSeq e e);
    in
    if r.success then r.value else "<R>";
  # an option `o` of the type `ty L` declared `n` times, defined by `defs L`, read on gen's engine and nixpkgs'
  both =
    {
      ty,
      defs ? _: [ ],
      n ? 1,
      # one record declared `n` times (the engine's one-value pair), or `n` records built apart
      shared ? true,
      wrap ? _: v: v,
      read ? c: c.o,
    }:
    let
      decl =
        L:
        let
          one = wrap L (ty L);
        in
        builtins.genList (_: {
          options.o = L.mkOption { type = if shared then one else wrap L (ty L); };
        }) n;
      mods = L: decl L ++ map (d: { config.o = d; }) (defs L);
    in
    {
      gen = try (read (gm.evalModuleTree { } (mods gm)).config);
      np = try (read (nixpkgsLib.evalModules { modules = mods nixpkgsLib; }).config);
    };
  same = v: {
    gen = v;
    np = v;
  };
  tys = L: L.types or L;
  sub =
    L:
    (tys L).submodule {
      options.a = L.mkOption {
        type = (tys L).str;
        default = "x";
      };
    };
  off = L: [ (L.mkIf false [ ]) ];
in
{
  flake.tests.empty-value-kept-record = {
    # controls: a record no `//` touched serves its constructor's empty value, and a leaf refuses
    test-control-listOf-unoverridden-serves-empty = {
      expr = both {
        ty = L: (tys L).listOf (tys L).str;
        defs = off;
      };
      expected = same [ ];
    };
    test-control-str-unoverridden-refuses = {
      expr = both { ty = L: (tys L).str; };
      expected = same "<R>";
    };
    # THE PRECEDENCE: the two fields disagree and nixpkgs' field decides
    test-disagreeing-fields-read-emptyValue = {
      expr = both {
        ty =
          L:
          (tys L).str
          // {
            emptyValue.value = "EV";
            whenEmpty.value = "WE";
          };
      };
      expected = same "EV";
    };
    # a kept record's `//` over `emptyValue` is honoured, in both directions
    test-kept-listOf-emptyValue-none-refuses = {
      expr = both {
        ty = L: (tys L).listOf (tys L).str // { emptyValue = { }; };
        defs = off;
      };
      expected = same "<R>";
    };
    test-kept-str-emptyValue-value-serves = {
      expr = both {
        ty = L: (tys L).str // { emptyValue.value = "EV"; };
        defs = off;
      };
      expected = same "EV";
    };
    # a `//` over `whenEmpty` alone is no nixpkgs field
    test-whenEmpty-only-none-serves-constructors = {
      expr = both { ty = L: (tys L).listOf (tys L).str // { whenEmpty = { }; }; };
      expected = same [ ];
    };
    test-whenEmpty-only-value-refuses-on-a-leaf = {
      expr = both { ty = L: (tys L).str // { whenEmpty.value = "WE"; }; };
      expected = same "<R>";
    };
    # a record stating a module set is rebuilt (`fixupOptionType`), and its `//` dropped
    test-rebuilt-submodule-drops-emptyValue-none = {
      expr = both { ty = L: sub L // { emptyValue = { }; }; };
      expected = same { a = "x"; };
    };
    test-rebuilt-listOf-submodule-drops-emptyValue-none = {
      expr = both {
        ty = L: (tys L).listOf (sub L) // { emptyValue = { }; };
        defs = off;
      };
      expected = same [ ];
    };
    test-rebuilt-attrsOf-submodule-drops-emptyValue-value = {
      expr = both { ty = L: (tys L).attrsOf (sub L) // { emptyValue.value = "EV"; }; };
      expected = same { };
    };
    # a module set nulled by `//` is not rebuilt: its own `emptyValue` is read
    test-nulled-module-set-is-kept = {
      expr = both {
        ty =
          L:
          sub L
          // {
            getSubModules = null;
            emptyValue.value = "EV";
          };
      };
      expected = same "EV";
    };
    # two declarations: the kept record is the functor's join, which drops the `//`
    test-two-declarations-drop-emptyValue-none = {
      expr = both {
        n = 2;
        ty =
          L:
          (tys L).listOf (tys L).str
          // {
            check = _: false;
            emptyValue = { };
          };
        defs = off;
      };
      expected = same [ ];
    };
    test-two-declarations-drop-emptyValue-value = {
      expr = both {
        n = 2;
        ty =
          L:
          (tys L).str
          // {
            check = _: false;
            emptyValue.value = "EV";
          };
      };
      expected = same "<R>";
    };
    test-three-declarations-drop-emptyValue-none = {
      expr = both {
        n = 3;
        ty =
          L:
          (tys L).listOf (tys L).str
          // {
            check = _: false;
            emptyValue = { };
          };
        defs = off;
      };
      expected = same [ ];
    };
    test-two-declarations-built-apart-drop-emptyValue-none = {
      expr = both {
        n = 2;
        shared = false;
        ty =
          L:
          (tys L).listOf (tys L).str
          // {
            check = _: false;
            emptyValue = { };
          };
        defs = off;
      };
      expected = same [ ];
    };
    # a FOREIGN record nixpkgs rebuilds is read as nixpkgs' rebuild: nixpkgs' `nonEmptyListOf` re-states `emptyValue = { }`
    # over `listOf`'s, so an option of it nothing defined refuses, and so does one whose definitions were all discharged
    # (services.mtr-exporter.jobs' type)
    test-foreign-nonEmptyListOf-submodule-undefined-refuses = {
      expr = both { ty = _: nt.nonEmptyListOf (sub nixpkgsLib); };
      expected = same "<R>";
    };
    test-foreign-nonEmptyListOf-submodule-discharged-refuses = {
      expr = both {
        ty = _: nt.nonEmptyListOf (sub nixpkgsLib);
        defs = off;
      };
      expected = same "<R>";
    };
    # a stray `whenEmpty` on a foreign record is no nixpkgs field
    test-foreign-nonEmptyListOf-stray-whenEmpty-refuses = {
      expr = both { ty = _: nt.nonEmptyListOf (sub nixpkgsLib) // { whenEmpty.value = [ ]; }; };
      expected = same "<R>";
    };
    # and a foreign module-set record's `//` over `emptyValue` is dropped by the rebuild, as nixpkgs drops it
    test-foreign-submodule-rebuild-drops-emptyValue-none = {
      expr = both { ty = _: sub nixpkgsLib // { emptyValue = { }; }; };
      expected = same { a = "x"; };
    };
    test-foreign-listOf-submodule-rebuild-drops-emptyValue-none = {
      expr = both { ty = _: nt.listOf (sub nixpkgsLib) // { emptyValue = { }; }; };
      expected = same [ ];
    };
    # an ELEMENT's empty value: `lazyAttrsOf` keeps a discharged key at it
    test-lazyAttrsOf-element-reads-emptyValue = {
      expr = both {
        ty = L: (tys L).str // { emptyValue.value = "EV"; };
        wrap = L: (tys L).lazyAttrsOf;
        defs = L: [ { k = L.mkIf false "v"; } ];
        read = c: c.o.k;
      };
      expected = same "EV";
    };
    # the empty value is served unchecked, as nixpkgs serves it: a `//` check rejecting it does not refuse it
    test-bad-check-empty-value-is-served = {
      expr = both {
        ty = L: (tys L).listOf (tys L).str // { check = _: false; };
        defs = off;
      };
      expected = same [ ];
    };
    # THE ROOT'S FIX-UP REACHES ONLY THROUGH STEPS STATING A MODULE SET (den-hoag-vy14u): a union (`either`, `oneOf`)
    # or a nulled copy states none, so nixpkgs rebuilds nothing below it and reads the record as written there.
    # One discharged key under a lazy container reads its element's empty value.
    test-below-either-listOf-sub-emptyValue-none-refuses = {
      expr = both {
        ty =
          L:
          (tys L).either ((tys L).lazyAttrsOf ((tys L).listOf (sub L) // { emptyValue = { }; })) (tys L).int;
        defs = L: [ { k = L.mkIf false [ ]; } ];
        read = c: c.o.k;
      };
      expected = same "<R>";
    };
    test-below-either-listOf-sub-emptyValue-value-serves = {
      expr = both {
        ty =
          L:
          (tys L).either ((tys L).lazyAttrsOf (
            (tys L).listOf (sub L) // { emptyValue.value = "EV"; }
          )) (tys L).int;
        defs = L: [ { k = L.mkIf false [ ]; } ];
        read = c: c.o.k;
      };
      expected = same "EV";
    };
    # a submodule record: its empty value is the threaded fold's at a rebuilt position, its own field below a union
    test-below-oneOf-submodule-emptyValue-none-refuses = {
      expr = both {
        ty =
          L:
          (tys L).oneOf [
            (tys L).int
            ((tys L).lazyAttrsOf (sub L // { emptyValue = { }; }))
          ];
        defs = L: [ { k = L.mkIf false { }; } ];
        read = c: c.o.k;
      };
      expected = same "<R>";
    };
    # the union under an exact container: the record is read off a container node, which carries the root's answer
    test-below-either-under-attrsOf-emptyValue-value-serves = {
      expr = both {
        ty =
          L:
          (tys L).either ((tys L).attrsOf (
            (tys L).lazyAttrsOf ((tys L).listOf (sub L) // { emptyValue.value = "EV"; })
          )) (tys L).int;
        defs = L: [ { p.k = L.mkIf false [ ]; } ];
        read = c: c.o.p.k;
      };
      expected = same "EV";
    };
    # no union: a container whose module set is nulled stops the fix-up as a union does
    test-below-a-nulled-container-emptyValue-none-refuses = {
      expr = both {
        ty =
          L:
          (tys L).lazyAttrsOf (
            (tys L).lazyAttrsOf ((tys L).listOf (sub L) // { emptyValue = { }; }) // { getSubModules = null; }
          );
        defs = L: [ { p.k = L.mkIf false [ ]; } ];
        read = c: c.o.p.k;
      };
      expected = same "<R>";
    };
    # controls: with no stop above it the record is rebuilt and the `//` dropped, and a submodule below the union
    # is a root of its own whose fix-up reaches its option's record
    test-control-bare-listOf-sub-emptyValue-none-is-rebuilt = {
      expr = both {
        ty = L: (tys L).lazyAttrsOf ((tys L).listOf (sub L) // { emptyValue = { }; });
        defs = L: [ { k = L.mkIf false [ ]; } ];
        read = c: c.o.k;
      };
      expected = same [ ];
    };
    test-control-a-submodule-below-the-union-is-a-root-of-its-own = {
      expr = both {
        ty =
          L:
          (tys L).either ((tys L).lazyAttrsOf (
            (tys L).submodule {
              options.q = L.mkOption {
                type = (tys L).lazyAttrsOf ((tys L).listOf (sub L) // { emptyValue = { }; });
              };
            }
          )) (tys L).int;
        defs = L: [ { k.q.z = L.mkIf false [ ]; } ];
        read = c: c.o.k.q.z;
      };
      expected = same [ ];
    };
    # `postFold`'s empty value is `g` over its element's, read the same way (nixpkgs' twin, a `merge` override,
    # leaves the empty value unreshaped, so the cell states gen's value alone)
    test-postFold-reshapes-the-kept-empty-value = {
      expr = try (
        (gm.evalModuleTree { } [
          {
            options.o = gm.mkOption {
              type = t.postFold (v: v ++ [ "g" ]) (t.listOf t.str // { emptyValue.value = [ "e" ]; });
            };
          }
        ]).config.o
      );
      expected = [
        "e"
        "g"
      ];
    };
  };
}
