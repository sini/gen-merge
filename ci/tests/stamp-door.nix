# gen-merge: an entry door's copy question (`interface.departsOnlyOutside`, den-hoag-6foy1) is asked of the
# fields the door reads, less the fields a record's own evaluation decides (`interface.ownEvaluation`), and
# forces no other cell. On Nix and Determinate a whole-record stamp forces every cell, so inside a registry
# knot the door aborted uncatchably; Lix answered by identity. Tripwires are `abort`: the stamp's comparison
# tolerates a catchable throw in a cell (it reads two undefined cells as agreeing).
{ genMerge, interface, ... }:
let
  t = genMerge.types;
  sub = p: t.submodule ({ ... }: p "stamp-door: the module set was evaluated");
  # a submodule-family record under each door, and three containers over one
  shapes = p: {
    sub = sub p;
    door = genMerge.mkOptionType (sub p);
    doorDoor = genMerge.mkOptionType (genMerge.mkOptionType (sub p));
    defined = t.defineType (sub p);
    doorDefined = genMerge.mkOptionType (t.defineType (sub p));
    attrsOf = t.attrsOf (sub p);
    listOf = t.listOf (sub p);
    nullOr = t.nullOr (sub p);
  };
  forces =
    r:
    builtins.filter (n: r ? ${n} && !(builtins.tryEval (builtins.seq r.${n} true)).success) (
      builtins.attrNames interface.importReads
    );
  marks = x: (builtins.tryEval (builtins.deepSeq x.__mint true)).success;
  demoted = x: x.__mint ? unmintable;
  # each field the import door reads beyond the completion's stated domain, two inside it, and a forged
  # value for each, over one submodule: which copies each door takes as the same type, which it leaves stale
  base = t.submodule {
    options.a = genMerge.mkOption {
      type = t.int;
      default = 1;
    };
  };
  forged = {
    _type = "option-type-x";
    descriptionClass = "conjunction";
    deprecationMessage = "forged";
    merge = loc: defs: 42;
    emptyValue.value = 7;
    getSubOptions = _: { forged = true; };
    getSubModules = [ ];
    substSubModules = _: base;
    typeMerge = _: null;
    nestedTypes.forged = base;
    functor = base.functor // {
      name = "forged";
    };
    unroledNested.forged = base;
    mergeDefs = _: { value = 42; };
    verify = _: null;
  };
  copy = door: f: door (base // { ${f} = forged.${f}; });
  sameType =
    door:
    builtins.filter (
      f:
      let
        e = builtins.tryEval (t.typeEq (copy door f) (door base));
      in
      e.success && e.value
    ) (builtins.attrNames forged);
  stale = door: builtins.filter (f: (copy door f).__staleStamp or false) (builtins.attrNames forged);
in
{
  flake.tests.stamp-door = {
    # RED with a field the module set decides left out of `ownEvaluation`: it forces the module set
    test-own-evaluation-is-what-a-door-record-forces = {
      expr = builtins.mapAttrs (_: forces) (shapes throw);
      expected = {
        sub = interface.ownEvaluation;
        door = interface.ownEvaluation;
        doorDoor = interface.ownEvaluation;
        defined = interface.ownEvaluation;
        doorDefined = interface.ownEvaluation;
        attrsOf = [ ];
        listOf = [ ];
        nullOr = [ ];
      };
    };
    # the door's question itself, called directly over the import door's domain: RED at a whole-record stamp
    test-the-copy-question-forces-no-module-set = {
      expr = builtins.mapAttrs (_: interface.departsOnlyOutside interface.importReads) (shapes abort);
      expected = builtins.mapAttrs (_: _: true) (shapes abort);
    };
    test-a-door-record-mark-forces-no-module-set = {
      expr = map marks [
        (genMerge.mkOptionType (sub abort))
        (genMerge.mkOptionType (genMerge.mkOptionType (sub abort)))
        (genMerge.mkOptionType (t.defineType (sub abort)))
      ];
      expected = [
        true
        true
        true
      ];
    };
    # the copy question still answers at each field the door reads
    test-a-copy-departing-where-the-door-reads-is-demoted = {
      expr = map (b: demoted (genMerge.mkOptionType (b // { mergeDefs = _: { value = 0; }; }))) [
        t.int
        (t.listOf t.int)
        (t.submodule { })
      ];
      expected = [
        true
        true
        true
      ];
    };
    # ... and a record its completion still is keeps its mark
    test-an-honest-record-keeps-its-mark = {
      expr = map (b: demoted (genMerge.mkOptionType b)) [
        t.int
        (t.listOf t.int)
        (t.submodule { })
      ];
      expected = [
        false
        false
        false
      ];
    };
    # THE PRICE, pinned: a copy departing only at `ownEvaluation` is the same type to `typeEq` at both doors
    # (at the import door every other copy is refused; `verify` enters sealed), and `defineType` leaves only
    # the copy departing at the fold stale. RED at a whole-record stamp: the import door takes none of the
    # three, and `defineType` leaves `unroledNested` stale.
    test-a-copy-departing-at-own-evaluation-is-the-same-type = {
      expr = {
        import = sameType genMerge.mkOptionType;
        defineType = builtins.attrNames (removeAttrs forged (sameType t.defineType));
        defineTypeStale = stale t.defineType;
      };
      expected = {
        import = [
          "descriptionClass"
          "nestedTypes"
          "unroledNested"
        ];
        defineType = [
          "mergeDefs"
          "verify"
        ];
        defineTypeStale = [ "mergeDefs" ];
      };
    };
  };
}
