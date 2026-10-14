# A door's return taken AS ITSELF states its check where nixpkgs reads it (den-hoag-v4cw1). nixpkgs' v2 protocol reads
# a declared type's rejection from `merge.v2`'s `headError` alone, and a `check` marked `isV2MergeCoherent` promises it
# is stated there. A caller's `//` copy can keep a marked check beside a merge that does not state it, so every door
# return that publishes the caller's merge as itself states the caller's check through
# `rebuildClosed.verifiedMerge.lifted`, nixpkgs' `addCheck` law. One cell per return site, each mounted in nixpkgs'
# `lib.evalModules`, inside `either _ <other>` or as the option's own type: a value the record's check rejects is
# refused, and its admitted twin is served, so neither a fold refusing everything nor one serving everything passes.
# Red, one cell per site, each with that site's lift taken out alone:
#  - `rebuildClosed`'s no-relation arm: `no-relation`;
#  - `rebuildClosed`'s constant-constructor arm: `own-functor`;
#  - `rebuildClosed`'s `close` for a top record stating no module set: `foreign-leaf-container`;
#  - `importType0`'s completed-container arm: `completed-container`;
#  - `importType0`'s nesting arm: `nesting-forge`;
#  - `carriedCopy`'s merge over a v2 base: `gen-verify-copy`;
#  - `rebuildClosed.imported`'s root: `foreign-verify-copy`.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    all
    deepSeq
    head
    isAttrs
    isInt
    isList
    tryEval
    ;
  run =
    t: v:
    let
      c =
        (nl.evalModules {
          modules = [
            { options.x = nl.mkOption { type = t; }; }
            { x = v; }
          ];
        }).config;
      o = tryEval (deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  sub = gt.submodule {
    key = "door-as-itself-sub";
    options.a = gm.mkOption {
      type = gt.int;
      default = 0;
    };
    options.b = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  # an ad-hoc check MARKED coherent, as nixpkgs' `addCheck` marks its own, over a merge that does not state it
  marked =
    t: p:
    t
    // {
      check = {
        __functor = _: v: t.check v && p v;
        isV2MergeCoherent = true;
      };
    };
  notTwo = v: !(isAttrs v) || v.a or 0 != 2;
  small = v: !(isList v) || all (x: !(isInt x) || x < 10) v;
  # a hand-built v2 record's merge, stating no `headError`
  hbMerge = {
    __functor =
      self: loc: defs:
      (self.v2 { inherit loc defs; }).value;
    v2 =
      { defs, ... }:
      {
        headError = null;
        value = (head defs).value;
        valueMeta = { };
      };
  };
  hbCheck = {
    __functor = _: v: isAttrs v && notTwo v;
    isV2MergeCoherent = true;
  };
  # the rejected value and its admitted twin, inside a union and as the option's own type
  both = t: {
    rejected = run (np.either t np.str) { a = 2; };
    admitted = run (np.either t np.str) { a = 1; };
    rootRejected = run t { a = 2; };
    rootAdmitted = run t { a = 1; };
  };
  inUnion = t: {
    rejected = run (np.either t np.str) { a = 2; };
    admitted = run (np.either t np.str) { a = 1; };
  };
in
{
  flake.tests.door-as-itself-states-check = {
    # a hand-built record stating no `typeMerge`
    test-no-relation = {
      expr =
        let
          r = {
            _type = "option-type";
            name = "door-as-itself-nr";
            description = "door-as-itself-nr";
            check = hbCheck;
            merge = hbMerge;
            deprecationMessage = null;
            getSubModules = null;
            substSubModules = _: r;
            emptyValue = { };
            nestedTypes = { };
            descriptionClass = null;
          };
        in
        both (gt.defineType r);
      expected = {
        rejected = "REFUSED";
        admitted.a = 1;
        rootRejected = "REFUSED";
        rootAdmitted.a = 1;
      };
    };
    # a hand-built record that is its own functor's `type`
    test-own-functor = {
      expr =
        let
          r0 = nl.mkOptionType {
            name = "door-as-itself-self";
            check = hbCheck;
            merge = hbMerge;
          };
          s = r0 // {
            functor = r0.functor // {
              type = s;
            };
          };
        in
        both (gt.defineType s);
      expected = {
        rejected = "REFUSED";
        admitted.a = 1;
        rootRejected = "REFUSED";
        rootAdmitted.a = 1;
      };
    };
    # a marked check over nixpkgs' `listOf`, whose merge does not state it
    test-foreign-leaf-container = {
      expr =
        let
          d = gt.defineType (marked (np.listOf np.int) small);
        in
        {
          rootRejected = run d [ 20 ];
          rootAdmitted = run d [ 1 ];
          rejected = run (np.either d np.str) [ 20 ];
        };
      expected = {
        rootRejected = "REFUSED";
        rootAdmitted = [ 1 ];
        rejected = "REFUSED";
      };
    };
    # a completed gen container whose fold is another constructor's, and a marked check over a completed `nullOr`
    test-completed-container = {
      expr =
        let
          forge = gm.mkOptionType (gt.listOf sub // { inherit (gt.nullOr sub) split mergeDefs merge; });
        in
        inUnion (gm.mkOptionType (marked (gt.nullOr sub) notTwo))
        // {
          forgeRejected = run (np.either forge np.int) { a = 1; };
          forgeOtherMember = run (np.either forge np.int) 5;
        };
      expected = {
        rejected = "REFUSED";
        admitted = {
          a = 1;
          b = 0;
        };
        forgeRejected = "REFUSED";
        forgeOtherMember = 5;
      };
    };
    # a marked check over a gen submodule carrying `nullOr`'s merge
    test-nesting-forge = {
      expr = inUnion (gm.mkOptionType (marked (sub // { inherit (gt.nullOr sub) merge; }) notTwo));
      expected = {
        rejected = "REFUSED";
        admitted = {
          a = 1;
          b = 0;
        };
      };
    };
    # a marked check beside a `verify` copy of a gen container
    test-gen-verify-copy = {
      expr =
        let
          r = marked (gt.nullOr sub // { verify = _: null; }) notTwo;
        in
        {
          defineType = inUnion (gt.defineType r);
          mkOptionType = inUnion (gm.mkOptionType r);
        };
      expected =
        let
          one = {
            rejected = "REFUSED";
            admitted = {
              a = 1;
              b = 0;
            };
          };
        in
        {
          defineType = one;
          mkOptionType = one;
        };
    };
    # a marked check beside a `verify` copy of a nixpkgs container, re-homed as itself
    test-foreign-verify-copy = {
      expr = inUnion (gm.mkOptionType (marked (np.nullOr sub // { verify = _: null; }) notTwo));
      expected = {
        rejected = "REFUSED";
        admitted = {
          a = 1;
          b = 0;
        };
      };
    };
  };
}
