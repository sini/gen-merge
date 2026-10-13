# A stamped record a published door returns as itself, stating a `verify` over a module set below it, faces
# nixpkgs' evaluation (`interface.rebuildClosed.door`, den-hoag-olrmz): its `verify` is read on the merged value
# where nixpkgs' `lib.evalModules` reads one, through every rebuild nixpkgs calls on it. A door output re-entered
# through a second door keeps one carriage, and its rebuild is published under `substSubModules` alone, so no
# reader compares one closure under two fields (a comparison that answers by evaluator). The union cells state
# ADR-0039's (b′) law for a door copy as a member of an overlapping nixpkgs union: the first member whose merge
# states no `headError` over the definitions, nixpkgs' own v2 `either` / `oneOf` rule. Each cell is red with its
# site reverted (`door`, `carried`, `rebuilt`), and the re-doored cells are red on Lix alone where `carried`
# publishes its closure under both fields.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    any
    attrValues
    concatMap
    isAttrs
    listToAttrs
    ;
  # "np": nixpkgs' `evalModules` over the gen-published records; "gen": gen-merge's `evalModuleTree`
  run =
    en: ts: dv:
    let
      mods =
        map (t: { options.x = (if en == "gen" then gm.mkOption else nl.mkOption) { type = t; }; }) ts
        ++ map (v: { x = v; }) dv;
      c =
        if en == "gen" then
          (gm.evalModuleTree { } mods).config
        else
          (nl.evalModules { modules = mods; }).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  sub =
    key:
    gt.submodule {
      inherit key;
      options.a = gm.mkOption {
        type = gt.int;
        default = 0;
      };
      options.b = gm.mkOption {
        type = gt.int;
        default = 0;
      };
    };
  verifying =
    limit: t:
    t
    // {
      # the member `a`, of the value or of an attrset member of it
      verify =
        v:
        if isAttrs v && any (m: isAttrs m && (m.a or 0) == limit) ([ v ] ++ attrValues v) then
          "a must not be ${toString limit}"
        else
          null;
    };

  # the overlapping union: X = a door's copy of a gen submodule whose `verify` rejects a = 20, Y admits every
  # attrset of ints
  gSub = sub "ffd-law";
  Y = np.attrsOf np.int;
  doors = {
    defineType = gt.defineType;
    mkOptionType = gm.mkOptionType;
  };
  unions = {
    either = x: np.either x Y;
    oneOf =
      x:
      np.oneOf [
        x
        Y
      ];
  };
  poss = {
    root = {
      mk = t: t;
      w = v: v;
      r = v: v;
    };
    host = {
      mk = t: np.submodule { options.y = nl.mkOption { type = t; }; };
      w = v: { y = v; };
      r = v: v.y;
    };
  };
  # A: the union declared once; TL: the union over the plain base, then the union over the copy; LL: the union over
  # the copy, twice
  arrs = {
    A = plain: x: [ x ];
    TL = plain: x: [
      plain
      x
    ];
    LL = plain: x: [
      x
      x
    ];
  };
  lawCell =
    d: u: p: a: en:
    let
      P = poss.${p};
      ts = arrs.${a} (P.mk (unions.${u} gSub)) (P.mk (unions.${u} (doors.${d} (verifying 20 gSub))));
      read =
        defs:
        let
          v = run en ts (map P.w defs);
        in
        if v == "REFUSED" then v else P.r v;
    in
    {
      name = "test-b-prime-${d}-${u}-${p}-${a}-${en}";
      value = {
        expr = {
          # the value oracle: X's merge where X admits, Y's where X's `verify` rejects the merged value
          admitted = read [ { a = 1; } ];
          rejected = read [ { a = 20; } ];
          # the check oracle: refused where both members reject
          neither = read [ { a = "s"; } ];
          neitherSplit = read [
            { a = 20; }
            { c = true; }
          ];
        };
        expected = {
          admitted = {
            a = 1;
            b = 0;
          };
          rejected.a = 20;
          neither = "REFUSED";
          neitherSplit = "REFUSED";
        };
      };
    };
  each = xs: f: concatMap f (builtins.attrNames xs);
  # a stamped container the door returns as itself (no `carriedCopy` admission): its base's identity fields removed
  # but its completion stamp kept, and a `verify` stated, as gen-schema's `refined` over a container builds it
  asItself =
    base: limit:
    gm.mkOptionType (
      verifying limit (
        removeAttrs base [
          "functor"
          "typeMerge"
          "__mint"
          "__okAt"
          "__payload"
          "__sealed"
        ]
      )
    );
in
{
  flake.tests.foreign-facing-door =
    listToAttrs (
      each doors (
        d:
        each unions (
          u:
          each poss (
            p:
            each arrs (
              a:
              map (lawCell d u p a) [
                "np"
                "gen"
              ]
            )
          )
        )
      )
    )
    // {
      # a gen container of a module set the door returns as itself, declared in nixpkgs' evaluation: its merge reads
      # the `verify` on the merged value, and so does the rebuild nixpkgs calls at the fixup
      test-a-container-a-door-returns-as-itself-reads-its-verify-in-nixpkgs-evaluation =
        let
          N = asItself (gt.nullOr (sub "ffd-as-itself")) 2;
          A = asItself (gt.attrsOf (sub "ffd-as-itself")) 2;
        in
        {
          expr = {
            nullOrBad = run "np" [ N ] [ { a = 2; } ];
            nullOrOk = run "np" [ N ] [ { a = 1; } ];
            attrsOfBad = run "np" [ A ] [ { k.a = 2; } ];
            attrsOfOk = run "np" [ A ] [ { k.a = 1; } ];
          };
          expected = {
            nullOrBad = "REFUSED";
            nullOrOk = {
              a = 1;
              b = 0;
            };
            attrsOfBad = "REFUSED";
            attrsOfOk.k = {
              a = 1;
              b = 0;
            };
          };
        };
      # a door output re-entered through `mkOptionType`, declared once: the second door re-carries the first's
      # carriage, and its rebuild, published under `substSubModules` alone, reads the `verify` on every evaluator
      test-a-door-output-re-entered-through-a-door-refuses-what-its-verify-rejects =
        let
          S = verifying 2 (sub "ffd-redoor");
          viaDefineType = gm.mkOptionType (gt.defineType S);
          viaMkOptionType = gm.mkOptionType (gm.mkOptionType S);
        in
        {
          expr = {
            defineTypeBad = run "np" [ viaDefineType ] [ { a = 2; } ];
            defineTypeOk = run "np" [ viaDefineType ] [ { a = 1; } ];
            mkOptionTypeBad = run "np" [ viaMkOptionType ] [ { a = 2; } ];
            mkOptionTypeOk = run "np" [ viaMkOptionType ] [ { a = 1; } ];
            genBad = run "gen" [ viaDefineType ] [ { a = 2; } ];
          };
          expected = {
            defineTypeBad = "REFUSED";
            defineTypeOk = {
              a = 1;
              b = 0;
            };
            mkOptionTypeBad = "REFUSED";
            mkOptionTypeOk = {
              a = 1;
              b = 0;
            };
            genBad = "REFUSED";
          };
        };
    };
}
