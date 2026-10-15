# A WRAPPER beside its own BARE BASE: one option declared once as a record that `wraps` gen's `int` (and
# refines it, admitting only values above 3) and once as `int` itself. The meet of a refinement with its
# own base is the refinement (`{v:B | e} ⊓ B = {v:B | e}`), and only the wrapper's relation knows what it
# adds, so whichever operand gen's dispatch would ask first, the wrapper's relation answers: gen's relation
# dispatch and its veto (`lib/modules.nix`), and the foreign entry where nixpkgs' engine asks the bare
# base (`exportTypeWith`'s `typeMerge`). The wrapper here is local to the suite; gen-schema's `refined` is
# the published one.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gt = genMerge.types;
  base = gt.int;
  wrapper = genMerge.mkOptionType (
    gt.mkIdentity "above3" [ base ] (tags: { base = builtins.head tags; }) [ ] "above3<int>"
    // {
      name = "int";
      description = "an integer above 3";
      verify = v: if !(base.check v) then "not an int" else if v > 3 then null else "must be above 3";
      functor = {
        name = "above3<int>";
        type = _: wrapper;
        payload = { };
        binOp = _: _: null;
      };
      # over one base the meet is this type: the base's own relation decides whether the partner joins
      typeMerge = f: if base.typeMerge f == null then null else wrapper;
      wraps = base;
    }
  );
  # a re-doored copy of the wrapper whose own `verify` also rejects 5
  copy = gt.defineType (
    wrapper
    // {
      verify = v: if v == 5 then "is 5" else wrapper.verify v;
    }
  );
  engines = {
    gen = {
      mkOption = genMerge.mkOption;
      eval = mods: genMerge.evalModuleTree { } mods;
    };
    nixpkgs = {
      mkOption = nixpkgsLib.mkOption;
      eval = mods: nixpkgsLib.evalModules { modules = mods; };
    };
  };
  declare = e: map (ty: { options.x = engines.${e}.mkOption { type = ty; }; });
  attempt =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then toString r.value else "R";
  # what `x = 4`, `x = 5` and `x = 3` read, `R` refused
  values =
    e: ts:
    builtins.concatStringsSep "," (
      map (v: attempt (engines.${e}.eval (declare e ts ++ [ { x = v; } ])).config.x) [
        4
        5
        3
      ]
    );
  # both engines, both orders
  orders = f: a: b: {
    gen = [
      (f "gen" [ a b ])
      (f "gen" [ b a ])
    ];
    nixpkgs = [
      (f "nixpkgs" [ a b ])
      (f "nixpkgs" [ b a ])
    ];
  };
  both = v: {
    gen = [
      v
      v
    ];
    nixpkgs = [
      v
      v
    ];
  };
  constructor = e: ts: attempt (engines.${e}.eval (declare e ts)).options.x.type.functor.name;
in
{
  test-a-wrapper-beside-its-bare-base-is-the-wrapper = {
    expr = orders constructor wrapper base;
    expected = both "above3<int>";
  };
  test-a-wrapper-beside-its-bare-base-serves-what-both-accept-and-refuses-what-it-rejects = {
    expr = orders values wrapper base;
    expected = both "4,5,R";
  };
  # the deferral meets the wrapper's answer with the copy's own declaration, so the copy's `verify` is kept
  test-a-re-doored-copy-of-the-wrapper-keeps-its-own-verify-beside-the-bare-base = {
    expr = orders values copy base;
    expected = both "4,R,R";
  };
  # a pair with no wrapper is decided as before
  test-control-int-beside-int-is-unchanged = {
    expr = orders values base base;
    expected = both "4,5,3";
  };
}
