# A `defineType` return's join under nixpkgs' `lib.evalModules` meets each declaration it has folded, at its top-level
# check and, over a module set, at every depth (ADR-0039 THE MEET; the converse: a gen `typeMerge` called inside
# nixpkgs' evaluation is gen's code; den-hoag-pfbow). nixpkgs reverses a redeclaration's list and hands the receiver
# only each partner's functor, so the door's return names itself there (`functor.__declared`) and its `typeMerge`
# meets the named partners, kept by the met record at every later join. Not met, and open: an element check inside a
# nixpkgs container, a widened operand's check inside a module set, and a met record an author redeclares; no cell
# here pins their served values.
# Cells, each mounted in nixpkgs' `lib.evalModules` with every declaration through `defineType`:
#  - the CHECK cells: a checked declaration before an unchecked one (the receiver), for a nixpkgs `attrTag` leaf, a
#    foreign self-returning leaf (`K`), and `K` inside an `attrTag`; a definition the check rejects is refused, one it
#    admits is served with the all-nixpkgs twin's value; `K` declared checked between two unchecked declarations holds a
#    later join;
#  - the UNION cells (reading 1, enum extension stays a union): two enums joined in either order serve a member of each;
#  - the RELATIVISED cells (reading 2): a check over an enum is owed relative to its own parameters, so a value it
#    rejects inside them is refused and one outside them is served;
#  - the VERIFY cells: a caller's `verify` declared before a checked partner is refused on what it rejects;
#  - the RESIDUE cell: a constant constructor's own record (`int`) crosses the door as itself, so a join it receives is
#    nixpkgs' `defaultTypeMerge`, and the earlier declaration's check is nixpkgs' drop (ADR-0039 "Not covered"). Pinned
#    to the twin's answer: nixpkgs' own drop, not correct behaviour.
# Red: the check, verify and later-join cells with the return naming no declaration and the join meeting only its own
# (the base's `close`); the union cells with the named partners carried whole (`carryBy`); `union-ab-a`, `union-ba-b`
# and `relativised-cb-c` with the receiver's own check carried whole (the base's `close`, beside the partners met).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  np = nl.types;
  run =
    ts: v:
    let
      c =
        (nl.evalModules {
          modules = map (t: { options.x = nl.mkOption { type = gm.types.defineType t; }; }) ts ++ [
            { x = v; }
          ];
        }).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  sub = np.submodule {
    options.a = nl.mkOption {
      type = np.str;
      default = "x";
    };
  };
  tag =
    b:
    np.attrTag {
      a = nl.mkOption { type = sub; };
      b = nl.mkOption { type = b; };
    };
  notOne = v: v != 1;
  # a foreign leaf whose `typeMerge` hands itself back as written; `Kc` is it with a check
  K =
    let
      k =
        nl.mkOptionType {
          name = "kint";
          check = builtins.isInt;
          merge = nl.mergeEqualOption;
          functor = {
            name = "kint";
            type = null;
            wrapped = null;
            payload = { };
            binOp = _: _: null;
          };
        }
        // {
          typeMerge = _: k;
        };
    in
    k;
  Kc = K // {
    check = v: K.check v && notOne v;
    functor = K.functor // {
      payload.keep = true;
    };
  };
  ic = np.addCheck np.int notOne;
  ea = np.enum [ "a" ];
  eb = np.enum [ "b" ];
  ca = np.addCheck (np.enum [
    "a"
    "c"
  ]) (v: v != "a");
  V = np.int // {
    verify = v: if v <= 5 then null else "must be at most 5";
  };
  cell = ts: v: expected: {
    expr = run ts v;
    inherit expected;
  };
in
{
  flake.tests.door-join-meets-partner = {
    test-check-tag-rejected = cell [ (tag ic) (tag np.int) ] { b = 1; } "REFUSED";
    test-check-tag-admitted = cell [ (tag ic) (tag np.int) ] { b = 2; } { b = 2; };
    test-check-K-rejected = cell [ Kc K ] 1 "REFUSED";
    test-check-K-admitted = cell [ Kc K ] 2 2;
    test-check-Ktag-rejected = cell [ (tag Kc) (tag K) ] { b = 1; } "REFUSED";
    test-check-Ktag-admitted = cell [ (tag Kc) (tag K) ] { b = 2; } { b = 2; };
    test-threaded-K-rejected = cell [ K Kc K ] 1 "REFUSED";
    test-threaded-K-admitted = cell [ K Kc K ] 2 2;
    test-union-ab-a = cell [ ea eb ] "a" "a";
    test-union-ab-b = cell [ ea eb ] "b" "b";
    test-union-ba-a = cell [ eb ea ] "a" "a";
    test-union-ba-b = cell [ eb ea ] "b" "b";
    test-relativised-cb-a = cell [ ca eb ] "a" "REFUSED";
    test-relativised-cb-b = cell [ ca eb ] "b" "b";
    test-relativised-cb-c = cell [ ca eb ] "c" "c";
    test-relativised-bc-a = cell [ eb ca ] "a" "REFUSED";
    test-relativised-bc-c = cell [ eb ca ] "c" "c";
    test-verify-rejected = cell [ V ic ] 7 "REFUSED";
    test-verify-check-rejected = cell [ ic V ] 1 "REFUSED";
    test-verify-admitted = cell [ V ic ] 3 3;
    test-residue-constant-constructor = cell [ ic np.int ] 1 1;
  };
}
