# A construction's certificate (`typeMergeRel.exact`) excuses an operand only where the answer carries it: the
# answer is the operand's own construction (its check witness), or a join stating parameters. These are the
# values every declaration admits, served unchanged: one construction declared twice, a `//` copy keeping its
# witness, and an author record or a same-name `defineType` beside gen's `int`. The values one declaration's own
# check rejects are pinned on the error plane (`ci/tests-error.nix`, `author-check-certification`).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  t = genMerge.types;
  np = nixpkgsLib.types;
  gen =
    ts: v:
    let
      x =
        (genMerge.evalModuleTree { } (
          map (ty: { options.x = genMerge.mkOption { type = ty; }; }) ts ++ [ { x = v; } ]
        )).config.x;
    in
    builtins.deepSeq x x;
  isInt = builtins.isInt;
  author = c: {
    name = "int";
    check = c;
    merge = np.int.merge;
  };
  borrowing = c: np.mkOptionType (author c) // { inherit (t.int) typeMergeRel; };
  auth = author (v: isInt v && v < 3);
  T = t.defineType auth;
  Tc = t.defineType (author (v: isInt v && v != 4));
  Td = t.defineType (author (v: isInt v && v != 7));
in
{
  flake.tests.author-check-certification = {
    test-a-borrowed-relation-serves-a-value-every-check-admits = {
      expr = gen [
        t.int
        (borrowing (v: isInt v && v < 3))
      ] 1;
      expected = 1;
    };
    test-a-borrowed-relation-through-definetype-serves-a-value-its-check-admits = {
      expr = gen [ (t.defineType (borrowing (v: isInt v && v < 3))) ] 1;
      expected = 1;
    };
    test-a-same-name-definetype-serves-a-value-every-check-admits = {
      expr = gen [
        T
        t.int
      ] 1;
      expected = 1;
    };
    test-two-same-name-definetypes-serve-a-value-both-checks-admit = {
      expr = gen [
        Tc
        Td
      ] 1;
      expected = 1;
    };
    test-gen-int-and-its-description-copy-serve-as-one-construction = {
      expr = gen [
        t.int
        (t.int // { description = "an int"; })
      ] 1;
      expected = 1;
    };
    test-a-definetype-and-its-description-copy-serve-as-one-construction = {
      expr = gen [
        T
        (T // { description = "d"; })
      ] 1;
      expected = 1;
    };
    test-two-borrowed-relations-serve-a-value-both-author-checks-admit = {
      expr = gen [
        (borrowing (v: isInt v && v != 7))
        (borrowing (v: isInt v && v != 4))
      ] 1;
      expected = 1;
    };
  };
}
