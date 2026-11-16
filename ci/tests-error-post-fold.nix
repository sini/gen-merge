# `types.postFold`'s refusals, by name, in gen's engine: the error-plane half of `tests/post-fold.nix`, over the same
# cases (`tests/_fixtures/post-fold-cases.nix`). Each names what it refuses: a definition the element's check rejects,
# an `addCheck` over the constructor (which nixpkgs drops), an identity demanded of the sealed `g`, any redeclaration
# partner but the one construction, and a debt carried by a copy of the constructor redeclared beside it.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  c = import ./tests/_fixtures/post-fold-cases.nix { inherit genMerge genTypes nixpkgsLib; } "native";
  force = v: builtins.deepSeq v v;
  refuses = expr: msg: {
    expr = force expr;
    expectedError = {
      type = "ThrownError";
      inherit msg;
    };
  };
  rejectedBelow = "a definition is rejected by the check of another declaration of this option";
  notProduced = "conservativeEq: `postFold' is not the value its producer completed";
in
{
  flake.testsError.post-fold = {
    # ── checks: the element's check judges every definition; a foreign `addCheck` over the constructor is enforced
    test-a-definition-the-element-rejects-is-refused-by-name = refuses c.checkElemRejects "a definition for option `s\\.x\\.foo\\.j\\.k\\.a' is not of the expected type";
    test-an-addcheck-over-the-constructor-is-enforced-nested = refuses c.checkAddCheckRejects "a definition for option `s\\.x' is not of type";
    test-an-addcheck-over-the-constructor-is-enforced-at-the-root = refuses c.checkAddCheckRoot "a definition for option `s' is not of type";
    # the read key of a throwing definition throws catchably, as in the twin
    test-a-read-throwing-definition-throws = refuses c.poisonThrowRead "^poison-bar$";
    # ── identity: no identity is ever minted over `g`, alone or under a container
    test-idof-refuses-naming-fn = refuses c.idOfLeafPf "idOf: type 'postFold' has sealed component\\(s\\) 'fn' ";
    test-idof-refuses-naming-fn-and-its-member = refuses c.idOfRefuses "idOf: type 'postFold' has sealed component\\(s\\) 'fn', 'members\\.0'";
    # `typeEq` over two different `g`s asks the sealed comparison, which refuses rather than answer
    test-typeeq-over-another-g-refuses = refuses c.typeEqOtherG "conservativeEq: two declarations of 'postFold' mint one identity";
    # ── redeclaration: every partner but the one construction is refused by name, in either order and in A·B·A
    test-postfold-beside-its-plain-element-is-refused = refuses c.redeclLeafPfPlain "option `s' is declared with types that do not merge \\(`postFold' and `int'";
    test-the-plain-element-beside-postfold-is-refused = refuses c.redeclLeafPlainPf "option `s' is declared with types that do not merge \\(`int' and `postFold'\\)";
    test-two-gs-a-b-a-are-refused = refuses c.redeclLeafABA "conservativeEq: two declarations of 'postFold' mint one identity";
    test-two-gs-over-one-element-are-refused = refuses c.redeclTwo "conservativeEq: two declarations of 'postFold' mint one identity";
    test-postfold-beside-a-plain-chain-is-refused = refuses c.redeclVsPlain "option `s' is declared with types that do not merge \\(`postFold' and `lazyAttrsOf'";
    # where the element's own redeclaration is refused (a submodule whose option states a default), the
    # construction's is too, with the element's refusal
    test-a-construction-over-a-defaulted-submodule-is-refused-as-its-element = refuses (c.rdSub 2) "The option `s\\.a' in `<unknown-file>' is already declared in `<unknown-file>': both declarations state `default'";
    # ── the `rewrites` arm: a debt on a step above a redeclared constructor is met there, so a definition it rejects is
    # refused by name; an `addCheck` copy of the constructor redeclared beside it is a different partner, refused
    # whatever the definition (sealed regime: nixpkgs' twin silently drops `g`)
    test-a-debt-on-the-element-step-refuses-a-bad-definition-checked-first = refuses (c.rw.elemAB true) rejectedBelow;
    test-a-debt-on-the-element-step-refuses-a-bad-definition-checked-second = refuses (c.rw.elemBA true) rejectedBelow;
    test-a-debt-one-step-higher-refuses-a-bad-definition-checked-first = refuses (c.rw.topAB true) rejectedBelow;
    test-a-debt-one-step-higher-refuses-a-bad-definition-checked-second = refuses (c.rw.topBA true) rejectedBelow;
    test-a-checked-copy-of-the-constructor-first-is-refused-bad = refuses (c.rw.rootAB true) notProduced;
    test-a-checked-copy-of-the-constructor-first-is-refused-good = refuses (c.rw.rootAB false) notProduced;
    test-a-checked-copy-of-the-constructor-second-is-refused-bad = refuses (c.rw.rootBA true) notProduced;
    test-a-checked-copy-of-the-constructor-second-is-refused-good = refuses (c.rw.rootBA false) notProduced;
  };
}
