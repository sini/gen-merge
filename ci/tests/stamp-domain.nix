# gen-merge: what a completion's identity covers (`__stampReads`, den-hoag-6d5r3). gen-types' member tag
# compares a minted member with the record its completion returned over these fields only, so forcing a
# container's mark evaluates neither a submodule's module set (`unroledNested`, `description`: the a0c4z
# rule) nor a caller's cell, while a member whose `verify` was replaced by a `//` still enters sealed.
{ genMerge, ... }:
let
  t = genMerge.types;
  # each aborts when evaluated, uncatchably: the stamp's comparison tolerates a catchable throw in a
  # cell (it reads two undefined cells as agreeing), so a `throw` here would not show the force
  tripwire = t.submodule ({ ... }: abort "stamp-domain: the module set was evaluated");
  heavy = t.defineType (t.int // { extraCell = abort "stamp-domain: a caller cell was forced"; });
  marks = x: (builtins.tryEval (builtins.deepSeq x.__mint.minted true)).success;
in
{
  flake.tests.stamp-domain = {
    # RED with the domain unstated (every field compared) or with `unroledNested` in it
    test-a-container-mark-forces-no-member-cell = {
      expr = map marks [
        (t.listOf tripwire)
        (t.attrsOf tripwire)
        (t.nullOr tripwire)
        (t.listOf (t.listOf tripwire))
        (t.listOf heavy)
      ];
      expected = [
        true
        true
        true
        true
        true
      ];
    };
    test-a-verify-copy-member-enters-sealed = {
      expr = builtins.attrNames (t.listOf (t.int // { verify = _: null; })).__sealed;
      expected = [ "members.0" ];
    };
    # metadata, restated or added, is outside the domain: the container keeps its identity
    test-a-metadata-copy-member-keeps-its-mark =
      let
        plain = (t.listOf t.int).__mint.minted;
      in
      {
        expr = map (m: (t.listOf (t.int // m)).__mint.minted == plain) [
          { description = "a count"; }
          { myTag = 1; }
        ];
        expected = [
          true
          true
        ];
      };
    test-the-domain-leaves-out-the-evaluated-field = {
      expr = builtins.elem "unroledNested" (t.int.__typeSelf null).__stampReads;
      expected = false;
    };
  };
}
