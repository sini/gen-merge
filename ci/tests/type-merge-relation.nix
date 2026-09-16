# C-4 — THE ENGINE'S DISPATCH BASIS, as a runnable cell rather than a text count.
#
# ★★ WHY THIS IS BEHAVIOURAL AND NOT A COUNT. The predicate it replaces asked for "the three-site
# count pinned as an in-suite assertion", which has three defensible readings — three sites, four
# fields, five counting `name` — and no read-versus-comment rule. A trigger whose value depends on
# which reading you take is not readable. This asks the engine a question instead:
#
#   Hand `mergeTypes` two GEN-NATIVE types carrying NO foreign-protocol field. Does it merge them?
#
# ★★★ THE CELL WAS RED BEFORE THE REWIRE, MEASURED, AND THAT IS THE HALF THAT MAKES IT AN ORACLE.
# Against the pre-rewire tree the gen-native pair answered `null` — `mergeTypes` read
# `a.typeMerge b.functor` and nothing else — while the control pair WITH foreign fields merged. A cell
# that was never red measures nothing.
#
# ★ ITS CONTROL READS THE DISPATCH BASIS RATHER THAN DETECTING BREAKAGE: the identical pair WITH
# foreign fields must STILL merge. If it stopped, the cell above would be reporting that the engine
# broke, not that its basis moved.
{
  genMergeCore,
  genMerge,
  genMergeWith,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  # Two gen-native types. `name` and `verify` are gen's own vocabulary; nothing here is a
  # foreign-protocol field, and that is the point of the fixture.
  genNative = {
    name = "port";
    verify = v: if builtins.isInt v then null else "not an int";
    typeMergeRel =
      other:
      if (other.name or null) == "port" then
        { merged = genNative; }
      else
        { refused = "types do not merge: 'port' and '${other.name or "<unnamed>"}'"; };
  };
  genNativeOther = genNative // {
    name = "hostname";
    typeMergeRel =
      other:
      if (other.name or null) == "hostname" then
        { merged = genNativeOther; }
      else
        { refused = "types do not merge: 'hostname' and '${other.name or "<unnamed>"}'"; };
  };

  # The same SHAPE wearing the foreign protocol and NOT the relation — the control's subject. The
  # relation is removed deliberately: a fixture built as `genNative // { typeMerge; functor; }`
  # carries BOTH, and would take the relation arm, so it would exercise the arm it is meant to be
  # the control for. (That precedence is correct and is pinned on its own below.)
  withForeign = removeAttrs genNative [ "typeMergeRel" ] // {
    typeMerge = _f: withForeign;
    functor = {
      name = "port";
      payload = { };
    };
  };

  # ── `attrs`: the one name at which two libraries' spellings MEET as merge operands ─────────────
  # `listOf`/`attrsOf` also collide in the published namespace, but their two spellings disagree in
  # their NAMES (`attrsOf` against `attrsOf<str>`), so the shadowed value can never be the partner of
  # the winning one. Here both sides are literally `attrs`, and so is the foreign module system's
  # own — which is why this type states its relation instead of taking the name-only default.
  gmAttrs = genMerge.types.attrs;
  # gen-types' `attrs`, PROTOCOL-COMPLETED by the library's own export path rather than hand-built,
  # and reached under a non-colliding key so the linkset does not shadow it with the strategy. Its
  # `.name` is still `attrs` — that is the whole hazard — and it carries no fold of its own.
  completedLeaf = (genMergeWith (genTypes // { attrsLeaf = genTypes.attrs; })).types.attrsLeaf;
  attrsAnswer =
    other:
    let
      a = gmAttrs.typeMergeRel other;
    in
    if a ? merged then "merged" else a.refused;

  # A type carrying BOTH, for the precedence cell.
  withBoth = genNative // {
    typeMerge = _f: throw "the foreign arm must not be reached when a relation is present";
    functor = {
      name = "port";
      payload = { };
    };
  };
in
{
  # C-4 ITSELF. Red before the rewire, green after; nothing else about the engine changed.
  flake.tests.type-merge-relation.test-c4-engine-merges-gen-native-types = {
    expr = (genMergeCore.mergeTypes genNative genNative) != null;
    expected = true;
  };

  # THE CONTROL: the foreign arm is untouched, so a pair carrying foreign fields still merges. This
  # is what makes the cell above a reading of the DISPATCH BASIS rather than of breakage.
  flake.tests.type-merge-relation.test-control-foreign-protocol-pair-still-merges = {
    expr = (genMergeCore.mergeTypes withForeign withForeign) != null;
    expected = true;
  };

  # THE RELATION IS PARTIAL, and its refusal is NAMED. A bare `null` says only that two types did
  # not merge; the reason says which two and why, which is what the declaration site needs when it
  # has to throw.
  flake.tests.type-merge-relation.test-relation-refuses-by-name = {
    expr = {
      refusedPairIsNull = genMergeCore.mergeTypes genNative genNativeOther == null;
      reasonIsNamed = genMergeCore.mergeTypesReason genNative genNativeOther;
    };
    expected = {
      refusedPairIsNull = true;
      reasonIsNamed = "types do not merge: 'port' and 'hostname'";
    };
  };

  # ★ THE RELATION IS ROW-FREE, and this is the cell that says so. nixpkgs asks
  # `a.typeMerge b.functor` — the second operand is a functor PAYLOAD, a row both sides must agree
  # on the shape of. The relation is handed THE OTHER TYPE, so a partner carrying no functor at all
  # is still a legible operand. Under the foreign arm that same partner is not.
  # ★ PRECEDENCE, PINNED RATHER THAN LEFT AS AN ACCIDENT. A type carrying BOTH a relation and the
  # foreign protocol takes the RELATION — gen-native first, foreign second. The fixture's
  # `typeMerge` throws, so a run that reached the foreign arm would abort rather than quietly
  # answer; the cell therefore fails loudly if the precedence is ever inverted.
  flake.tests.type-merge-relation.test-relation-takes-precedence-over-the-foreign-arm = {
    expr = (genMergeCore.mergeTypes withBoth withBoth) != null;
    expected = true;
  };

  # ★★ THE TWO-LEVEL RELATION, AND ITS FOUR FAILURES ARE CONJUNCTS OF ONE EXPECTED VALUE — two of
  # them read as success on their own. A relation matching on `.name` alone answers `merged` to both
  # foreign pairings, silently adopting a partner whose fold is not this one's. A relation refusing
  # every same-named partner refuses `attrs` against ITSELF, which breaks the ordinary case every
  # consumer hits and which no other cell in this suite would see. And collapsing the name mismatch
  # into the foldless branch reports "a partner named `attrs'" about a partner named `string' — which
  # is what the two controls read, on the same predicate in the same run.
  flake.tests.type-merge-relation.test-attrs-relation-discriminates-the-foldless-partner = {
    expr = {
      vsCompletedLeaf = attrsAnswer completedLeaf;
      vsForeign = attrsAnswer nixpkgsLib.types.attrs;
      vsSelf = attrsAnswer gmAttrs;
      controlStr = attrsAnswer genMerge.types.str;
      controlInt = attrsAnswer genMerge.types.int;
      # The two partners really are named `attrs`, so the pairings above are the collision this
      # relation exists for and not a name mismatch wearing its clothes.
      partnersAreBothNamedAttrs = [
        completedLeaf.name
        nixpkgsLib.types.attrs.name
      ];
    };
    expected = {
      vsCompletedLeaf = "`attrs' and a partner named `attrs' that states no fold of its own";
      vsForeign = "`attrs' and a partner named `attrs' that states no fold of its own";
      vsSelf = "merged";
      controlStr = "`attrs' and `string'";
      controlInt = "`attrs' and `int'";
      partnersAreBothNamedAttrs = [
        "attrs"
        "attrs"
      ];
    };
  };

  flake.tests.type-merge-relation.test-relation-takes-a-type-not-a-payload = {
    expr = {
      # the partner has no `functor` whatsoever, and the merge still answers
      partnerWithoutFunctor = (genMergeCore.mergeTypes genNative { name = "port"; }) != null;
      # CONTROL: the foreign arm cannot read that partner — it needs `b.functor`
      foreignArmCannot = genMergeCore.mergeTypes withForeign { name = "port"; } == null;
    };
    expected = {
      partnerWithoutFunctor = true;
      foreignArmCannot = true;
    };
  };
}
