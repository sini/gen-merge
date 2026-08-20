# WHY a union's merge consults EVERY definition before choosing a member — and why the reading is an
# exit code rather than a test cell.
#
# ONE FIXTURE, ONE SWITCH. Every arm below declares the same option at the same path over the same
# member pair (`listOf str` | `str`) and defines it from the same named files. The only thing that
# varies is WHICH merge the type carries: the shipped one, which picks the member that accepts every
# definition, or `preEither`, which picks from the FIRST definition and merges the rest through it.
# An arm that simply removed the union would separate "union absent" from "union present", which
# nobody disputes and which says nothing about the rule.
#
# WHY IT IS NOT A TEST. The pre-remediation merge hands the definition its chosen member cannot
# consume to the interpreter, which answers `expected a list but found a string: "b"` — an error that
# is NOT a `throw` and therefore ESCAPES `builtins.tryEval`, killing the runner instead of failing a
# cell. Neither nix-unit output can host it: `flake.tests`' asserter forces every cell and
# `flake.testsError` reads a thrown message that this arm never produces. The only instrument that
# reads the difference is the exit code of a separate evaluation, and the before/after PAIR only
# exists while both constructions are present — which is what this file keeps.
#
# The remediated arm's refusal IS a `throw` and its message is asserted where messages belong, in
# ci/tests-error.nix `union-merge`. What is measured here is the property no cell can state: that the
# abort became catchable at all.
#
# RUN (per arm; the sweep is `either-totality.sh`):
#   nix-instantiate --eval --strict --json --argstr arm pre ./ci/bench/either-totality.nix
{
  arm ? "shipped",
}:
let
  fromLock =
    name:
    let
      lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
      node = lock.nodes.${name}.locked;
    in
    builtins.fetchTree {
      inherit (node)
        type
        owner
        repo
        rev
        narHash
        ;
    };
  # Each library's own flake wires these; the bench reads the same locked revisions and applies the
  # same arguments, so it binds what `./ci` binds without going through a flake.
  prelude = import "${fromLock "gen-prelude"}/lib";
  genTypes = import "${fromLock "gen-types"}/lib" { inherit prelude; };
  gm = import ../../lib {
    inherit prelude;
    types = genTypes;
  };
  t = gm.types;

  # The member pair, fixed for every arm. Each member accepts exactly what the other rejects, so a
  # definition set mixing them is one no single member can take whole.
  memberA = t.listOf t.str;
  memberB = t.str;

  # `isValid` as lib/types.nix computes it — a gen-types leaf's `verify` first, then a structural
  # type's own `check`. Restated here because the constructions below are this file's and must not
  # borrow a binding the library could change underneath them.
  isValid =
    ty: v:
    if ty ? verify then
      ty.verify v == null
    else if ty ? check then
      ty.check v
    else
      true;

  # THE MEMBERS' ANSWERS AS THEY WERE, and this is exact for this pair rather than a general
  # restatement: `str` answered through `verify` then as now, and `listOf` carried no domain of its
  # own, so the completion THEN IN `lib/types.nix` handed it `_: true` and the union's dispatch was
  # told it accepted the string too. That construct no longer exists — the completion is now
  # `lib/interface.nix` `exportType`, and a container states its domain as `admits` — but this arm
  # reproduces the answers of the revision the defect was measured at, so it is stated as history
  # rather than repointed at a construct that would answer differently.
  preIsValid = ty: v: if ty ? verify then ty.verify v == null else true;

  # THE PRE-REMEDIATION MERGE, carried here rather than remembered: the member comes from the FIRST
  # definition's shape and every definition is then merged through it. Parameterised by the
  # membership answer, because the two halves of the rule are separable and the sweep separates them.
  preEither =
    valid:
    gm.mkOptionType {
      name = "eitherPre";
      check = v: valid memberA v || valid memberB v;
      merge =
        loc: defs:
        gm.mergeDefs loc (
          if defs != [ ] && valid memberA (builtins.head defs).value then memberA else memberB
        ) defs;
    };

  # One definition per named file, so a refusal has files to name and the two constructions are
  # compared over identical input.
  valueOf =
    ty: values:
    (gm.evalModuleTree {
      modules = [
        {
          _file = "decl.nix";
          options.x = gm.mkOption { type = ty; };
        }
      ]
      ++ prelude.imap0 (i: v: {
        _file = "def${toString i}.nix";
        config.x = v;
      }) values;
    }).config.x;

  # THE DEFINITION SET IS ONE SET IN TWO AUTHORED ORDERS, and the order matters to the arms below
  # for a reason worth stating: the fold hands a merge its definitions in the REVERSE of authored
  # order, so which member the pre-remediation dispatch picks from "the first definition" depends on
  # which module wrote last. `mixed` is the bead's fixture; `mixedListLast` is the same set authored
  # the other way round, which is the order that still defeats the old dispatch once the members
  # answer honestly.
  mixed = [
    [ "a" ]
    "b"
  ];
  mixedListLast = [
    "b"
    [ "a" ]
  ];
  homogeneous = [
    [ "a" ]
    [ "b" ]
  ];

  catch = v: {
    caught = !(builtins.tryEval (builtins.deepSeq v v)).success;
  };
in
if arm == "shipped" then
  # THE CLAIM: the mixed set is refused by a `throw`, so the catcher sees it and the evaluation ends.
  catch (valueOf (t.either memberA memberB) mixed)
else if arm == "shippedListLast" then
  # The same set authored the other way round: a union's answer about a definition SET does not
  # depend on which module wrote last, so this arm reads identically to the one above.
  catch (valueOf (t.either memberA memberB) mixedListLast)
else if arm == "pre" then
  # THE CONTROL, and it reproduces the WHOLE prior state — the old dispatch AND the members'
  # then-answers. The same set escapes the same catcher.
  catch (valueOf (preEither preIsValid) mixed)
else if arm == "preCurrentChecks" then
  # THE DISCRIMINATOR BETWEEN THE RULE'S TWO HALVES. The members answer honestly here — only the
  # DISPATCH is the old one — and the abort is still reachable: picking from the first definition
  # picks the list member for this order and then hands it the string. Without this arm the sweep
  # would be consistent with the members' new checks carrying the whole rule and the dispatch change
  # being decorative.
  catch (valueOf (preEither isValid) mixedListLast)
else if arm == "shippedHomogeneous" then
  { value = valueOf (t.either memberA memberB) homogeneous; }
else if arm == "preHomogeneous" then
  # The POSITIVE CONTROL on the pre-remediation construction: it is not merely broken — on a set its
  # chosen member takes whole it returns, and returns what the shipped union returns. Without this,
  # `pre`'s non-zero exit would prove only that something in a hand-built type is wrong.
  { value = valueOf (preEither preIsValid) homogeneous; }
else if arm == "catchControl" then
  # The catcher's own positive control: a plain `throw` IS caught here, so `pre`'s exit is an
  # escaping abort rather than a `tryEval` that stopped working.
  catch (throw "either-totality: catcher control")
else
  throw "unknown arm"
