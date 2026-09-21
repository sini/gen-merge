# WHY the foreign type merge asks whether a structure bottoms out BEFORE handing it to a foreign
# `typeMerge` — and why the reading is an exit code rather than a test cell.
#
# ONE FIXTURE, ONE SWITCH. Every arm below self-merges the same foreign type through the same
# boundary binding. The only thing that varies is WHICH `importedMerge` the arm carries: the shipped
# one, which consults `importedDecidable` on both operands first, or `preImportedMerge`, which is the
# construction as it stood — `a.typeMerge b.functor`, unconditionally. An arm that simply removed the
# merge would separate "merge absent" from "merge present", which nobody disputes and which says
# nothing about the guard.
#
# WHY IT IS NOT A TEST. `types.json` is self-referential: `json.typeMerge json.functor` unfolds
# forever and the interpreter answers `stack overflow; max-call-depth exceeded` — an error that is
# NOT a `throw` and therefore ESCAPES `builtins.tryEval`, killing the runner instead of failing a
# cell. Neither nix-unit output can host it: `flake.tests`' asserter forces every cell and
# `flake.testsError` reads a thrown message that this arm never produces. The only instrument that
# reads the difference is the exit code of a separate evaluation, and the before/after PAIR only
# exists while both constructions are present — which is what this file keeps.
#
# The guarded arm's refusal IS a `throw` at the declaration site and its message is asserted where
# messages belong, in ci/tests-error.nix `foreign-selfmerge`; that the merge is CONTAINED at all is
# asserted in ci/tests/nixpkgs-protocol.nix. What is measured here is the property no cell can
# state: that the abort became catchable at all.
#
# ★ THIS FILE IS A DISCRIMINATOR A MAINTAINER RUNS, NOT A GATE. Nothing in `.github/workflows`
# invokes `ci/bench/`, exactly as nothing invokes `either-totality.sh`. It reds on demand, in one
# run, against a co-resident permanent seeded defect — which is the only arrangement in which the
# abort and its absence can be compared at all.
#
# RUN (per arm; the sweep is `selfmerge-totality.sh`):
#   nix-instantiate --eval --strict --json --argstr arm unguarded-json ./ci/bench/selfmerge-totality.nix
{
  arm ? "guarded-json",
}:
let
  fromLock =
    lockFile: name:
    let
      lock = builtins.fromJSON (builtins.readFile lockFile);
      node = lock.nodes.${name}.locked;
    in
    builtins.fetchTree (
      if node.type == "tarball" then
        { inherit (node) type url narHash; }
      else
        {
          inherit (node)
            type
            owner
            repo
            rev
            narHash
            ;
        }
    );
  rootLock = ../../flake.lock;
  # nixpkgs is the CI lock's, resolved BY PATH FROM ROOT rather than by the node's own name: the
  # node literally spelled `nixpkgs` in that file is a transitive decoy at a different revision.
  ciLock = ../flake.lock;
  ciLockData = builtins.fromJSON (builtins.readFile ciLock);
  nixpkgsSrc = fromLock ciLock ciLockData.nodes.${ciLockData.root}.inputs.nixpkgs;

  # Each library's own flake wires these; the bench reads the same locked revisions and applies the
  # same arguments, so it binds what `./ci` binds without going through a flake.
  prelude = import "${fromLock rootLock "gen-prelude"}/lib";
  genTypes = import "${fromLock rootLock "gen-types"}" { inherit prelude; };
  genMemo = import "${fromLock rootLock "gen-memo"}" { inherit prelude; };
  genScope = import "${fromLock rootLock "gen-scope"}" { inherit prelude; };
  core = import ../../lib/modules.nix {
    inherit prelude;
    priority = import ../../lib/priority.nix { inherit prelude; };
    memo = genMemo;
    scope = genScope;
  };
  gm = import ../../lib {
    inherit prelude;
    types = genTypes;
    memo = genMemo;
    scope = genScope;
  };
  interface = core.interface;

  nixpkgsLib = import "${nixpkgsSrc}/lib";
  t = nixpkgsLib.types;

  # THE PRE-GUARD MERGE, carried here rather than remembered. This is `lib/interface.nix`'s
  # `importedMerge` exactly as it stood before the decidability pre-check: the first type's
  # `typeMerge` applied to the second's functor, with nothing asked first. It is the permanent
  # seeded defect this file exists to keep co-resident with the fix.
  preImportedMerge = a: b: if a ? typeMerge && b ? functor then a.typeMerge b.functor else null;

  # The subject and its control. `json` is self-referential and its unfolding does not bottom out;
  # `number` is an ordinary two-member union whose does, and both reach the boundary by the same
  # route — neither carries a gen `typeMergeRel`.
  undecidable = t.json;
  decidable = t.number;

  read = v: if v == null then { merged = "NULL"; } else { merged = "MERGED name=${v.name}"; };
  catch =
    v:
    let
      r = builtins.tryEval (builtins.deepSeq v v);
    in
    {
      success = r.success;
    }
    // (if r.success then read v else { });
in
if arm == "guarded-json" then
  # THE CLAIM: the shipped boundary declines the call and answers its documented "not mergeable".
  read (interface.importedMerge undecidable undecidable)
else if arm == "unguarded-json" then
  # THE CONTROL, and it reproduces the WHOLE prior state. The same fixture through the same
  # boundary with the pre-check removed: no JSON to read, the exit code is the whole reading.
  read (preImportedMerge undecidable undecidable)
else if arm == "tryguard-json" then
  # CONTAINMENT: a consumer CAN defend against the shipped answer, because there is an answer.
  catch (interface.importedMerge undecidable undecidable)
else if arm == "tryunguarded-json" then
  # THE POINT OF THE WHOLE FILE. The identical `tryEval` over the pre-guard merge does NOT contain
  # it — the abort escapes the wrapper and takes the process. Without this arm the guard would be
  # indistinguishable from a defect a consumer could already have caught.
  catch (preImportedMerge undecidable undecidable)
else if arm == "guarded-number" then
  # POSITIVE CONTROL: a decidable foreign pair still reaches nixpkgs' own `typeMerge` and comes
  # back with a real merged type. Without it, `guarded-json`'s `NULL` is equally consistent with a
  # boundary that stopped merging anything.
  read (interface.importedMerge decidable decidable)
else if arm == "unguarded-number" then
  # The pre-guard construction is not merely broken — on a pair whose structure bottoms out it
  # returns, and returns what the shipped boundary returns. Without this, `unguarded-json`'s
  # non-zero exit would prove only that a hand-built merge is wrong.
  read (preImportedMerge decidable decidable)
else if arm == "tryunguarded-number" then
  # The catcher's control on the pre-guard construction itself: it catches fine here, so
  # `tryunguarded-json`'s exit is an escaping abort rather than a `tryEval` that stopped working.
  catch (preImportedMerge decidable decidable)
else if arm == "catchControl" then
  # The catcher's own positive control: a plain `throw` IS caught in this evaluation.
  catch (throw "selfmerge-totality: catcher control")
else if arm == "declaration-guarded" then
  # THE PUBLISHED SURFACE, not the internal binding: the ordinary redeclaration a consumer authors.
  # Under the guard it is a catchable `throw` naming the ceiling; the message itself is pinned in
  # ci/tests-error.nix, and what this arm reads is that the evaluation SURVIVES it.
  catch
    (gm.evalModuleTree {
      modules = [
        {
          _file = "a.nix";
          options.x = gm.mkOption { type = undecidable; };
        }
        {
          _file = "b.nix";
          options.x = gm.mkOption { type = undecidable; };
        }
      ];
    }).options.x.type.name
else
  throw "unknown arm"
