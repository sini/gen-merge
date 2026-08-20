# THE LOCK-AGREEMENT INVARIANT — this repository's two locks resolve THE SAME gen-types revision.
#
# ★★★ THE DEFECT THIS EXISTS FOR SHIPPED HERE, and it is not a hypothetical: the root lock pinned
# gen-types `887ad871` while the ci lock pinned `ad180dab` — two revisions of one input in one
# repository. The SUITE evaluates the ci pin, so every behavioural claim this repository's CI made
# about gen-types was evidence about a revision its consumers do not resolve. Nothing was red.
# A divergence between two locks is invisible to every cell that reads only one of them, which is
# every other cell here.
#
# ★★ WHY AN INVARIANT RATHER THAN A LANDING-TIME INSPECTION. A `jq` run at the reconciliation would
# have passed once and never run again, and the two locks drift through ORDINARY WORK — one bumped
# for a consumer's benefit, the other left, each change locally reasonable. The failure is not that
# someone did something wrong; it is that nothing was watching the pair. This cell watches the pair.
#
# ★ THE WALKER IS gen-link's, COPIED BYTE-FOR-BYTE (`_fixtures/lock-walk.nix`), because the question
# is the same one and a second implementation of it would be a second thing to be wrong. What it
# counts is DISTINCT NODES reached under an input carrying a label, walked from `.root` — never lock
# entries whose key spelling matches, since those carry nix's own `_2`/`_3` disambiguation suffixes
# and are an artefact of how the file was written down rather than a fact about the evaluation.
#
# Two questions, and they are genuinely different — a lock can resolve exactly one gen-types while
# the other lock resolves exactly one DIFFERENT gen-types, which is precisely what happened:
#   · WITHIN each lock: exactly one node under the label, so `.lib` is one value;
#   · ACROSS the two: those nodes are the same revision, so the suite's evidence is about the
#     revision a consumer of the root entry actually gets.
#
# Reading repository files from a cell is the move `purity.nix` next door already makes.
{
  lib,
  ...
}:
let
  walkOf = lock: import ./_fixtures/lock-walk.nix { inherit lib lock; };

  rootLock = builtins.fromJSON (builtins.readFile ../../flake.lock);
  ciLock = builtins.fromJSON (builtins.readFile ../flake.lock);

  # The REVISIONS the distinct gen-types nodes of a lock resolve to. Sorted and deduplicated, so the
  # answer is a property of the lock rather than of node-key ordering.
  revsUnder =
    lock: label:
    lib.unique (
      lib.sort (a: b: a < b) (
        map (k: lock.nodes.${k}.locked.rev or "<unlocked>") ((walkOf lock).distinctUnder label)
      )
    );

  # ── THE ARMING ──
  # A comparison between two locks that happen to be equal is a tautology until someone shows it can
  # come apart. Seeding a DIFFERENT revision onto the ci lock's gen-types node reproduces exactly the
  # shape that shipped, in memory, changing nothing on disk. The seed is a real revision of this same
  # input — the one the root lock actually carried during the divergence — rather than a nonsense
  # string, because a nonsense value could be caught by a well-formedness check that the real defect
  # would walk straight past.
  divergedRev = "887ad871d13f3baeb168a8cb5503b39737fe947b";
  seedDivergence =
    lock:
    let
      node = builtins.head ((walkOf lock).distinctUnder "gen-types");
    in
    lock
    // {
      nodes = lock.nodes // {
        ${node} = lock.nodes.${node} // {
          locked = lock.nodes.${node}.locked // {
            rev = divergedRev;
          };
        };
      };
    };

  # And the other direction: a lock reaching TWO distinct nodes under the label. The second edge has
  # to come from a DIFFERENT node — one node's `inputs` is an attrset and can carry only one
  # `gen-types` — which is exactly the shape the real hazard takes: a transitive dependency acquiring
  # its own gen-types through a door no `follows` here governs. The carrier is the node the root's
  # `gen-prelude` input names, and it is pointed at the root node itself: guaranteed present in any
  # lock, and guaranteed distinct from the gen-types node, so this seed works on either file without
  # knowing what else either one carries.
  seedSecondInstance =
    lock:
    let
      rootKey = lock.root;
      carrier = lock.nodes.${rootKey}.inputs."gen-prelude";
    in
    lock
    // {
      nodes = lock.nodes // {
        ${carrier} = lock.nodes.${carrier} // {
          inputs = (lock.nodes.${carrier}.inputs or { }) // {
            "gen-types" = rootKey;
          };
        };
      };
    };
in
{
  # WITHIN each lock: one node under the label, so `.lib` is one value rather than two that agree by
  # luck.
  flake.tests.lock-agreement.test-root-lock-resolves-one-gen-types = {
    expr = (walkOf rootLock).countUnder "gen-types";
    expected = 1;
  };
  flake.tests.lock-agreement.test-ci-lock-resolves-one-gen-types = {
    expr = (walkOf ciLock).countUnder "gen-types";
    expected = 1;
  };

  # ACROSS the two: the same revision. THIS is the cell the divergence would have failed, and it is
  # stated as an equality of the resolved revisions rather than of the two files, because the files
  # legitimately differ in everything else.
  flake.tests.lock-agreement.test-both-locks-resolve-the-same-gen-types = {
    expr = revsUnder rootLock "gen-types" == revsUnder ciLock "gen-types";
    expected = true;
  };

  # ★ THE COMPARISON IS SHOWN ABLE TO FAIL, in the same run, on the shape that actually shipped.
  flake.tests.lock-agreement.test-control-a-seeded-divergence-is-seen = {
    expr = revsUnder rootLock "gen-types" == revsUnder (seedDivergence ciLock) "gen-types";
    expected = false;
  };

  # ★ And the WITHIN-lock counter is shown able to move too, so a counter that reported 1 because it
  # could not see a second node would not pass this suite forever.
  flake.tests.lock-agreement.test-control-a-second-instance-is-counted = {
    expr = (walkOf (seedSecondInstance ciLock)).countUnder "gen-types";
    expected = 2;
  };

  # ★ The walker DISCRIMINATES: a label no input carries reaches nothing. Without this row, a walk
  # that silently reached nothing at all would report 1 for no reason anyone could see.
  flake.tests.lock-agreement.test-control-an-absent-label-reaches-nothing = {
    expr = (walkOf ciLock).countUnder "not-an-input-of-anything";
    expected = 0;
  };

  # ★ A wrongly rooted walk REFUSES rather than reporting zero for every label, which is the reading
  # that would look exactly like a held invariant.
  flake.tests.lock-agreement.test-control-a-wrongly-rooted-walk-refuses = {
    expr =
      (builtins.tryEval ((walkOf (ciLock // { root = "no-such-node"; })).countUnder "gen-types")).success;
    expected = false;
  };
}
