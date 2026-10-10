# Scores one modules.sh run (the slurped records) against the committed baseline ($base, its rows).
#
# An assertion's verdict is modules.sh's own, PASS or FAIL, except on a baseline row carrying `class`:
# there a FAIL whose evaluation refused (non-zero exit) with every literal of `class` in its stderr is
# PASS-CLASS — the refusal nixpkgs makes, in gen-merge's words (the owner's criterion is refusal CLASS,
# not text). A class names gen-merge's BY-NAME refusal, so one literal opens `gen-merge: `, and none
# carries a store path (the tree's path moves with every gen-merge revision).
#
# PASS-CLASS is SOUND, NOT COMPLETE: a same-class refusal gen-merge raises in nixpkgs' words, or with a
# degraded field (`<unknown-file>`), cannot be pinned and stays FAIL. The bar undercounts, never over.
#
# OVER-REACH, checked on every run: a class literal that also fires on a row where nixpkgs SERVES (every
# non-`checkConfigError` assertion, which the reference passes) names a refusal gen-merge makes for some
# other reason there, so it may be a different reason here too. Such a row must carry `overreach`, the
# argument that its own cell is the same subject and the same rule (an eager refusal of the same
# conflict, say); without it the row is OVERREACH, and an `overreach` the run no longer needs is STALE.
# Its reach is a WITNESS test, not a same-reason proof: it sees a wrong-class literal only when the same
# wrong refusal also shows on a serve row. A literal that matches a different refusal on rows where
# nixpkgs refuses too is not caught here, so authoring a class stays a review judgement.
#
# $mode "check" emits one line per disagreement and a summary; "write" emits the new baseline.
def id: [.kind, .env, .argv] | tojson;
def dupsOf: group_by(.) | map(select(length > 1) | .[0]);
. as $recs
| ($base | map({ key: (.key | id), value: . }) | from_entries) as $B
| ($recs | map(.key | id) | dupsOf) as $dups
| ($base | map(.key | id) | dupsOf) as $baseDups
| [ $recs[] | select(.key.kind != "checkConfigError" and .rc != 0) ] as $served
| ($recs | map(
    . as $r
    | ($B[$r.key | id] // null) as $b
    | $r + {
        id: ($r.key | id),
        base: $b,
        got: (
          if $r.verdict == "PASS" then "PASS"
          elif ($b.class // null) != null and $r.rc != 0 and ($b.class | all(. as $c | $r.err | contains($c))) then "PASS-CLASS"
          else "FAIL" end
        )
      }
  )) as $runs
| ($runs | map(.id)) as $seen
| if $mode == "write" then
    $runs
    | sort_by(.id)
    | map({ key, verdict: .got } + ((.base // { }) | with_entries(select(.key == "class" or .key == "overreach"))))
    | .[]
    | tojson
  else
    (
      [ $dups[] | "DUPLICATE record \(.)" ]
      + [ $baseDups[] | "DUPLICATE baseline \(.)" ]
      + [ $base[] | select(.class != null)
          | select((.class | type) != "array" or (.class | any(.[]; startswith("gen-merge: ")) | not)
              or (.class | any(.[]; contains("/nix/store/"))))
          | "INVALID-CLASS \(.key | id)" ]
      + [ $base[] | select(.class != null) | . as $b
          | [ $served[] | select(.err as $e | $b.class | all(. as $c | $e | contains($c))) | "L\(.line)" ] as $hits
          | if ($hits | length) > 0 and .overreach == null then "OVERREACH \($hits | join(",")) \(.key | id)"
            elif ($hits | length) == 0 and .overreach != null then "STALE-OVERREACH \(.key | id)"
            else empty end ]
      + [ $base[] | select(.class == null and .overreach != null) | "INVALID-CLASS overreach without class \(.key | id)" ]
      + [ $runs[] | select(.base == null) | "UNBASELINED L\(.line) \(.got) \(.id)" ]
      + [ $runs[] | select(.base != null and .base.verdict != .got)
          | (if .got == "FAIL" then "REGRESSED" elif .base.verdict == "FAIL" then "IMPROVED" else "MOVED" end) + " L\(.line) \(.base.verdict) -> \(.got) \(.id)"
          + (if .got == "FAIL" then " || " + (.err | split("\n") | map(select(test("^ *error:"))) | last // "(no error line)" | ltrimstr(" ")) else "" end) ]
      + [ $base[] | select((.key | id) as $i | $seen | index($i) | not) | "MISSING \(.verdict) \(.key | id)" ]
    ) as $bad
    | ($bad[]),
      "modules-sh: \($runs | length) assertions, baseline \($base | length): \([$runs[] | select(.got == "PASS")] | length) PASS, \([$runs[] | select(.got == "PASS-CLASS")] | length) PASS-CLASS, \([$runs[] | select(.got == "FAIL")] | length) FAIL; \($bad | length) disagreements"
  end
