# Scores one modules.sh run (the slurped records) against the committed baseline ($base, its rows).
#
# An assertion's verdict is modules.sh's own, PASS or FAIL, except on a baseline row carrying `class`:
# there a FAIL whose evaluation refused (non-zero exit) with every literal of `class` in its stderr is
# PASS-CLASS — the refusal nixpkgs makes, in gen-merge's words (the owner's criterion is refusal CLASS,
# not text). A class names gen-merge's BY-NAME refusal, so one literal opens `gen-merge: `, and none
# carries a store path (the tree's path moves with every gen-merge revision). ONE class is the
# evaluator's, not gen-merge's: `["infinite recursion encountered"]`, the evaluator's own refusal of a
# cycle, which no engine raises by name. It is valid only on a row run with modules.sh's
# `REQUIRE_INFINITE_RECURSION_HINT` (env `RIRH`): there nixpkgs aborts on that cycle too, and the
# assertion also asks for nixpkgs' words around it (the context nixpkgs wraps its `config` argument
# in), which are text, not class. Since no `gen-merge: ` prefix marks it, it is matched as the
# evaluation's FINAL error line exactly, never as a substring: a named refusal quoting those words,
# or any other abort, stays FAIL.
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
# PERF, on the rows where nixpkgs serves (`checkConfigOutput`, `checkExpression`; a refusing evaluation
# writes no counters, so `checkConfigError` carries none): a record carries gen's `perf` and the reference
# run's `ref: {rc, verdict, perf}`, and `perf.<$ev>.gen.{thunks,bytes}` is an EXACT bound (ADR-0032), each
# clause `nixos-bar-compare.jq`'s over this register's id: above it is COST-REGRESSED, below it COST-RATCHET,
# no entry for $ev UNANCHORED, perf on another row INVALID-PERF; each is a disagreement.
#
# THE REFUSAL TEXT (den-hoag-pvy24), `nixos-bar-compare.jq`'s rule over this register's id: a FAIL or PASS-CLASS
# row whose gen evaluation refused (non-zero exit) records its last `error:` line, store paths `<store>`, per
# evaluator in `refusal.<$ev>`, written by `--fold` only; REFUSAL-MOVED and UNRECORDED-REFUSAL are disagreements.
#
# $mode "check" emits one line per disagreement and a summary · "perf" one `PERF modules-sh <json>` line per
# perf row, the line `--fold` reads · "write" the new baseline's verdicts, every perf entry the committed one's
# (`--fold` is the sole perf writer) · "fold" $base with
# $perf's lines merged in and $moves' IMPROVED verdicts adopted (all three evaluators, or refused).
def id: [.kind, .env, .argv] | tojson;
def dupsOf: group_by(.) | map(select(length > 1) | .[0]);
# counts: a perf entry's figures without its wall `ms`, which is recorded, never compared.
def counts: if type == "object" then map_values(if type == "object" then del(.ms) else . end) else . end;
def perfKind: .key.kind | IN("checkConfigOutput", "checkExpression");
def lastErr: (. // "") | split("\n") | map(select(test("^ *error:"))) | last // "(no error line)" | sub("^ +"; "");
def storeFree: gsub("/nix/store/[0-9a-z]{32}-[^/\\s'`\"):]*"; "<store>");
def refusalOf: if (.got == "FAIL" or .got == "PASS-CLASS") and .rc != 0 then .err | lastErr | storeFree else null end;
def validRefusal: .refusal == null or ((.refusal | type) == "object" and .verdict != "PASS"
  and (.refusal | to_entries | all(.value | type == "string" and (contains("/nix/store/") | not))));
def sortedObj: to_entries | sort_by(.key) | from_entries;
def parity: if .gen == null or .ref == null then null
  elif .gen.thunks <= .ref.thunks and .gen.bytes <= .ref.bytes then "at-parity" else "above-parity" end;
($ARGS.named.ev // "") as $ev
| ($ARGS.named.perf // []) as $perf
| if $mode == "fold" then
  ($perf | group_by(.key | id) | map({ key: (.[0].key | id), value: map({ key: .evaluator, value: { gen, ref } }) | from_entries }) | from_entries) as $P
  | ($base | map({ key: (.key | id), value: true }) | from_entries) as $ids
  | ($P | keys | map(select($ids[.] | not))) as $stray
  | if ($stray | length) > 0 then error("PERF lines for rows the register lacks: \($stray)") else . end
  # $refusals: the logs' REFUSAL lines, folded as `nixos-bar-compare.jq`'s fold folds them.
  | (($ARGS.named.refusals // []) | group_by(.key | id) | map({ key: (.[0].key | id), value: map({ key: .evaluator, value: .text }) | from_entries }) | from_entries) as $T
  | ($T | keys | map(select($ids[.] | not))) as $tstray
  | if ($tstray | length) > 0 then error("REFUSAL lines for rows the register lacks: \($tstray)") else . end
  | ($ARGS.named.cols // []) as $cols
  # $moves: the logs' verdict lines, adopted as `nixos-bar-compare.jq`'s fold adopts them.
  | ($base | map({ key: (.key | id), value: .verdict }) | from_entries) as $was
  | (($ARGS.named.moves // []) | map(select($was[.id] != null))) as $mine
  | ($mine | map(select(.word == "IMPROVED")) | group_by([.id, .was, .now])
      | map(select($ARGS.named.columns == 3 and (map(.col) | unique | length) == 3 and .[0].was == $was[.[0].id]))
      | map({ key: .[0].id, value: .[0].now }) | from_entries) as $V
  | ($mine | map(select(.word != "IMPROVED" or $V[.id] != .now) | .line) | unique) as $refused
  | if ($refused | length) > 0 then error("verdict lines --fold does not adopt (only an IMPROVED line from three distinct evaluators): \($refused)") else . end
  | $base[]
  # A column whose counts are the register's keeps its entry, so a fold moving no count is byte-stable.
  | if perfKind then (.perf // { }) as $o | .perf = ($o + (($P[.key | id] // { })
      | with_entries(if ($o[.key] | counts) == (.value | counts) then .value = $o[.key] else . end))) else . end
  | .verdict = ($V[.key | id] // .verdict)
  | (((.refusal // { }) | with_entries(select(.key as $k | $cols | index($k) | not))) + ($T[.key | id] // { }) | sortedObj) as $r
  | if .verdict == "PASS" or $r == { } then del(.refusal) else .refusal = $r end
  | tojson
else
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
          elif ($b.class // null) == ["infinite recursion encountered"] then
            (if $r.rc != 0 and ($r.err | split("\n") | map(select(test("^ *error:"))) | last // "" | sub("^ +"; ""))
                == "error: infinite recursion encountered"
             then "PASS-CLASS" else "FAIL" end)
          elif ($b.class // null) != null and $r.rc != 0 and ($b.class | all(. as $c | $r.err | contains($c))) then "PASS-CLASS"
          else "FAIL" end
        )
      }
  )) as $runs
| ($runs | map(.id)) as $seen
| if $mode == "perf" then
    ($runs[]
    | select(perfKind)
    | { gen: .perf, ref: .ref.perf } as $p
    | "PERF modules-sh " + ({ key, evaluator: $ev, gen: $p.gen, ref: $p.ref, parity: ($p | parity),
        ratio: (if ($p | parity) == null then null else { thunks: ($p.gen.thunks / $p.ref.thunks), bytes: ($p.gen.bytes / $p.ref.bytes) } end) } | tojson)),
    ([ $runs[] | refusalOf as $t | select($t != null) | { key, evaluator: $ev, text: $t } ] as $rs
      | ($rs[] | "REFUSAL modules-sh \(tojson)"), "REFUSALS modules-sh \($rs | length)")
  elif $mode == "write" then
    $runs
    | sort_by(.id)
    | map({ key, verdict: .got }
        + ((.base // { }) | with_entries(select(.key == "class" or .key == "overreach")))
        # Perf is the committed baseline's, never this run's: `--fold` is the sole perf writer (`nixos-bar-compare.jq`).
        + (if perfKind and .base.perf != null then { perf: .base.perf } else { } end)
        + (if .got != "PASS" and .base.refusal != null then { refusal: .base.refusal } else { } end))
    | .[]
    | tojson
  else
    (
      [ $dups[] | "DUPLICATE record \(.)" ]
      + [ $baseDups[] | "DUPLICATE baseline \(.)" ]
      + [ $base[] | select(.class != null)
          | select((.class | type) != "array"
              or ((.class | any(.[]; startswith("gen-merge: ")))
                or (.class == ["infinite recursion encountered"] and (.key.env | split(" ") | any(. == "RIRH")))
                | not)
              or (.class | any(.[]; contains("/nix/store/"))))
          | "INVALID-CLASS \(.key | id)" ]
      + [ $base[] | select(.class != null) | . as $b
          | [ $served[] | select(.err as $e | $b.class | all(. as $c | $e | contains($c))) | "L\(.line)" ] as $hits
          | if ($hits | length) > 0 and .overreach == null then "OVERREACH \($hits | join(",")) \(.key | id)"
            elif ($hits | length) == 0 and .overreach != null then "STALE-OVERREACH \(.key | id)"
            else empty end ]
      + [ $base[] | select(.class == null and .overreach != null) | "INVALID-CLASS overreach without class \(.key | id)" ]
      + [ $base[] | select(validRefusal | not) | "INVALID-REFUSAL \(.key | id)" ]
      + [ $runs[] | select(.base != null and .base.verdict == .got) | (refusalOf) as $t | (.base.refusal[$ev] // null) as $a
          | select($t != $a)
          | if $a == null then "UNRECORDED-REFUSAL L\(.line) \(.id) '\($t)' (fold the register in this change)"
            else "REFUSAL-MOVED L\(.line) \(.id) '\($a)' -> '\($t // "(no refusal)")' (fold the register in this change)" end ]
      + [ $runs[] | select(.base == null) | "UNBASELINED L\(.line) \(.got) \(.id)" ]
      + [ $runs[] | select(.base != null and .base.verdict != .got)
          | (if .got == "FAIL" then "REGRESSED" elif .base.verdict == "FAIL" then "IMPROVED" else "MOVED" end) + " L\(.line) \(.base.verdict) -> \(.got) \(.id)"
          + (if .got == "FAIL" then " || " + (.err | split("\n") | map(select(test("^ *error:"))) | last // "(no error line)" | ltrimstr(" ")) else "" end) ]
      + [ $base[] | select((.key | id) as $i | $seen | index($i) | not) | "MISSING \(.verdict) \(.key | id)" ]
      + [ $base[] | select(.perf != null and (perfKind | not)) | "INVALID-PERF \(.key | id)" ]
      + [ $runs[] | select(perfKind and .base != null) | . as $r
          | ($r.base.perf[$ev] // null) as $a
          | if $a == null then "UNANCHORED L\(.line) \(.id) has no perf entry for '\($ev)'"
            elif $a.gen == null or $r.perf == null then empty
            else
              "thunks \($a.gen.thunks) -> \($r.perf.thunks), bytes \($a.gen.bytes) -> \($r.perf.bytes)" as $d
              | if $r.perf.thunks > $a.gen.thunks or $r.perf.bytes > $a.gen.bytes then "COST-REGRESSED L\(.line) \(.id) \($d)"
                elif $r.perf.thunks < $a.gen.thunks or $r.perf.bytes < $a.gen.bytes then "COST-RATCHET L\(.line) \(.id) \($d) (lower the bound in this change)"
                else empty end
            end ]
    ) as $bad
    | ($bad[]),
      "modules-sh: \($runs | length) assertions, baseline \($base | length): \([$runs[] | select(.got == "PASS")] | length) PASS, \([$runs[] | select(.got == "PASS-CLASS")] | length) PASS-CLASS, \([$runs[] | select(.got == "FAIL")] | length) FAIL; \($bad | length) disagreements"
  end
end
