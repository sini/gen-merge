# Scores one stage-2 run (the slurped cell records, `nixos-bar.bash`) against the committed register ($base,
# its rows), for the evaluator whose `--version` line is $ev.
#
# A record is `{key, claim?, ref, gen}`, an arm `{refused, v, err?, perf}` (null where the walk has no such
# node). The verdict is stage 1's (`modules-sh-compare.jq`):
#   PASS        both arms serve and their values are equal: the drvPath for toplevel / options, the
#               entry's JSON hash for a doc node; the docs-walk row is PASS iff both walks ran to the end
#   PASS-CLASS  both refuse, on a row whose committed `class` literals all occur in gen's refusal; a class
#               opens `gen-merge: ` and carries no store path, and OVER-REACH is read on every run against
#               the rows where nixpkgs serves and gen refuses (`modules-sh-compare.jq` gives the rule)
#   FAIL        everything else: unequal, gen refusing where nixpkgs serves, a node gen lacks, and gen
#               serving where nixpkgs refuses (FAIL until a (b') ruling names the cell, ADR-0039)
# A toplevel or options row carries `"claim":"identity"`: its PASS is one derivation's identity, evidence and
# never acceptance (ADR-0039). Only those two kinds carry it, and only perf rows carry `perf`.
#
# PERF, on toplevel / options / docs-walk rows: `perf.<$ev>.gen.{thunks,bytes}` is an EXACT bound (ADR-0032).
#
# $mode "check": one line per disagreement and a summary · "perf": one `PERF <json>` line per perf row,
# the line `--fold` reads · "write": the new register, $ev's perf merged in · "fold": $base with $perf's
# lines merged in.
def id: .key | tojson;
def dupsOf: group_by(.) | map(select(length > 1) | .[0]);
def perfKind: .key.kind | IN("toplevel", "options", "docs-walk");
def identityKind: .key.kind | IN("toplevel", "options");
def hits($c): . as $e | $c | all(. as $l | $e | contains($l));
def lastErr: (. // "") | split("\n") | map(select(test("^ *error:"))) | last // "(no error line)" | sub("^ +"; "");
def parity: if .gen == null or .ref == null then null
  elif .gen.thunks <= .ref.thunks and .gen.bytes <= .ref.bytes then "at-parity" else "above-parity" end;
($ARGS.named.ev // "") as $ev
| ($ARGS.named.perf // []) as $perf
| if $mode == "fold" then
  ($perf | group_by(.key | tojson) | map({ key: (.[0].key | tojson), value: map({ key: .evaluator, value: { gen, ref } }) | from_entries }) | from_entries) as $P
  | ($base | map({ key: id, value: true }) | from_entries) as $ids
  | ($P | keys | map(select($ids[.] | not))) as $stray
  | if ($stray | length) > 0 then error("PERF lines for rows the register lacks: \($stray)") else . end
  | $base[]
  | if perfKind then .perf = ((.perf // { }) + ($P[id] // { })) else . end
  | tojson
else
. as $recs
| ($base | map({ key: id, value: . }) | from_entries) as $B
| [ $recs[] | select(.ref != null and .ref.refused == false and .gen != null and .gen.refused == true and .gen.err != null) ] as $served
| ($recs | map(
    . as $r
    | ($B[$r | id] // null) as $b
    | $r + {
        id: ($r | id),
        base: $b,
        got: (
          if $r.key.kind == "docs-walk" then
            (if $r.ref.refused == false and $r.gen.refused == false then "PASS" else "FAIL" end)
          elif $r.ref == null or $r.gen == null then "FAIL"
          elif $r.ref.refused == false and $r.gen.refused == false and $r.ref.v == $r.gen.v then "PASS"
          elif $r.ref.refused and $r.gen.refused and ($b.class // null) != null and ($r.gen.err // "" | hits($b.class)) then "PASS-CLASS"
          else "FAIL" end
        )
      }
  )) as $runs
| ($runs | map({ key: .id, value: true }) | from_entries) as $seen
| if $mode == "perf" then
    $runs[]
    | select(perfKind)
    | { gen: .gen.perf, ref: .ref.perf } as $p
    | "PERF " + ({ key, evaluator: $ev, gen: $p.gen, ref: $p.ref, parity: ($p | parity),
        ratio: (if ($p | parity) == null then null else { thunks: ($p.gen.thunks / $p.ref.thunks), bytes: ($p.gen.bytes / $p.ref.bytes) } end) } | tojson)
  elif $mode == "write" then
    $runs
    | sort_by(.id)
    | map({ key, verdict: .got }
        + (if identityKind then { claim: "identity" } else { } end)
        + ((.base // { }) | with_entries(select(.key == "class" or .key == "overreach")))
        + (if perfKind then { perf: ((.base.perf // { }) + { ($ev): { gen: .gen.perf, ref: .ref.perf } }) } else { } end))
    | .[]
    | tojson
  else
    (
      [ $recs | map(id) | dupsOf | .[] | "DUPLICATE record \(.)" ]
      + [ $base | map(id) | dupsOf | .[] | "DUPLICATE baseline \(.)" ]
      + [ $base[] | select((.claim == "identity") != identityKind) | "INVALID-CLAIM \(id)" ]
      + [ $base[] | select(.perf != null and (perfKind | not)) | "INVALID-PERF \(id)" ]
      + [ $base[] | select(.class != null)
          | select((.class | type) != "array"
              or (.class | any(.[]; startswith("gen-merge: ")) | not)
              or (.class | any(.[]; contains("/nix/store/"))))
          | "INVALID-CLASS \(id)" ]
      + [ $base[] | select(.class != null) | . as $b
          | [ $served[] | select(.gen.err | hits($b.class)) | id ] as $w
          | if ($w | length) > 0 and .overreach == null then "OVERREACH \($w | join(",")) \(id)"
            elif ($w | length) == 0 and .overreach != null then "STALE-OVERREACH \(id)"
            else empty end ]
      + [ $base[] | select(.class == null and .overreach != null) | "INVALID-CLASS overreach without class \(id)" ]
      + [ $runs[] | select(.base == null) | "UNBASELINED \(.got) \(.id)" ]
      + [ $runs[] | select(.base != null and .base.verdict != .got)
          | (if .got == "FAIL" then "REGRESSED" elif .base.verdict == "FAIL" then "IMPROVED" else "MOVED" end) + " \(.base.verdict) -> \(.got) \(.id)"
          + (if .got == "FAIL" and .gen.refused == true then " || " + (.gen.err | lastErr) else "" end) ]
      + [ $base[] | select($seen[id] | not) | "MISSING \(.verdict) \(id)" ]
      + [ $runs[] | select(perfKind and .base != null) | . as $r
          | ($r.base.perf[$ev] // null) as $a
          | if $a == null then "UNANCHORED \(.id) has no perf entry for '\($ev)'"
            elif $a.gen == null or $r.gen.perf == null then empty
            else
              "thunks \($a.gen.thunks) -> \($r.gen.perf.thunks), bytes \($a.gen.bytes) -> \($r.gen.perf.bytes)" as $d
              | if $r.gen.perf.thunks > $a.gen.thunks or $r.gen.perf.bytes > $a.gen.bytes then "COST-REGRESSED \(.id) \($d)"
                elif $r.gen.perf.thunks < $a.gen.thunks or $r.gen.perf.bytes < $a.gen.bytes then "COST-RATCHET \(.id) \($d) (lower the bound in this change)"
                else empty end
            end ]
    ) as $bad
    | [ $runs[] | select(.key.kind == "doc") ] as $docs
    | [ $runs[] | select(identityKind) ] as $idn
    | ($bad[]),
      "nixos-bar: \($runs | length) cells, register \($base | length): doc \([$docs[] | select(.got == "PASS")] | length) PASS, \([$docs[] | select(.got == "PASS-CLASS")] | length) PASS-CLASS, \([$docs[] | select(.got == "FAIL")] | length) FAIL; identity (evidence) \([$idn[] | select(.got == "PASS")] | length) PASS, \([$idn[] | select(.got != "PASS")] | length) not; docs-walk \([$runs[] | select(.key.kind == "docs-walk") | .got] | join(",")); \($bad | length) disagreements"
  end
end
