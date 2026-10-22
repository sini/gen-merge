# The rows of a register change that LOWER the bar: $old and $new are two revisions of one register.
# A key falls when its rank drops (PASS > PASS-CLASS > FAIL) or when a PASS / PASS-CLASS key is gone
# (an upstream edit that re-keys an assertion is a disappearance plus an UNBASELINED newcomer, so it
# falls here too). One line per fallen key: `<id>\t<old verdict>\t<new verdict, or ABSENT>`.
#
# $keyform (default "legacy"): "legacy" is modules-sh's id, `[.kind, .env, .argv]`; "json" is the key
# itself, for every later register (`nixos-bar-baseline.jsonl`).
#
# $part "rise" reads the perf clause instead (ADR-0032's EXACT bound): a row whose committed gen `thunks`
# or `bytes` for one evaluator ROSE between the revisions, both revisions serving. One line per rise:
# `<id>\t<evaluator>\t<old gen thunks/bytes>\t<new gen thunks/bytes>\t<new at parity: yes|no>\t<old
# above its reference at the anchor: yes|no>`. A new evaluator key, or a first serving run, is a new
# anchor and never a rise. A perf entry that carries its summed `set` (stage 3's `tests` row) and whose set
# moved reads as a rise whatever the figures did: the same work was not measured, so a lower figure is not
# a lowering.
def id: if ($ARGS.named.keyform // "legacy") == "legacy" then [.kind, .env, .argv] else . end | tojson;
def rank: { "PASS": 2, "PASS-CLASS": 1, "FAIL": 0 }[.];
def le($a; $b): $a.thunks <= $b.thunks and $a.bytes <= $b.bytes;
if ($ARGS.named.part // "fall") == "rise" then
  ($old | map({ key: (.key | id), value: (.perf // { }) }) | from_entries) as $O
  | $new[]
  | (.key | id) as $i
  | (.perf // { }) | to_entries[]
  | .key as $e
  | .value as $n
  | ($O[$i][$e] // null) as $o
  | select($o != null and $o.gen != null and $n.gen != null)
  | select($n.gen.thunks > $o.gen.thunks or $n.gen.bytes > $o.gen.bytes or ($n.gen.set // null) != ($o.gen.set // null))
  | "\($i)\t\($e)\t\($o.gen.thunks)/\($o.gen.bytes)\t\($n.gen.thunks)/\($n.gen.bytes)\t\(if $n.ref != null and le($n.gen; $n.ref) then "yes" else "no" end)\t\(if $o.ref != null and (le($o.gen; $o.ref) | not) then "yes" else "no" end)"
else
  ($new | map({ key: (.key | id), value: .verdict }) | from_entries) as $N
  | $old[]
  | (.key | id) as $i
  | .verdict as $was
  | ($N[$i] // "ABSENT") as $now
  | select(if $now == "ABSENT" then ($was | rank) > 0 else ($now | rank) < ($was | rank) end)
  | "\($i)\t\($was)\t\($now)"
end
