# Scores one replacement-bar run (the slurped cell records, `nixos-bar.bash`; stage 2's `nixos-bar` and stage
# 3's `hm-bar`) against the committed register ($base, its rows), for the evaluator whose `--version` line is
# $ev. $label is the program's name, on its PERF and summary lines.
#
# A record is `{key, claim?, ref, gen}`, an arm `{refused, v, err?, perf, caught?, trace?}` (null where the
# walk has no such node). The verdict is stage 1's (`modules-sh-compare.jq`):
#   PASS        both arms serve and their values are equal: the drvPath for toplevel / options, the
#               entry's JSON hash for a doc node, the value's hash for a test; a docs-walk or tests row is
#               PASS iff both arms ran to the end
#   PASS-CLASS  both refuse, on a row whose committed `class` literals all occur in gen's refusal; a class
#               opens `gen-merge: ` and carries no store path, and OVER-REACH is read on every run against
#               the rows where nixpkgs serves and gen refuses (`modules-sh-compare.jq` gives the rule);
#               or both refuse with THE SHARED THROW (below)
#   FAIL        everything else: unequal, gen refusing where nixpkgs serves, a node gen lacks, and gen
#               serving where nixpkgs refuses (FAIL until a (b') ruling names the cell, ADR-0039)
#
# THE SHARED THROW (den-hoag-refusal-class-consumer-throw-ovyos), a reading of ADR-0039's "refused wherever
# nixpkgs refuses (the same refusal CLASS, not text)": a doc node or a test both arms refuse is PASS-CLASS when
#   T1  each arm's refusal was caught by `builtins.tryEval` (`caught`: the walk's or the chunk's read). tryEval
#       catches `throw` and a failed `assert`, never an evaluator's refusal for its mode (import from
#       derivation off, a restricted URI or path), so a refusal the instrument's mode raises never passes;
#   T2  each arm's innermost position, the last `at /<path>:<line>:<col>:` line of its `--show-trace` re-read
#       (`trace`), is the same on both arms and lies under one of the stage's subject roots ($roots: nixpkgs,
#       and for stage 3 the patched home-manager tree and nmt). The reference arm never imports gen-merge's
#       sources, so an equal site is never gen-merge's code, and the roots exclude the instrument's own files;
#   T3  the text from each trace's last `error:` line to its end is byte-identical: the message names its
#       subject, so the same site refusing another subject does not pass.
# Same site and same message is the refusal's identity, stronger than its class. SOUND, NOT COMPLETE: an
# `abort` or an evaluator error both arms raise at one site is not caught, so it stays FAIL; and only doc nodes
# and tests carry `caught` and `trace`, so a toplevel or options cell both arms refuse stays FAIL. The summary
# names the share of PASS-CLASS this rule gave.
# A toplevel, options or flake-drv row carries `"claim":"identity"`: its PASS is derivations' identity, evidence
# and never acceptance (ADR-0039). Only those kinds carry it, and only perf rows carry `perf`. Stage 4's kinds
# (unit, memo, template, flake, flake-drv) occur in no other stage's register (`fp-bar-cells.bash` reads it), so
# adding them here moves no row of stages 2-3.
#
# PERF, on toplevel / options / docs-walk / tests rows and every stage-4 row: `perf.<$ev>.gen.{thunks,bytes}` is an EXACT bound (ADR-0032),
# read only where the run summed the same processes as the anchor: a perf entry carrying `set` (stage 3's
# `tests` row) whose set moved reads SET-MOVED instead of a COST line.
#
# $mode "check": one line per disagreement and a summary · "perf": one `PERF <label> <json>` line per perf row,
# the line `--fold` reads · "write": the new register, $ev's perf merged in · "fold": $base with $perf's
# lines merged in. Every mode but "fold" refuses without $roots, a non-empty list of absolute store paths: an
# empty list would pass no shared throw, silently.
def id: .key | tojson;
def dupsOf: group_by(.) | map(select(length > 1) | .[0]);
def perfKind: .key.kind | IN("toplevel", "options", "docs-walk", "tests", "unit", "memo", "template", "flake", "flake-drv");
def identityKind: .key.kind | IN("toplevel", "options", "flake-drv");
def hits($c): . as $e | $c | all(. as $l | $e | contains($l));
def lastErr: (. // "") | split("\n") | map(select(test("^ *error:"))) | last // "(no error line)" | sub("^ +"; "");
def site: (. // "") | split("\n") | map(select(test("^ *at /"))) | last // null | if . == null then null else sub("^ *at "; "") end;
def final: (. // "") | split("\n") | (map(test("^ *error:")) | rindex(true)) as $i | if $i == null then null else .[$i:] | join("\n") end;
def shared($roots): (.ref.trace | site) as $s | (.ref.trace | final) as $f
  | .ref.caught == true and .gen.caught == true
    and $s != null and $s == (.gen.trace | site) and ($roots | any(. as $p | $s | startswith($p + "/")))
    and $f != null and $f == (.gen.trace | final);
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
($ARGS.named.roots // null) as $roots
| if ($roots | type) != "array" or ($roots | length) == 0 or ($roots | any(.[]; type != "string" or (startswith("/nix/store/") | not)))
  then error("roots: \($mode) needs --argjson roots, the stage's subject roots, a non-empty list of store paths; got \($roots | tojson)") else . end
| . as $recs
| ($base | map({ key: id, value: . }) | from_entries) as $B
| [ $recs[] | select(.ref != null and .ref.refused == false and .gen != null and .gen.refused == true and .gen.err != null) ] as $served
| ($recs | map(
    . as $r
    | ($B[$r | id] // null) as $b
    | ($r.ref.refused == true and $r.gen.refused == true and ($r.key.kind | IN("docs-walk", "tests") | not)) as $both
    | ($both and ($b.class // null) != null and ($r.gen.err // "" | hits($b.class))) as $cls
    | ($both and ($cls | not) and ($r | shared($roots))) as $sh
    | $r + {
        id: ($r | id),
        base: $b,
        shared: $sh,
        got: (
          if $r.key.kind | IN("docs-walk", "tests") then
            (if $r.ref.refused == false and $r.gen.refused == false then "PASS" else "FAIL" end)
          elif $r.ref == null or $r.gen == null then "FAIL"
          elif $r.ref.refused == false and $r.gen.refused == false and $r.ref.v == $r.gen.v then "PASS"
          elif $cls or $sh then "PASS-CLASS"
          else "FAIL" end
        )
      }
  )) as $runs
| ($runs | map({ key: .id, value: true }) | from_entries) as $seen
| if $mode == "perf" then
    $runs[]
    | select(perfKind)
    | { gen: .gen.perf, ref: .ref.perf } as $p
    | "PERF \($ARGS.named.label) " + ({ key, evaluator: $ev, gen: $p.gen, ref: $p.ref, parity: ($p | parity),
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
          + (if .got == "FAIL" and .gen.refused == true then " || " + (if .gen.err == null then "(text not read: chunk)" else .gen.err | lastErr end) else "" end) ]
      + [ $base[] | select($seen[id] | not) | "MISSING \(.verdict) \(id)" ]
      + [ $runs[] | select(perfKind and .base != null) | . as $r
          | ($r.base.perf[$ev] // null) as $a
          | if $a == null then "UNANCHORED \(.id) has no perf entry for '\($ev)'"
            elif $a.gen != null and ($a.gen.set // null) != ($r.gen.perf.set // null) then
              "SET-MOVED \(.id) summed \($a.gen.set.processes // "none") -> \($r.gen.perf.set.processes // "none") processes, set \($a.gen.set.sha[0:12] // "none") -> \($r.gen.perf.set.sha[0:12] // "none") (the bound compares only equal sets)"
            elif $a.gen == null or $r.gen.perf == null then empty
            else
              "thunks \($a.gen.thunks) -> \($r.gen.perf.thunks), bytes \($a.gen.bytes) -> \($r.gen.perf.bytes)" as $d
              | if $r.gen.perf.thunks > $a.gen.thunks or $r.gen.perf.bytes > $a.gen.bytes then "COST-REGRESSED \(.id) \($d)"
                elif $r.gen.perf.thunks < $a.gen.thunks or $r.gen.perf.bytes < $a.gen.bytes then "COST-RATCHET \(.id) \($d) (lower the bound in this change)"
                else empty end
            end ]
    ) as $bad
    | [ $runs[] | select(.key.kind == "doc") ] as $docs
    | [ $runs[] | select(.key.kind == "test") ] as $tests
    | [ $runs[] | select(identityKind) ] as $idn
    | def tally: "\(map(select(.got == "PASS")) | length) PASS, \(map(select(.got == "PASS-CLASS")) | length) PASS-CLASS (\(map(select(.shared)) | length) shared throw), \(map(select(.got == "FAIL")) | length) FAIL";
    ($bad[]),
      "\($ARGS.named.label): \($runs | length) cells, register \($base | length): doc \($docs | tally)"
      + (if ($tests | length) > 0 then "; test \($tests | tally)" else "" end)
      + (if ($idn | length) > 0 then "; identity (evidence) \([$idn[] | select(.got == "PASS")] | length) PASS, \([$idn[] | select(.got != "PASS")] | length) not" else "" end)
      + "; docs-walk \([$runs[] | select(.key.kind == "docs-walk") | .got] | join(","))"
      + (if ($tests | length) > 0 then "; tests \([$runs[] | select(.key.kind == "tests") | .got] | join(","))" else "" end)
      + ([ "unit", "memo", "template", "flake", "flake-drv" ] | map(. as $k | [ $runs[] | select(.key.kind == $k) ] | select(length > 0) | "; \($k) \(tally)") | join(""))
      + "; \($bad | length) disagreements"
  end
end
