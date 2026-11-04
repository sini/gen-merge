# The cells of `checks.bar-fold` (`bar-fold.nix`) for one bar's `--fold`:
#   bar-fold-cells.bash <name> <bin> <register>
# Each cell folds three synthetic column logs, built from a perf row of the committed register, into a copy of
# that register and reads the copy's md5 against the register's own. Prints `PASS <name> <cell>` or
# `FAIL <name> <cell>: <why>`, one line per cell; the derivation holds their count.
set -u
name=$1 bin=$2 reg=$3
w=$(mktemp -d)
want=$(md5sum <"$reg")
# A row's identity as the bar's compare spells it, and a verdict line's prefix (modules-sh prints the line).
if [ "$name" = modules-sh ]; then idf='.key | [.kind, .env, .argv] | tojson' pre='L1 '; else idf='.key | tojson' pre=''; fi
row=$(jq -cn 'first(inputs | select(.perf != null and (.perf | length) >= 3))' "$reg")
pass=$(jq -rn "first(inputs | select(.verdict == \"PASS\")) | $idf" "$reg")
[ -n "$row" ] && [ -n "$pass" ] || { echo "FAIL $name fixture: no perf row with three columns, or no PASS row"; exit 1; }
# The row's columns: one of each evaluator family, and a second Determinate one.
col() { jq -r --arg f "$1" '[.perf | keys[] | select(contains($f))] | .[-1]' <<<"$row"; }
det=$(col '(Determinate ') lix=$(col '(Lix') nix=$(col '(Nix)')
det2=$(jq -r --arg d "$det" '[.perf | keys[] | select(contains("(Determinate ") and . != $d)] | .[0]' <<<"$row")
for e in "$det" "$lix" "$nix" "$det2"; do
  [ -n "$e" ] && [ "$e" != null ] || { echo "FAIL $name fixture: the perf row lacks a column of each family and two Determinate ones"; exit 1; }
done
# log <file> <column> <jq over the column's perf entry>: one column's log, its PERF line for the row.
log() {
  jq -r --arg c "$2" --arg bar "$name" ".key as \$k | .perf | to_entries | map(select(.key == \$c)) | .[0] | $3
    | \"2026-11-03T00:00:00.0000000Z PERF \(\$bar) \" + ({key: \$k, evaluator: .key, gen: .value.gen, ref: .value.ref} | tojson)" \
    <<<"$row" >"$w/$1"
}
# fold <cell> <log>...: the bar's --fold into a copy of the register; leaves rc, and the copy's md5 in got.
fold() {
  local c=$1
  shift
  cp "$reg" "$w/$c.reg"
  chmod u+w "$w/$c.reg"
  rc=0
  "$bin" --fold "$w/$c.reg" "$@" >"$w/$c.out" 2>"$w/$c.err" || rc=$?
  got=$(md5sum <"$w/$c.reg")
}
say() { if [ "$2" = ok ]; then echo "PASS $name $1"; else echo "FAIL $name $1: $2 (rc $rc; $(tail -1 "$w/$1.err"))"; fi; }

c=0
for e in "$det" "$lix" "$nix"; do
  log "c$c.log" "$e" .
  log "ms$c.log" "$e" '.value.gen.ms += 1 | .value.ref.ms += 1'
  { cat "$w/c$c.log"; echo "2026-11-03T00:00:00.0000000Z REGRESSED ${pre}PASS -> FAIL $pass"; } >"$w/r$c.log"
  c=$((c + 1))
done
log moved0.log "$det" '.value.gen.thunks += 1'
log det2.log "$det2" .

# Three distinct columns carrying the register's own figures: the register, byte for byte.
fold same "$w/c0.log" "$w/c1.log" "$w/c2.log"
say same "$([ "$rc" = 0 ] && [ "$got" = "$want" ] && echo ok || echo "not the register's bytes")"
# The same counts at other wall times: `ms` is recorded, never compared, so a fold moving no count is a no-op.
fold ms "$w/ms0.log" "$w/ms1.log" "$w/ms2.log"
say ms "$([ "$rc" = 0 ] && [ "$got" = "$want" ] && echo ok || echo "a fold moving no count rewrote the register")"
# The control for the two above: one moved count is one changed row, carrying the log's figure.
fold moved "$w/moved0.log" "$w/c1.log" "$w/c2.log"
d=$(jq -n --slurpfile a "$reg" --slurpfile b "$w/moved.reg" '[range($a | length) as $i | select($a[$i] != $b[$i])] | length')
say moved "$([ "$rc" = 0 ] && [ "$d" = 1 ] && echo ok || echo "$d rows changed, want 1")"
# One log passed three times is one column: refused, by the count of evaluators, and the register untouched.
fold dup "$w/c0.log" "$w/c0.log" "$w/c0.log"
say dup "$([ "$rc" != 0 ] && grep -q 'missing' "$w/dup.err" && [ "$got" = "$want" ] && echo ok || echo "not refused by evaluator count with the register untouched")"
# A verdict line the fold does not adopt refuses, and a refused fold leaves the register as it was.
fold refused "$w/r0.log" "$w/r1.log" "$w/r2.log"
say refused "$([ "$rc" != 0 ] && grep -q 'verdict lines --fold does not adopt' "$w/refused.err" && [ "$got" = "$want" ] && echo ok || echo "not refused with the register untouched ($(wc -c <"$w/refused.reg") bytes)")"
# Three distinct versions are not three evaluators: two Determinate columns and Lix is a fold with no Nix
# column, refused by the family it lacks, and the register untouched.
fold fam "$w/c0.log" "$w/det2.log" "$w/c1.log"
say fam "$([ "$rc" = 2 ] && grep -q 'missing: Nix$' "$w/fam.err" && [ "$got" = "$want" ] && echo ok || echo "not refused naming the missing Nix family with the register untouched")"
