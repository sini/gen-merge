# The cells of `checks.bar-fold` (`bar-fold.nix`) for one bar's `--fold`:
#   bar-fold-cells.bash <name> <bin> <register>
# Each cell folds three synthetic column logs, built from a perf row of the committed register, into a copy of
# that register (the FIXTURE, below) and reads the folded copy's md5 against the fixture's own. Prints `PASS <name> <cell>` or
# `FAIL <name> <cell>: <why>`, one line per cell; the derivation holds their count.
set -u
name=$1 bin=$2 reg=$3
w=$(mktemp -d)
# A row's identity as the bar's compare spells it, and a verdict line's prefix (modules-sh prints the line).
if [ "$name" = modules-sh ]; then idf='.key | [.kind, .env, .argv] | tojson' pre='L1 '; else idf='.key | tojson' pre=''; fi
row=$(jq -cn 'first(inputs | select(.perf != null and (.perf | length) >= 3))' "$reg")
pass=$(jq -rn "first(inputs | select(.verdict == \"PASS\")) | $idf" "$reg")
[ -n "$row" ] && [ -n "$pass" ] || { echo "FAIL $name fixture: no perf row with three columns, or no PASS row"; exit 1; }
# The row's columns: one of each evaluator family.
col() { jq -r --arg f "$1" '[.perf | keys[] | select(contains($f))] | .[-1]' <<<"$row"; }
det=$(col '(Determinate ') lix=$(col '(Lix') nix=$(col '(Nix)')
for e in "$det" "$lix" "$nix"; do
  [ -n "$e" ] && [ "$e" != null ] || { echo "FAIL $name fixture: the perf row lacks a column of each family"; exit 1; }
done
# A second Determinate column, minted here: the cell reads no evaluator from the register beyond the three above.
det2="nix-instantiate (Determinate Nix 0.0.0-bar-fold) 0.0.0"
# THE FIXTURE: the register with ONE row of its own made a refusal carrying a text for each CI column, so the text
# cell reads the refusal-text path whatever the register holds. A register need hold no refusal row: a reference move
# that serves its last refused cell leaves it none (hm-bar at nixpkgs d4f25a3, waveterm-example-config). The row is
# the first one that is neither the perf row nor the PASS row the verdict lines name, written as jq writes a register
# row, so the folds below reproduce the fixture byte for byte.
fx=$(jq -cn --argjson p "$row" --arg pass "$pass" "first(inputs | select(.key != \$p.key and ($idf) != \$pass))" "$reg")
[ -n "$fx" ] || { echo "FAIL $name fixture: no row besides the perf and PASS rows to carry a refusal text"; exit 1; }
jq -c --argjson f "$fx" --arg d "$det" --arg l "$lix" --arg n "$nix" \
  'if .key == $f.key then .verdict = "FAIL" | .refusal = ({($d): "error: bar-fold fixture: a refusal", ($l): "error: bar-fold fixture: a refusal", ($n): "error: bar-fold fixture: a refusal"} | to_entries | sort_by(.key) | from_entries) else . end' \
  "$reg" >"$w/fixture.reg"
# A bar's `--fold` reads the register its build baked in (`base`, `BAR_BASE`), never F, so the fixture is folded by a
# copy of the bar whose one baked register path, asserted to be this register, names the fixture instead.
baked=$(grep -oE "/nix/store/[a-z0-9]{32}-$name-baseline\.jsonl" "$bin" | sort -u)
[ "$(wc -w <<<"$baked")" = 1 ] && cmp -s "$baked" "$reg" ||
  { echo "FAIL $name fixture: $bin does not bake exactly one register path holding this register"; exit 1; }
sed "s#$baked#$w/fixture.reg#g" "$bin" >"$w/bar"
chmod +x "$w/bar"
bin=$w/bar
reg=$w/fixture.reg
want=$(md5sum <"$reg")
text=$(jq -cn --argjson f "$fx" 'first(inputs | select(.key == $f.key))' "$reg")
# log <file> <column> <jq over the column's perf entry> [<evaluator>]: one column's log, its PERF line for the row,
# then the column's REFUSAL line for every register row carrying a text for it, and their count line
# (den-hoag-pvy24). An <evaluator> relabels the column: its log carries <column>'s figures under that name.
log() {
  jq -r --arg c "$2" --arg e "${4:-$2}" --arg bar "$name" ".key as \$k | .perf | to_entries | map(select(.key == \$c)) | .[0] | .key = \$e | $3
    | \"2026-11-03T00:00:00.0000000Z PERF \(\$bar) \" + ({key: \$k, evaluator: .key, gen: .value.gen, ref: .value.ref} | tojson)" \
    <<<"$row" >"$w/$1"
  jq -r --arg c "${4:-$2}" --arg bar "$name" 'select(.refusal[$c] != null)
    | "2026-11-03T00:00:00.0000000Z REFUSAL \($bar) " + ({key, evaluator: $c, text: .refusal[$c]} | tojson)' "$reg" >"$w/$1.r"
  cat "$w/$1.r" >>"$w/$1"
  echo "2026-11-03T00:00:00.0000000Z REFUSALS $name $(wc -l <"$w/$1.r")" >>"$w/$1"
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
log det2.log "$det" . "$det2"
# A column's log with its REFUSALS count line gone (den-hoag-pvy24).
grep -v " REFUSALS $name " "$w/c0.log" >"$w/nocount0.log"
# The text row's own column, and that column's log with the row's REFUSAL text moved. The column is the first of the
# perf row's CI columns the text row carries a text for (THE FIXTURE gave it one for each), read by name, never by key
# position.
tcol=$(jq -r --arg d "$det" --arg l "$lix" --arg n "$nix" '[.refusal | keys[] | select(. == $d or . == $l or . == $n)] | .[0] // ""' <<<"$text")
for e in "$det" "$lix" "$nix"; do [ "$e" = "$tcol" ] && break; done
[ "$e" = "$tcol" ] || { echo "FAIL $name fixture: the text row carries no refusal text for a CI column of the perf row"; exit 1; }
tc=0
for e in "$det" "$lix" "$nix"; do [ "$e" = "$tcol" ] && break; tc=$((tc + 1)); done
tk=$(jq -c .key <<<"$text")
jq -cR --argjson k "$tk" --arg bar "$name" '. as $l | if startswith("2026-11-03T00:00:00.0000000Z REFUSAL \($bar) {")
  then (ltrimstr("2026-11-03T00:00:00.0000000Z REFUSAL \($bar) ") | fromjson) as $r
    | if $r.key == $k then "2026-11-03T00:00:00.0000000Z REFUSAL \($bar) " + ($r | .text += " (moved)" | tojson) else $l end
  else $l end' "$w/c$tc.log" | jq -r . >"$w/text$tc.log"

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
# THE TEXT CELL (den-hoag-pvy24): one column's refusal text moved is one changed row, carrying the log's text.
logs=("$w/c0.log" "$w/c1.log" "$w/c2.log")
logs[tc]=$w/text$tc.log
fold text "${logs[@]}"
d=$(jq -n --slurpfile a "$reg" --slurpfile b "$w/text.reg" '[range($a | length) as $i | select($a[$i] != $b[$i])] | length')
t=$(jq -rn --argjson k "$tk" --arg c "$tcol" 'first(inputs | select(.key == $k)) | .refusal[$c]' "$w/text.reg")
say text "$([ "$rc" = 0 ] && [ "$d" = 1 ] && [ "$t" = "$(jq -r --arg c "$tcol" '.refusal[$c]' <<<"$text") (moved)" ] && echo ok || echo "$d rows changed, want 1 carrying the moved text")"
# A log with no REFUSALS count line is a column that printed no refusals, never one with none: refused, register untouched.
fold nocount "$w/nocount0.log" "$w/c1.log" "$w/c2.log"
say nocount "$([ "$rc" = 2 ] && grep -q "count lines, not one" "$w/nocount.err" && [ "$got" = "$want" ] && echo ok || echo "not refused for its missing count line with the register untouched")"
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
