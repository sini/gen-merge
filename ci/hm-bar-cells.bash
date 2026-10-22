# Stage 3's cells (den-hoag-stage3-home-manager-nk0o6, `hm-bar.nix`), run by the shared body `nixos-bar.bash`.
#
# MODE. `--read-write-mode`: home-manager's tests interpolate path literals, which copies them into the store,
# and read-only that copy is never written (the reference arm dies `path … is not valid`). No builds: IFD is
# off, so a test that reads a derivation's output at evaluation refuses by name. No network: restricted
# evaluation with no allowed URI refuses every eval-time fetcher (`access to URI … is forbidden in restricted
# mode`), and `-I /nix/store` admits the store paths the sources arrive as.
BAR_FLAGS=(--read-write-mode --option allow-import-from-derivation false --option restrict-eval true --option allowed-uris "" -I /nix/store)
# wargs <read> <route>: one argument per line, a walk read's arguments over the set `wset`.
wargs() { printf '%s\n' --argstr read "$1" --argstr set "$wset" --argstr route "$2"; }

# THE TESTS run in chunks of 50 of the sorted names (home-manager's own CI chunk size), one process per chunk
# per arm, each test under `tryEval` (`hm-bar-eval.nix`'s `chunk` read). Up to BAR_JOBS processes run at once
# (default: the host's cores), each under its own memory cap, a GC heap of BAR_HEAP bytes (default: the
# host's memory over BAR_JOBS); an evaluation that exceeds it is CONTROL FAILED (`evalArm`), never a verdict.
#
# A chunk that exits non-zero on EITHER arm is re-run one test per process on BOTH arms, so that test's value
# and refusal text come from its own process, and both arms read every test at the same grain. A test
# refused inside a chunk that completed is re-run alone on gen for its text where the reference refused too
# (a PASS-CLASS candidate) or the register holds a class row (the over-reach read needs every refused text);
# alone it must refuse again, or the chunk's reading was not the test's.
#
# THE `tests` PERF ROW sums thunks, attributed bytes and ms over one process set, the same on both arms: a
# process enters only if every test it holds served on BOTH arms. So a refused test never adds to a sum, and
# the two sums are over the same work. The row's perf is null on both arms when no process qualifies.
#
# THE SET IS PART OF THE FIGURE. A chunk that dies moves its tests from one process to fifty, so the same
# tests cost a different sum. Each arm's perf carries `set`, the summed processes' identity: their count, and
# the sha256 of the sorted lines `<process>\t<test>` (`c<n>` for a chunk, `alone` for a test in its own
# process). Test names alone would not tell a dead chunk from a live one. The compare reads the EXACT bound
# only between equal sets, and a set that moved reads SET-MOVED, never a COST line.
#
# A chunk that exits non-zero leaves its last error lines in the job log, since the run's working directory
# does not outlive it.
#
# THE SHARED THROW (`nixos-bar-compare.jq`) reads, for a test both arms refuse, each arm's `caught` and
# `trace`. In a chunk that completed, both are caught: the chunk's `tryEval` read `err`. In a chunk that died,
# each arm is read once more as a one-test `chunk`: exit 0 with `err` is caught, exit 1 is not (the refusal
# killed the process, as an IFD-off or restricted-mode refusal does), and exit 0 with `ok:` is CONTROL FAILED
# (the test served under `tryEval` though it refused alone). Where both arms are caught, both are re-read alone
# with `--show-trace` for their `trace`, and a traced read that serves is CONTROL FAILED. An uncaught test gets
# no trace read.
tests() {
  local c i e n js t sum
  local -a names=() chunk=() alive=() died=()
  evalArm names ref names --argstr read names
  [ "$rc" -eq 0 ] || control "the test names read refused: $(grep -E '^ *error' "$tmp/names.err" | tail -1)"
  mapfile -t names < <(jq -r '.v[]' "$tmp/names.out")
  [ "${#names[@]}" -gt 0 ] || control "the test names read answered no test"
  n=$(((${#names[@]} + 49) / 50))
  for ((c = 0; c < n; c++)); do
    printf '%s\n' "${names[@]:c*50:50}" | jq -Rsc 'split("\n") | map(select(. != ""))' >"$tmp/c$c.names"
    js=$(<"$tmp/c$c.names")
    for e in ref gen; do par evalArm "c$c-$e" "$e" chunk --argstr read chunk --argstr tests "$js"; done
  done
  joinAll
  : >"$tmp/summed"
  : >"$tmp/summedset"
  for ((c = 0; c < n; c++)); do
    if jq -se 'all(.[]; .refused | not)' "$tmp/c$c-ref.arm" "$tmp/c$c-gen.arm" >/dev/null; then
      alive+=("$c")
      # Every chunk line is its test's, in order: a chunk that answers another set read nothing.
      jq -se '.[0] == (.[1].v | split("\n") | map(split("\t")[0])) and .[0] == (.[2].v | split("\n") | map(split("\t")[0]))' \
        "$tmp/c$c.names" "$tmp/c$c-ref.out" "$tmp/c$c-gen.out" >/dev/null || control "chunk $c's lines are not its tests"
    else
      died+=("c$c")
      for e in ref gen; do
        if jq -e .refused "$tmp/c$c-$e.arm" >/dev/null; then
          echo "$BAR_NAME: chunk c$c died on $e:"
          grep -E '^ *error' "$tmp/c$c-$e.err" | tail -3 | cut -c1-400 | sed "s/^/$BAR_NAME:   c$c-$e /"
        fi
      done
      mapfile -t chunk < <(jq -r '.[]' "$tmp/c$c.names")
      for ((i = 0; i < ${#chunk[@]}; i++)); do
        js=$(jq -cn --arg t "${chunk[i]}" '[$t]')
        for e in ref gen; do par evalArm "c$c-t$i-$e" "$e" test --argstr read test --argstr tests "$js"; done
      done
    fi
  done
  joinAll
  # The refusal texts a chunk lost, re-read alone.
  local cls
  cls=$(jq -s 'any(.[]; .class != null)' "$base")
  for c in "${alive[@]}"; do
    jq -r --arg cls "$cls" --slurpfile ref "$tmp/c$c-ref.out" --slurpfile gen "$tmp/c$c-gen.out" -n \
      '[$ref[0].v, $gen[0].v | split("\n") | map(split("\t"))] | transpose | to_entries[]
        | select(.value[1][1] == "err" and (.value[0][1] == "err" or $cls == "true")) | "\(.key)\t\(.value[0][0])"' \
      >"$tmp/c$c.reread"
    while IFS=$'\t' read -r i t; do
      par evalArm "c$c-r$i" gen test --argstr read test --argstr tests "$(jq -cn --arg t "$t" '[$t]')"
    done <"$tmp/c$c.reread"
    # Both arms refused it, so both were caught: the traced reads of the shared-throw rule.
    jq -r --slurpfile ref "$tmp/c$c-ref.out" --slurpfile gen "$tmp/c$c-gen.out" -n \
      '[$ref[0].v, $gen[0].v | split("\n") | map(split("\t"))] | transpose | to_entries[]
        | select(.value[0][1] == "err" and .value[1][1] == "err") | "\(.key)\t\(.value[0][0])"' >"$tmp/c$c.both"
    while IFS=$'\t' read -r i t; do
      for e in ref gen; do par evalArm "c$c-x$i-$e" "$e" test --argstr read test --argstr tests "$(jq -cn --arg t "$t" '[$t]')" --show-trace; done
    done <"$tmp/c$c.both"
  done
  # A test both arms refused in a chunk that died: each arm's catchability, as a one-test `chunk`.
  for c in "${died[@]}"; do
    c=${c#c}
    mapfile -t chunk < <(jq -r '.[]' "$tmp/c$c.names")
    for ((i = 0; i < ${#chunk[@]}; i++)); do
      jq -se 'all(.[]; .refused)' "$tmp/c$c-t$i-ref.arm" "$tmp/c$c-t$i-gen.arm" >/dev/null || continue
      js=$(jq -cn --arg t "${chunk[i]}" '[$t]')
      for e in ref gen; do par evalArm "c$c-k$i-$e" "$e" chunk --argstr read chunk --argstr tests "$js"; done
    done
  done
  joinAll
  for c in "${died[@]}"; do
    c=${c#c}
    mapfile -t chunk < <(jq -r '.[]' "$tmp/c$c.names")
    for ((i = 0; i < ${#chunk[@]}; i++)); do
      [ -e "$tmp/c$c-k$i-ref.arm" ] || continue
      for e in ref gen; do
        if jq -e .refused "$tmp/c$c-k$i-$e.arm" >/dev/null; then
          echo false >"$tmp/c$c-k$i-$e.caught"
        elif [ "$(jq -r '.v | split("\t")[1]' "$tmp/c$c-k$i-$e.out")" = err ]; then
          echo true >"$tmp/c$c-k$i-$e.caught"
        else
          control "test ${chunk[i]} refused alone on $e but served as a one-test chunk"
        fi
      done
      if [ "$(cat "$tmp/c$c-k$i-ref.caught" "$tmp/c$c-k$i-gen.caught")" = "$(printf 'true\ntrue')" ]; then
        js=$(jq -cn --arg t "${chunk[i]}" '[$t]')
        for e in ref gen; do par evalArm "c$c-x$i-$e" "$e" test --argstr read test --argstr tests "$js" --show-trace; done
      fi
    done
  done
  joinAll
  for c in "${alive[@]}"; do
    while IFS=$'\t' read -r i t; do
      jq -e .refused "$tmp/c$c-r$i.arm" >/dev/null || control "test $t refused in chunk $c but served alone"
    done <"$tmp/c$c.reread"
    while IFS=$'\t' read -r i t; do
      for e in ref gen; do
        jq -e .refused "$tmp/c$c-x$i-$e.arm" >/dev/null || control "test $t refused on both arms in chunk $c but its traced $e read served"
      done
    done <"$tmp/c$c.both"
    jq -cn --slurpfile ref "$tmp/c$c-ref.out" --slurpfile gen "$tmp/c$c-gen.out" --rawfile rr "$tmp/c$c.reread" --arg dir "$tmp" --arg c "$c" \
      '($rr | split("\n") | map(select(. != "") | split("\t")[0] | tonumber)) as $re
        | def arm: if .[1] == "err" then { refused: true, v: null, err: null } else { refused: false, v: (.[1] | ltrimstr("ok:")) } end;
        [$ref[0].v, $gen[0].v | split("\n") | map(split("\t"))] | transpose | to_entries[]
        | { key: { kind: "test", name: .value[0][0] }, ref: (.value[0] | arm), gen: (.value[1] | arm), i: .key }' >"$tmp/c$c.recs"
    # The re-read texts, attached to their records.
    while IFS=$'\t' read -r i t; do
      jq -c --argjson i "$i" --rawfile err "$tmp/c$c-r$i.err" 'if .i == $i then .gen.err = $err else . end' "$tmp/c$c.recs" >"$tmp/c$c.recs2"
      mv "$tmp/c$c.recs2" "$tmp/c$c.recs"
    done <"$tmp/c$c.reread"
    while IFS=$'\t' read -r i t; do
      jq -c --argjson i "$i" --rawfile rt "$tmp/c$c-x$i-ref.err" --rawfile gt "$tmp/c$c-x$i-gen.err" \
        'if .i == $i then .ref += {caught: true, trace: $rt} | .gen += {caught: true, trace: $gt} else . end' "$tmp/c$c.recs" >"$tmp/c$c.recs2"
      mv "$tmp/c$c.recs2" "$tmp/c$c.recs"
    done <"$tmp/c$c.both"
    jq -c 'del(.i)' "$tmp/c$c.recs" >>"$tmp/records.jsonl"
    if jq -se 'all(.[]; .ref.refused == false and .gen.refused == false)' "$tmp/c$c.recs" >/dev/null; then
      echo "c$c-ref c$c-gen" >>"$tmp/summed"
      jq -r --arg p "c$c" '.[] | "\($p)\t\(.)"' "$tmp/c$c.names" >>"$tmp/summedset"
    fi
  done
  for ((c = 0; c < n; c++)); do
    [ -e "$tmp/c$c-t0-ref.arm" ] || continue
    mapfile -t chunk < <(jq -r '.[]' "$tmp/c$c.names")
    for ((i = 0; i < ${#chunk[@]}; i++)); do
      jq -cn --arg t "${chunk[i]}" --slurpfile ref "$tmp/c$c-t$i-ref.arm" --slurpfile gen "$tmp/c$c-t$i-gen.arm" \
        '{ key: { kind: "test", name: $t }, ref: ($ref[0] | del(.perf)), gen: ($gen[0] | del(.perf)) }' >"$tmp/c$c-t$i.rec"
      for e in ref gen; do
        [ -e "$tmp/c$c-k$i-$e.caught" ] || continue
        if [ -e "$tmp/c$c-x$i-$e.arm" ]; then
          jq -e .refused "$tmp/c$c-x$i-$e.arm" >/dev/null || control "test ${chunk[i]} refused alone on both arms but its traced $e read served"
          jq -c --arg e "$e" --rawfile tr "$tmp/c$c-x$i-$e.err" '.[$e] += {caught: true, trace: $tr}' "$tmp/c$c-t$i.rec"
        else
          jq -c --arg e "$e" --argjson k "$(cat "$tmp/c$c-k$i-$e.caught")" '.[$e] += {caught: $k}' "$tmp/c$c-t$i.rec"
        fi >"$tmp/c$c-t$i.rec2"
        mv "$tmp/c$c-t$i.rec2" "$tmp/c$c-t$i.rec"
      done
      cat "$tmp/c$c-t$i.rec" >>"$tmp/records.jsonl"
      if jq -se 'all(.[]; .refused | not)' "$tmp/c$c-t$i-ref.arm" "$tmp/c$c-t$i-gen.arm" >/dev/null; then
        echo "c$c-t$i-ref c$c-t$i-gen" >>"$tmp/summed"
        printf 'alone\t%s\n' "${chunk[i]}" >>"$tmp/summedset"
      fi
    done
  done
  # The two sums, over the same processes.
  local set
  set=$(jq -cn --argjson n "$(wc -l <"$tmp/summed")" --arg sha "$(LC_ALL=C sort "$tmp/summedset" | sha256sum | cut -c1-64)" \
    '{ processes: $n, sha: $sha }')
  sum() {
    local -a f=()
    local p
    while read -r p; do f+=("$tmp/$p.arm"); done
    if [ "${#f[@]}" -eq 0 ]; then echo null; else jq -sc --argjson set "$set" 'map(.perf) | { thunks: (map(.thunks) | add), bytes: (map(.bytes) | add), ms: (map(.ms) | add), $set }' "${f[@]}"; fi
  }
  jq -cn --argjson ref "$(cut -d' ' -f1 "$tmp/summed" | sum)" --argjson gen "$(cut -d' ' -f2 "$tmp/summed" | sum)" \
    '{ key: { kind: "tests" }, ref: { refused: false, v: null, perf: $ref }, gen: { refused: false, v: null, perf: $gen } }' >>"$tmp/records.jsonl"
  echo "$BAR_NAME: tests: ${#names[@]} in $n chunks, ${#alive[@]} completed on both arms, $((n - ${#alive[@]})) re-run per test on both (${died[*]:-none}); $(wc -l <"$tmp/summed") processes per arm summed (every test they hold served on both arms), set $(jq -r '.sha[0:12]' <<<"$set")"
  # Diagnostic, never a bound: each arm's counters over every process of it that exited 0, so repeats can
  # be read for identity while the summed set is empty.
  for e in ref gen; do
    find "$tmp" -maxdepth 1 -regex ".*/c[0-9]+\(-t[0-9]+\)?-$e\.arm" -print0 | xargs -0 cat |
      jq -sc --arg e "$e" '[.[] | .perf | select(. != null)] | "\(length) served \($e) processes: thunks \(map(.thunks) | add), bytes \(map(.bytes) | add)"' |
      sed "s/^\"/$BAR_NAME: tests: /; s/\"\$//"
  done
}

cells() {
  local jobs
  jobs=${BAR_JOBS:-$(nproc)}
  export GC_MAXIMUM_HEAP_SIZE=${BAR_HEAP:-$(($(awk '/^MemTotal:/ { print $2 }' /proc/meminfo) * 1024 / jobs))}
  echo "$BAR_NAME: $jobs processes at once, each under a GC heap of $GC_MAXIMUM_HEAP_SIZE bytes"
  for wset in hm nixos darwin; do
    docsWalk "{\"kind\":\"docs-walk\",\"set\":\"$wset\"}" "$wset" wargs
  done
  tests
}
