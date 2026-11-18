# barBudget [<jobs>]: a bar phase's concurrency and GC heap, from the memory this process may actually use.
# Sets and exports BAR_JOBS (`par`'s bound) and GC_MAXIMUM_HEAP_SIZE; with <jobs> the phase runs that many.
#
# The room is the least of the host's MemAvailable and, for the process's own cgroup (v2) and EVERY ancestor that
# limits memory, memory.max or memory.high less that cgroup's memory.current. A scope's cap binds as surely as
# the host's memory does, and the cap is shared with what the scope already holds. RESERVE bytes of the room are
# left to the shell, jq and each evaluator's non-GC memory. Defaults, applied only where unset:
#   jobs = min(nproc, room / FLOOR), heap = room / jobs (FLOOR: the heap the measured BAR_JOBS=4 BAR_HEAP=2.5GiB
#   workaround served the full register at, under a 12G scope).
# BAR_JOBS and BAR_HEAP, when set, are honoured as given (the documented override); with BOTH set nothing is read.
# FAILS CLOSED (exit 2, CONTROL FAILED, never a verdict) when the room cannot be read (no cgroup v2 entry, a
# missing cgroup directory, an unreadable or malformed limit) or is too small for one FLOOR heap per job,
# because guessing would be the overcommit this replaces. Set BAR_JOBS and BAR_HEAP to run anyway.
# BAR_PROCFS and BAR_SYSFS move /proc and /sys/fs/cgroup, for `bar-budget-cells.bash` only.
barBudget() {
  local floor=2684354560 reserve=2147483648 proc=${BAR_PROCFS:-/proc} sys=${BAR_SYSFS:-/sys/fs/cgroup}
  local want=${1:-${BAR_JOBS:-}} heap=${BAR_HEAP:-} room rel dir f lim cur n
  bad() {
    echo "$BAR_NAME: CONTROL FAILED: memory budget: $* (set BAR_JOBS and BAR_HEAP to override)" >&2
    exit 2
  }
  if [ -z "$want" ] || [ -z "$heap" ]; then
    room=$(awk '/^MemAvailable:/ { print $2 * 1024 }' "$proc/meminfo" 2>/dev/null || true)
    [[ $room =~ ^[0-9]+$ ]] || bad "no MemAvailable in $proc/meminfo"
    n=$(grep -c '^0::' "$proc/self/cgroup" 2>/dev/null || true)
    [ "$n" = 1 ] || bad "$proc/self/cgroup holds $n cgroup v2 entries, not 1"
    rel=$(sed -n 's/^0:://p' "$proc/self/cgroup")
    dir=$sys${rel%/}
    [ -d "$dir" ] || bad "the process's cgroup $dir does not exist"
    while :; do
      for f in memory.max memory.high; do
        [ -e "$dir/$f" ] || continue
        read -r lim 2>/dev/null <"$dir/$f" || bad "$dir/$f is unreadable"
        [ "$lim" = max ] && continue
        [[ $lim =~ ^[0-9]+$ ]] || bad "$dir/$f reads '$lim'"
        read -r cur 2>/dev/null <"$dir/memory.current" && [[ $cur =~ ^[0-9]+$ ]] ||
          bad "$dir limits memory but its memory.current is unreadable"
        if ((lim - cur < room)); then room=$((lim > cur ? lim - cur : 0)); fi
      done
      if [ "$dir" = "$sys" ]; then break; fi
      dir=${dir%/*}
    done
    room=$((room > reserve ? room - reserve : 0))
  fi
  if [ -z "$want" ]; then
    n=$(nproc)
    want=$((room / ${heap:-$floor}))
    ((want <= n)) || want=$n
    ((want >= 1)) || bad "$room bytes of room hold no ${heap:-$floor}-byte heap"
  fi
  if [ -z "$heap" ]; then
    heap=$((room / want))
    ((heap >= floor)) || bad "$room bytes of room over $want processes is under the $floor-byte floor per heap"
  fi
  export BAR_JOBS=$want GC_MAXIMUM_HEAP_SIZE=$heap
  echo "$BAR_NAME: $BAR_JOBS processes at once, each under a GC heap of $GC_MAXIMUM_HEAP_SIZE bytes"
}
