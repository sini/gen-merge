# barBudget [<jobs>]: a bar phase's concurrency and GC heap, from the memory this process may actually use.
# Exports GC_MAXIMUM_HEAP_SIZE and sets barJobs. Without <jobs> it also exports BAR_JOBS (`par`'s bound); with
# <jobs> (a serial phase) the phase runs that many and BAR_JOBS is left as it was. The heap is the evaluator's GC
# bound, not an RSS bound, and the reserve is a heuristic for the memory outside it, not a guarantee: the scope's
# own limit, not this budget, is what the kernel enforces.
#
# The room is the least of the host's MemAvailable and, for the process's own cgroup (v2) and EVERY ancestor that
# limits memory, memory.max or memory.high less that cgroup's memory.current. A scope's cap binds as surely as
# the host's memory does, and the cap is shared with what the scope already holds. RESERVE bytes of the room are
# left to the shell, jq and each evaluator's non-GC memory. Defaults, applied only where unset:
#   jobs = min(nproc, room / FLOOR), heap = room / jobs (FLOOR: the heap the measured BAR_JOBS=4 BAR_HEAP=2.5GiB
#   workaround served the full register at, under a 12G scope).
# OVERRIDES are the operator's responsibility: BAR_JOBS and BAR_HEAP, when set, must be positive integers (anything
# else fails closed) and are honoured as given. With ONE set, the other is still derived from the room, so the
# product stays bounded by it; with BOTH set nothing is read and nothing bounds them but the operator.
# SUPPORTED: a process in the initial cgroup namespace (a host, a VM, a CI runner), where every ancestor is visible.
# Inside any other cgroup namespace (a container) ancestors above its root are hidden, so it fails closed there.
# FAILS CLOSED (exit 2, CONTROL FAILED, never a verdict) when the room cannot be read (a cgroup namespace other
# than the initial one; no cgroup v2 entry; a cgroup path that is not absolute and canonical; no
# cgroup2 mount at /sys/fs/cgroup whose root is `/`, so a cgroup namespace viewing an outer mount, whose own path
# reads `/` there and would name the host's root, refuses; a missing cgroup directory; an unreadable or malformed
# limit) or is too small for one FLOOR heap per job,
# because guessing would be the overcommit this replaces. Set BAR_JOBS and BAR_HEAP to run anyway.
# BAR_PROCFS and BAR_SYSFS move /proc and /sys/fs/cgroup, for `bar-budget-cells.bash` only.
barBudget() {
  local floor=2684354560 reserve=2147483648 proc=${BAR_PROCFS:-/proc} sys=${BAR_SYSFS:-/sys/fs/cgroup}
  local want=${1:-${BAR_JOBS:-}} heap=${BAR_HEAP:-} room by=MemAvailable rel dir f lim cur n
  bad() {
    echo "$BAR_NAME: CONTROL FAILED: memory budget: $* (set BAR_JOBS and BAR_HEAP to override)" >&2
    exit 2
  }
  # Digit counts bound the values before any arithmetic touches them: at most 9999 jobs and 10^16 bytes of heap.
  [ -z "$want" ] || [[ $want =~ ^[1-9][0-9]{0,3}$ ]] || bad "BAR_JOBS (or the phase's jobs) reads '$want', not an integer 1-9999"
  [ -z "$heap" ] || [[ $heap =~ ^[1-9][0-9]{0,15}$ ]] || bad "BAR_HEAP reads '$heap', not an integer of bytes 1-9999999999999999"
  if [ -n "$want" ] && [ -n "$heap" ]; then
    by="BAR_JOBS and BAR_HEAP, the operator's"
  else
    # The kB field is read as text and scaled here, so no awk number formatting can reach the arithmetic.
    room=$(awk '/^MemAvailable:/ { print $2 }' "$proc/meminfo" 2>/dev/null || true)
    [[ $room =~ ^[0-9]{1,15}$ ]] || bad "no MemAvailable in $proc/meminfo (read: '$room')"
    room=$((room * 1024))
    n=$(readlink "$proc/self/ns/cgroup" 2>/dev/null || true)
    # 4026531835 is the kernel's fixed inode of the initial cgroup namespace (PROC_CGROUP_INIT_INO).
    [ "$n" = "cgroup:[4026531835]" ] || bad "the process is not in the initial cgroup namespace (read: '$n'), so ancestors may be hidden"
    n=$(grep -c '^0::' "$proc/self/cgroup" 2>/dev/null || true)
    [ "$n" = 1 ] || bad "$proc/self/cgroup holds $n cgroup v2 entries, not 1"
    rel=$(sed -n 's/^0:://p' "$proc/self/cgroup")
    [[ $rel =~ ^(/[^/]+)*/?$ && ! $rel =~ (^|/)\.\.?(/|$) ]] || bad "the cgroup path '$rel' is not absolute and canonical"
    n=$(awk -v m="$sys" '{ for (i = 7; i < NF; i++) if ($i == "-") break } $(i + 1) == "cgroup2" && $5 == m { print $4 }' \
      "$proc/self/mountinfo" 2>/dev/null || true)
    [ "$n" = / ] || bad "no cgroup2 mount at $sys with root / in $proc/self/mountinfo (read: '${n//$'\n'/ }'), so $rel cannot be placed"
    dir=$sys${rel%/}
    [ -d "$dir" ] || bad "the process's cgroup $dir does not exist"
    while :; do
      for f in memory.max memory.high; do
        [ -e "$dir/$f" ] || continue
        read -r lim 2>/dev/null <"$dir/$f" || bad "$dir/$f is unreadable"
        [ "$lim" = max ] && continue
        [[ $lim =~ ^[0-9]{1,18}$ ]] || bad "$dir/$f reads '$lim'"
        read -r cur 2>/dev/null <"$dir/memory.current" && [[ $cur =~ ^[0-9]{1,18}$ ]] ||
          bad "$dir limits memory but its memory.current is unreadable"
        if ((lim - cur < room)); then room=$((lim > cur ? lim - cur : 0)) by="$dir/$f $lim less memory.current $cur"; fi
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
  barJobs=$want
  export GC_MAXIMUM_HEAP_SIZE=$heap
  [ -n "${1:-}" ] || export BAR_JOBS=$want
  echo "$BAR_NAME: $barJobs processes at once, each under a GC heap of $GC_MAXIMUM_HEAP_SIZE bytes (room ${room:--} after the reserve, bound by $by)"
}
