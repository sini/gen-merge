# The cells of `checks.bar-budget` (`bar-budget.nix`): `barBudget` (`bar-budget.bash`) over planted /proc and
# /sys/fs/cgroup trees, with nproc pinned at 32 (cortex's). Prints `PASS <cell>` or `FAIL <cell>: <why>`, one line
# per cell; the derivation holds their count.
#   bar-budget-cells.bash <bar-budget.bash>
set -u
src=$1
w=$(mktemp -d)
G=1073741824
# The function under test, and its MUTANT: the ancestor walk cut to the leaf, which the nested-limit cells must catch.
cp "$src" "$w/budget.bash"
sed 's#^      dir=\${dir%/\*}$#      break#' "$src" >"$w/mutant.bash"
cmp -s "$src" "$w/mutant.bash" && { echo "FAIL mutant: the sed did not cut the ancestor walk"; exit 1; }

# tree <name> <MemAvailable GiB, or -> <cgroup file line, or -> [<dir> <file> <value>]...: a planted host.
# A value `DIR` makes the file a directory (unreadable as a file).
tree() {
  local t=$w/$1 d f v
  mkdir -p "$t/proc/self/ns" "$t/sys"
  ln -s "${CGNS:-cgroup:[4026531835]}" "$t/proc/self/ns/cgroup"
  if [ "$2" != - ]; then echo "MemAvailable: $(($2 * 1048576)) kB" >"$t/proc/meminfo"; else : >"$t/proc/meminfo"; fi
  if [ "$3" != - ]; then echo "$3" >"$t/proc/self/cgroup"; else echo "4:memory:/legacy" >"$t/proc/self/cgroup"; fi
  # The cgroup2 mount at the planted /sys/fs/cgroup, its root `/` unless MOUNT_ROOT says otherwise (`none`: no line).
  [ "${MOUNT_ROOT:-/}" = none ] || echo "28 52 0:3 ${MOUNT_ROOT:-/} $t/sys rw,nosuid - cgroup2 cgroup2 rw,nsdelegate" >"$t/proc/self/mountinfo"
  echo "29 52 0:4 / $t/proc rw - proc proc rw" >>"$t/proc/self/mountinfo"
  shift 3
  while [ $# -gt 0 ]; do
    d=$t/sys$1 f=$2 v=$3
    shift 3
    mkdir -p "$d"
    if [ "$v" = DIR ]; then mkdir -p "$d/$f"; else echo "$v" >"$d/$f"; fi
  done
}
# run <impl> <tree> [<jobs arg>] (env BAR_JOBS / BAR_HEAP from the caller): prints "<rc> <jobs> <heap>".
run() {
  local impl=$1 t=$w/$2
  shift 2
  (
    set -euo pipefail
    nproc() { echo 32; }
    BAR_NAME=cell BAR_PROCFS=$t/proc BAR_SYSFS=$t/sys
    # shellcheck disable=SC1090
    source "$w/$impl.bash"
    barBudget "$@" >/dev/null 2>"$w/err"
    echo "0 $barJobs $GC_MAXIMUM_HEAP_SIZE${PRINT_BAR_JOBS:+ ${BAR_JOBS:-unset}}"
  ) || echo "$? - -"
}
# want <cell> <got> <rc> [<jobs> <heap>]: the cell's verdict.
want() {
  local c=$1 got=$2 rc=$3
  if [ "$rc" != 0 ]; then
    [ "${got%% *}" = "$rc" ] && echo "PASS $c" || echo "FAIL $c: want exit $rc, got '$got'"
  else
    [ "$got" = "0 $4 $5${6:+ $6}" ] && echo "PASS $c" || echo "FAIL $c: want '0 $4 $5${6:+ $6}', got '$got' ($(cat "$w/err"))"
  fi
}

# CONTROL: no limit anywhere, so the host's room (64 - 2 GiB reserve) decides: 24 heaps of the floor, not nproc's 32.
tree unlimited 64 0::/user.slice/run.scope /user.slice/run.scope memory.max max /user.slice/run.scope memory.current 0
want unlimited "$(run budget unlimited)" 0 24 $((62 * G / 24))
# THE DEFECT'S CASE: cortex's 125 GiB host under a 12G scope already holding 1 GiB. The old default was 32 x 3.9 GiB.
tree scope12 120 0::/user.slice/run.scope /user.slice/run.scope memory.max $((12 * G)) /user.slice/run.scope memory.current $((1 * G))
want scope12 "$(run budget scope12)" 0 3 $((9 * G / 3))
# NESTED: the slice above the scope caps tighter (8 GiB holding 2) than the scope itself (12 GiB): 6 - 2 = 4 GiB, one heap.
tree nested 120 0::/s.slice/run.scope /s.slice/run.scope memory.max $((12 * G)) /s.slice/run.scope memory.current 0 \
  /s.slice memory.max $((8 * G)) /s.slice memory.current $((2 * G))
want nested "$(run budget nested)" 0 1 $((4 * G))
# The mutant (leaf only) reads the scope's 12 GiB and answers otherwise: the cell above is what catches it.
got=$(run mutant nested)
[ "$got" != "0 1 $((4 * G))" ] && echo "PASS nested-mutant" || echo "FAIL nested-mutant: the leaf-only mutant passes the nested cell"

# memory.high binds like memory.max.
tree high 120 0::/run.scope /run.scope memory.max $((12 * G)) /run.scope memory.high $((7 * G)) /run.scope memory.current 0
want high "$(run budget high)" 0 2 $((5 * G / 2))
# A namespaced root (`0::/`) whose own top directory carries the limit.
tree nsroot 120 0::/ / memory.max $((7 * G)) / memory.current 0
want nsroot "$(run budget nsroot)" 0 2 $((5 * G / 2))
# A limit already used up: the room is 0, never negative.
tree full 120 0::/run.scope /run.scope memory.max $((4 * G)) /run.scope memory.current $((5 * G))
want full "$(run budget full)" 2
# FAILS CLOSED: too small for one floor heap; no v2 entry (a v1 host); a missing cgroup directory; an unreadable,
# a malformed limit; a limit with no readable memory.current; no MemAvailable.
tree tiny 120 0::/run.scope /run.scope memory.max $((3 * G)) /run.scope memory.current 0
want tiny "$(run budget tiny)" 2
tree v1 120 -
want v1 "$(run budget v1)" 2
tree nodir 120 0::/gone.scope
want nodir "$(run budget nodir)" 2
tree unreadable 120 0::/run.scope /run.scope memory.max DIR /run.scope memory.current 0
want unreadable "$(run budget unreadable)" 2
tree malformed 120 0::/run.scope /run.scope memory.max 12G /run.scope memory.current 0
want malformed "$(run budget malformed)" 2
tree nocurrent 120 0::/run.scope /run.scope memory.max $((12 * G))
want nocurrent "$(run budget nocurrent)" 2
tree nomeminfo - 0::/run.scope /run.scope memory.max max
want nomeminfo "$(run budget nomeminfo)" 2
# A cgroup namespace viewing the outer mount (bitstream, `unshare -Ur --cgroup` under a 12G scope: root
# /../../../../.., own path `/`), which would otherwise read the host root's (absent) limit; no cgroup2 mount.
MOUNT_ROOT=/../../../../.. tree outerns 120 0::/ / memory.current 0
want outerns "$(run budget outerns)" 2
MOUNT_ROOT=none tree nomount 120 0::/run.scope /run.scope memory.max max
want nomount "$(run budget nomount)" 2
# OVERRIDES: both set are honoured with nothing read (the v1 host would fail closed); one set fills the other.
want override-both "$(BAR_JOBS=4 BAR_HEAP=$((5 * G / 2)) run budget v1)" 0 4 $((5 * G / 2))
want override-jobs "$(BAR_JOBS=2 run budget scope12)" 0 2 $((9 * G / 2))
want override-heap "$(BAR_HEAP=$((4 * G)) run budget scope12)" 0 2 $((4 * G))
want override-jobs-floor "$(BAR_JOBS=8 run budget scope12)" 2
# INVALID OVERRIDES fail closed: zero, negative, non-numeric, a unit suffix.
want override-jobs-zero "$(BAR_JOBS=0 run budget scope12)" 2
want override-jobs-text "$(BAR_JOBS=four run budget scope12)" 2
want override-heap-zero "$(BAR_HEAP=0 run budget scope12)" 2
want override-heap-negative "$(BAR_HEAP=-1 run budget scope12)" 2
want override-heap-suffix "$(BAR_HEAP=2G BAR_JOBS=4 run budget scope12)" 2
# Overrides past the digit bounds refuse before any arithmetic (a 2^63 heap would wrap).
want override-jobs-huge "$(BAR_JOBS=10000 run budget scope12)" 2
want override-heap-huge "$(BAR_HEAP=9223372036854775808 BAR_JOBS=1 run budget scope12)" 2
# A cgroup namespace other than the initial one (a container, or `unshare --cgroup` with cgroup2 remounted, whose
# root reads `/` and hides the tighter ancestors above it) refuses, even with an otherwise clean tree.
CGNS='cgroup:[4026532999]' tree container 120 0::/ / memory.current 0
want container "$(run budget container)" 2
# A cgroup path that is relative, carries `..` or `.`, or doubles a slash refuses, so the ancestor walk is only
# ever over the canonical path below the mount.
tree relpath 120 0::run.scope /run.scope memory.max max
want relpath "$(run budget relpath)" 2
tree dotdot 120 0::/a/../.. /a memory.max max
want dotdot "$(run budget dotdot)" 2
tree dot 120 0::/a/./b /a/b memory.max max
want dot "$(run budget dot)" 2
tree dblslash 120 0::/a//b /a/b memory.max max
want dblslash "$(run budget dblslash)" 2
# A MemAvailable past 15 digits of kB (10^10 GiB), and a limit past 18 digits, refuse.
tree hugemem 10000000000 0::/run.scope /run.scope memory.max max
want hugemem "$(run budget hugemem)" 2
tree hugelim 120 0::/run.scope /run.scope memory.max 9999999999999999999 /run.scope memory.current 0
want hugelim "$(run budget hugelim)" 2
# PHASE 2 (`barBudget 1`) leaves BAR_JOBS as phase 1 exported it, unset or the operator's.
want phase2-keeps-unset "$(PRINT_BAR_JOBS=1 run budget scope12 1)" 0 1 $((9 * G)) unset
want phase2-keeps-operator "$(PRINT_BAR_JOBS=1 BAR_JOBS=7 run budget scope12 1)" 0 1 $((9 * G)) 7
want phase1-exports "$(PRINT_BAR_JOBS=1 run budget scope12)" 0 3 $((9 * G / 3)) 3
# PHASE 2 (`barBudget 1`): one process, all the room.
want phase2 "$(run budget scope12 1)" 0 1 $((9 * G))
want phase2-tiny "$(run budget tiny 1)" 2
rm -rf "$w"
