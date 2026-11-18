# The gating oracle of `barBudget` (`bar-budget.bash`), the memory budget hm-bar and fp-bar size their processes by:
# its cells (`bar-budget-cells.bash`) over planted /proc and cgroup trees, a sandboxed check, the same in every CI
# column. This derivation holds their COUNT, with equality, because a run that silently collects fewer cells reads
# exactly like a green.
_: {
  perSystem =
    { pkgs, ... }:
    {
      checks.bar-budget = pkgs.runCommand "gen-merge-bar-budget-cells" { } ''
        rc=0
        bash ${./bar-budget-cells.bash} ${./bar-budget.bash} > cells.out 2>&1 || rc=$?
        cat cells.out
        n=$(grep -c '^PASS ' cells.out || true)
        ! grep -q '^FAIL ' cells.out || rc=1
        [ "$rc" = 0 ] || { echo "bar-budget: a cell failed"; exit 1; }
        [ "$n" = 27 ] || { echo "bar-budget: collected $n cells, want exactly 27"; exit 1; }
        echo "bar-budget: 27 cells" > $out
      '';
    };
}
