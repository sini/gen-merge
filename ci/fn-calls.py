"""fn-calls.py <stats.json> <modules.nix> <binding>...: each binding's call count from an evaluator's NIX_COUNT_CALLS
statistics, one per line. A binding is found by its definition line (`<name> =` at two or four spaces) in the lib text
the cell evaluated, and counted at the innermost lambda of the curried header on the next line, which counts every
full application. A stats file with no `functions`, or a binding the lib does not define, cannot be measured: the
script says so on stderr and exits 2, never printing a zero for it."""

import json
import re
import sys

stats = json.load(open(sys.argv[1]))
src = open(sys.argv[2]).read().split("\n")
fns = stats.get("functions")
if fns is None:
    sys.exit(f"fn-calls: {sys.argv[1]} carries no `functions` (NIX_COUNT_CALLS unset?): cannot measure")
for name in sys.argv[3:]:
    lines = [i + 1 for i, line in enumerate(src) if re.match(rf"^ {{2,4}}{re.escape(name)} =$", line)]
    if len(lines) != 1:
        sys.exit(f"fn-calls: `{name}' is defined {len(lines)} times in {sys.argv[2]}: cannot measure")
    header = lines[0] + 1
    hits = [f for f in fns if f.get("line") == header and f.get("file", "") == sys.argv[2]]
    if not hits:
        print(0)
        continue
    inner = max(h["column"] for h in hits)
    print(sum(h["count"] for h in hits if h["column"] == inner))
