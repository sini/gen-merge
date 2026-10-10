# The rows of a baseline change that LOWER the bar: $old and $new are two revisions of the register.
# A key falls when its rank drops (PASS > PASS-CLASS > FAIL) or when a PASS / PASS-CLASS key is gone
# (an upstream edit that re-keys an assertion is a disappearance plus an UNBASELINED newcomer, so it
# falls here too). One line per fallen key: `<id>\t<old verdict>\t<new verdict, or ABSENT>`.
def id: [.kind, .env, .argv] | tojson;
def rank: { "PASS": 2, "PASS-CLASS": 1, "FAIL": 0 }[.];
($new | map({ key: (.key | id), value: .verdict }) | from_entries) as $N
| $old[]
| (.key | id) as $i
| .verdict as $was
| ($N[$i] // "ABSENT") as $now
| select(if $now == "ABSENT" then ($was | rank) > 0 else ($now | rank) < ($was | rank) end)
| "\($i)\t\($was)\t\($now)"
