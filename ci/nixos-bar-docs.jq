# The docs walk's two outputs ($ref, $gen: the `walk` read, one slurped value each) as one record per node:
# `{key: {kind: "doc", set?, name, n}, ref, gen}` (`set`, the walk's option set, only where $set is not ""),
# an arm being `{refused: false, v}` or
# `{refused: true, step, route}`, and null where that walk has no such node. `n` is the node's occurrence
# ordinal among the walk's nodes of the same name (a name may occur twice: `services.tuned.settings._module.*`).
def nodes:
  if . == "" then [] else split("\n") end
  | to_entries
  | map(.key as $i | .value | split("\t") as $f | { i: $i, name: $f[0], v: $f[1], route: (if ($f | length) > 2 then ($f[2] | fromjson) else null end) })
  | group_by(.name)
  | map(sort_by(.i) | to_entries | map(.value + { n: .key }))
  | add // []
  | sort_by(.i)
  | map({
      key: ({ kind: "doc" } + (if $set == "" then { } else { $set } end) + { name, n }),
      arm: (if .v | startswith("err:") then { refused: true, step: (.v | ltrimstr("err:")), route } else { refused: false, v } end)
    });
($ref[0].v | nodes) as $R
| ($gen[0].v | nodes) as $G
| ($G | map({ key: (.key | tojson), value: .arm }) | from_entries) as $GM
| ($R | map({ key: (.key | tojson), value: true }) | from_entries) as $RS
| ($R[] | { key, ref: .arm, gen: ($GM[.key | tojson] // null) }),
  ($G[] | select($RS[.key | tojson] | not) | { key, ref: null, gen: .arm })
