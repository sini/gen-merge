# A path leaf that imports to a FUNCTION module — the path-to-function classification fixture
# (design spec §3: a path is classified by its imported RESULT; a function result is DIRTY). Never
# applied by `classifyModule` (classification reads the import result's shape only), so the formals
# are immaterial; `config, ...` is the ordinary config-reading shape a dirty module has.
{ config, ... }: { }
