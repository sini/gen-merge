# Standalone (non-flake) entry. Flake consumers should use the `.lib` output.
#
# gen-merge is a function of two named values — gen-prelude (the pure utility base) and gen-types
# (the leaf checkers). Defaults fetch the flake-locked revs (content-addressed via narHash, so the
# plain-import path stays pure and in lockstep with the flake output; per the gen root-file
# convention). Pass either explicitly to override (e.g. a local gen-types checkout).
{
  lock ? builtins.fromJSON (builtins.readFile ./flake.lock),
  fetch ?
    name:
    builtins.fetchTree (
      let
        node = lock.nodes.${lock.nodes.root.inputs.${name}}.locked;
      in
      node
    ),
  prelude ? import "${fetch "gen-prelude"}/lib",
  types ? import "${fetch "gen-types"}/lib" { inherit prelude; },
}:
import ./lib { inherit prelude types; }
