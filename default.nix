# Standalone (non-flake) entry. Flake consumers should use the `.lib` output.
#
# gen-merge is a function of three named values — gen-prelude (the pure utility base), gen-types
# (the leaf checkers) and gen-memo (the incremental plane's reuse DECISION — ADR-0008 item 2).
# Defaults fetch the flake-locked revs (content-addressed via narHash, so the plain-import path
# stays pure and in lockstep with the flake output; per the gen root-file convention). Pass any
# explicitly to override (e.g. a local gen-types checkout).
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
  # Through gen-types' OWN standalone entry rather than its `./lib`, so gen-types' own dependencies
  # are satisfied from gen-types' lock. Reaching for `./lib` obliged this file to name that
  # library's whole formal list by hand — and a hand-picked list is a SECOND SIGNATURE that
  # nothing compares against the first: gen-types gained `identity` and this site, still passing
  # `prelude` alone, threw on every forced standalone import while the flake path stayed green.
  # Through the entry, a formal gained downstream is defaulted downstream and the divergence
  # cannot form.
  types ? import "${fetch "gen-types"}" { inherit prelude; },
  # Same precedent as `types` above — gen-memo's own standalone entry, so its `graph` dep is
  # satisfied from gen-memo's lock rather than hand-named here.
  memo ? import "${fetch "gen-memo"}" { inherit prelude; },
}:
import ./lib { inherit prelude types memo; }
