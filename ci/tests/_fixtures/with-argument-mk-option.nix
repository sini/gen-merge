# network-interfaces.nix's scoping: `with lib; with u;`, so a bare `mkOption` is looked up in the module
# argument first (the innermost `with`), and the node's WHNF reads that argument's key set. A file of its
# own, since a lexical `mkOption` in the cell would win over both `with`s.
{ lib, u, ... }:
with lib;
with u;
{
  options.p = mkOption {
    type = types.int;
    default = 1;
  };
}
