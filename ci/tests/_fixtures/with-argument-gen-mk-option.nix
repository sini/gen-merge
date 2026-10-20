# The gen-grammar twin of with-argument-mk-option.nix: `with gm; with u;`.
gm:
{ u, ... }:
with gm;
with u;
{
  options.p = mkOption {
    type = types.int;
    default = 1;
  };
}
