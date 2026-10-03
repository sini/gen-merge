# A FUNCTION path module that declares an option and names itself. The caller supplies `mkOption`
# and `types` through `specialArgs`.
{ mkOption, types, ... }:
{
  _file = "/real/PD.nix";
  options.x = mkOption { type = types.int; };
}
