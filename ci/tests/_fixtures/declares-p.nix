# A module FILE declaring one option, so a docs entry has a declaring file to name (`declarations`).
# Engine-agnostic: the caller supplies `lib` through `specialArgs`.
{ lib, ... }:
{
  options.p = lib.mkOption {
    type = lib.types.str;
    default = "d";
    description = "declared in a file";
  };
}
