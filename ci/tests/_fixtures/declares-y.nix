# A module FILE declaring `y`, the definition a copied submodule's module set completes
# (`submodule-laziness.nix`, `copyDeclares`).
{ lib, ... }:
{
  options.y = lib.mkOption { type = lib.types.int; };
}
