# Redeclares `_module.args` read-only and defines it: the readOnly refusal names this module.
{ mkOption, ... }:
{
  _file = "/real/AR.nix";
  options._module.args = mkOption { readOnly = true; };
  config._module.args.pkgs = "P";
}
