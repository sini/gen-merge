# A path module naming itself and importing an unattributed child.
{
  _file = "/real/CH.nix";
  imports = [ { config.bogus = 1; } ];
}
