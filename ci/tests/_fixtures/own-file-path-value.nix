# A path module whose `_file` is a PATH VALUE naming a different file than itself.
{
  _file = ./own-file-def.nix;
  config.x = 1;
}
