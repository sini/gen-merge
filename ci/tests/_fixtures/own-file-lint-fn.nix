# The same module as a FUNCTION path module reading `options`: the lint applies no module, so its
# `options-introspection` finding names the path where the engine names the in-file `_file`.
{ options, ... }:
{
  _file = "/real/LF.nix";
  config.xs = {
    _type = "order";
    priority = 1500;
    content = [ "z" ];
  };
}
