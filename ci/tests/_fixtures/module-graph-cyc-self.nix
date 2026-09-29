# module-graph fixture: a path module importing itself.
{
  imports = [ ./module-graph-cyc-self.nix ];
  l = [ "s" ];
}
