# module-graph fixture: the other half of a path import cycle.
{
  imports = [ ./module-graph-cyc-a.nix ];
  l = [ "b" ];
}
