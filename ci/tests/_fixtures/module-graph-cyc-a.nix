# module-graph fixture: one half of a path import cycle.
{
  imports = [ ./module-graph-cyc-b.nix ];
  l = [ "a" ];
}
