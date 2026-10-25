{
  imports = [
    {
      _file = "y.nix";
      x = [ "y" ];
    }
  ];
  x = [ "def" ];
}
