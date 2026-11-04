# ONE EVALUATION of the stage-2 replacement-bar arm (den-hoag-fwkzx, `nixos-bar.nix`): one NixOS
# configuration through nixpkgs' own `nixos/lib/eval-config.nix`, with `lib` either nixpkgs' (engine
# "ref") or the lib `modules-sh-lib.nix` builds (engine "gen"): nixpkgs' lib with `evalModules` and
# `lib.modules.evalModules` = gen-merge's `evalModuleTree`. `eval-config.nix` takes `lib` as an argument, so
# no copy of nixpkgs is made, and the nested evaluations NixOS makes through its `lib` argument
# (`documentation.nix`'s) run through gen as well.
#
# The configurations are nixos/release.nix's `closures` set, each with that file's `buildFromConfig`
# `rest` module, and `docs` is its `options` job (an empty user module). They are retyped here because
# release.nix builds them through its own `eval-config.nix` call, which takes no `lib`; a relock that
# moves nixpkgs reads release.nix's `closures` against this list.
#
# read:
#   toplevel  config.system.build.toplevel.drvPath
#   options   config.system.build.manual.optionsJSON.drvPath (release.nix's `options` job; cfg "docs")
#   walk      the docs walk, one line per node (below)
#   docsLen   the length of nixpkgs' own `optionAttrSetToDocList` over the same options (conservation)
#   node      the one walk node `route` names, forced without `tryEval`, so its refusal reaches stderr
# Every read answers `{ v, gen }`: `gen` is the control that the arm ran the engine it names, a field
# gen-merge's evaluation answers and nixpkgs' does not.
{
  srcs,
  engine,
  cfg,
  read,
  route ? "[]",
}:
let
  s = import srcs;
  np = s.nixpkgs;
  nplib = import "${np}/lib";
  lib =
    if engine == "ref" then
      nplib
    else if engine == "gen" then
      import s.genLibFile {
        orig = nplib;
        inherit (s)
          libSrc
          genPreludeSrc
          genIdentitySrc
          genGraphSrc
          genTypesSrc
          genAlgebraSrc
          genMemoSrc
          genScopeSrc
          ;
      }
    else
      throw "nixos-bar: engine must be ref or gen, not ${engine}";
  # release.nix's buildFromConfig `rest` module.
  rest =
    { lib, ... }:
    {
      fileSystems."/".device = lib.mkDefault "/dev/sda1";
      fileSystems."/".fsType = lib.mkDefault "auto";
      boot.loader.grub.device = lib.mkDefault "/dev/sda";
    };
  closures = {
    smallContainer =
      { ... }:
      {
        boot.isContainer = true;
        services.openssh.enable = true;
      };
    tinyContainer =
      { ... }:
      {
        boot.isContainer = true;
        imports = [ "${np}/nixos/modules/profiles/minimal.nix" ];
      };
    ec2 =
      { ... }:
      {
        imports = [ "${np}/nixos/modules/virtualisation/amazon-image.nix" ];
      };
    kde =
      { ... }:
      {
        services.xserver.enable = true;
        services.displayManager.sddm.enable = true;
        services.desktopManager.plasma6.enable = true;
      };
    xfce =
      { ... }:
      {
        services.xserver.enable = true;
        services.xserver.desktopManager.xfce.enable = true;
      };
    gnome =
      { ... }:
      {
        services.xserver.enable = true;
        services.displayManager.gdm.enable = true;
        services.desktopManager.gnome.enable = true;
      };
    pantheon =
      { ... }:
      {
        services.xserver.enable = true;
        services.desktopManager.pantheon.enable = true;
      };
    lapp =
      { pkgs, ... }:
      {
        services.httpd.enable = true;
        services.httpd.adminAddr = "foo@example.org";
        services.httpd.enablePHP = true;
        services.postgresql.enable = true;
        services.postgresql.package = pkgs.postgresql;
      };
    docs = { ... }: { };
  };
  ev = import "${np}/nixos/lib/eval-config.nix" {
    inherit lib;
    system = "x86_64-linux";
    modules = [
      closures.${cfg}
      rest
    ];
  };
  # THE DOCS WALK is the shared one (`bar-walk.nix`, which stage 3 imports too), over every entry the
  # manual's `rawOpts` holds, internal and invisible options included (`published = false`). A string path,
  # as `genLibFile` is: `--readonly-mode` refuses the store copy a path literal would make.
  bw = import s.walkFile {
    inherit nplib route;
    options = ev.options;
    published = false;
  };
  reads = {
    toplevel = ev.config.system.build.toplevel.drvPath;
    options = ev.config.system.build.manual.optionsJSON.drvPath;
    inherit (bw) walk node docsLen;
  };
in
{
  v = reads.${read};
  gen = ev ? deprecations && ev ? freeformConfig;
}
