# ONE EVALUATION of the stage-2 replacement-bar arm (den-hoag-fwkzx, `nixos-bar.nix`): one NixOS
# configuration through nixpkgs' own `nixos/lib/eval-config.nix`, with `lib` either nixpkgs' (engine
# "ref") or the lib `modules-sh-lib.nix` builds (engine "gen"): nixpkgs' lib with ONE binding replaced,
# top-level `evalModules` = gen-merge's `evalModuleTree`. `eval-config.nix` takes `lib` as an argument, so
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
  # THE DOCS WALK. Each node is exactly the entry nixpkgs' `optionAttrSetToDocList` emits for that
  # option: nixpkgs' own `optionAttrSetToDocList'`, called one option at a time with its sub-option
  # recursion cut, so the walk recurses itself, under `tryEval`, and one refusing node cannot hide the
  # rest. It reads internal and invisible options too, every entry the manual's `rawOpts` holds.
  # A line is `<name>\tok:<sha256 of the entry's JSON>`, or `<name>\terr:<step>\t<route>` where forcing
  # it refused; `route` is the JSON path back to it (a key, or null for a `getSubOptions` step), for the
  # `node` read. A group whose keys refuse is `<path>.<keys>`, a sub-option set that refuses
  # `<name>.<sub>`.
  one =
    opt:
    builtins.head (
      nplib.optionAttrSetToDocList' [ ] {
        x = opt // {
          type = opt.type // {
            getSubOptions = _: { };
          };
        };
      }
    );
  isOpt = t: nplib.isOption t;
  nameOf = t: nplib.showOption t.loc;
  subsOf =
    t:
    let
      v = t.visible or true;
      shown = if builtins.isBool v then v else v == "transparent";
    in
    if shown then t.type.getSubOptions t.loc else { };
  forced = v: builtins.seq v v;
  walk =
    let
      dot = nplib.concatStringsSep ".";
      err = nm: step: rt: [ "${nm}\terr:${step}\t${builtins.toJSON rt}" ];
      node =
        pre: rt: t:
        let
          o = builtins.tryEval (isOpt t);
        in
        if !o.success then
          err (dot pre) "isopt" rt
        else if o.value then
          let
            e = builtins.tryEval (forced (builtins.toJSON (one t)));
            n = builtins.tryEval (nameOf t);
            nm = if n.success then n.value else dot pre;
            ss = builtins.tryEval (
              let
                x = subsOf t;
              in
              builtins.seq (builtins.attrNames x) x
            );
          in
          (if e.success then [ "${nm}\tok:${builtins.hashString "sha256" e.value}" ] else err nm "opt" rt)
          ++ (if !ss.success then err "${nm}.<sub>" "sub" rt else node pre (rt ++ [ null ]) ss.value)
        else if !(builtins.isAttrs t) then
          [ ]
        else
          let
            ks = builtins.tryEval (builtins.attrNames t);
          in
          if !ks.success then
            err "${dot pre}.<keys>" "keys" rt
          else
            builtins.concatMap (k: node (pre ++ [ k ]) (rt ++ [ k ]) t.${k}) ks.value;
    in
    builtins.concatStringsSep "\n" (node [ ] [ ] ev.options);
  # The node `route` names, reached by the steps the walk took, and the step that refused there forced.
  node =
    let
      rt = builtins.fromJSON route;
      step = builtins.head rt;
      at = builtins.foldl' (t: k: if k == null then subsOf t else t.${k}) ev.options (builtins.tail rt);
    in
    if step == "isopt" then
      isOpt at
    else if step == "opt" then
      forced (builtins.toJSON (one at))
    else if step == "sub" then
      builtins.attrNames (subsOf at)
    else if step == "keys" then
      builtins.attrNames at
    else
      throw "nixos-bar: unknown node step ${builtins.toJSON step}";
  reads = {
    toplevel = ev.config.system.build.toplevel.drvPath;
    options = ev.config.system.build.manual.optionsJSON.drvPath;
    inherit walk node;
    docsLen = builtins.length (nplib.optionAttrSetToDocList ev.options);
  };
in
{
  v = reads.${read};
  gen = ev ? deprecations && ev ? freeformConfig;
}
