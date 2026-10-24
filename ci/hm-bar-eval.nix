# ONE EVALUATION of the stage-3 replacement-bar arm (den-hoag-stage3-home-manager-nk0o6, `hm-bar.nix`):
# home-manager's own drivers, unmodified but for `hm-bar.patch`, run on gen-merge's nixpkgs with `lib` either
# nixpkgs' (engine "ref") or the lib `modules-sh-lib.nix` builds (engine "gen": nixpkgs' lib with `evalModules`
# and `lib.modules.evalModules` = gen-merge's `evalModuleTree`), handed in as `pkgs.lib`. home-manager extends that `lib`
# itself (`modules/lib/stdlib-extended.nix`), so every evaluation it makes runs through the engine named.
#
#   tests  home-manager's `tests/default.nix` (patched to return nmt's argument record) and nmt's
#          `evalTest`, re-stated: nmt's init module, `nmt.nix`, the test, and the driver's `modules`.
#   docs   `docs/default.nix`'s `_internal.<set>.docsEval` (patched to export it), set hm | nixos | darwin.
#
# read:
#   names   every test's name (the attribute names of the driver's `tests`, the x86_64-linux suite)
#   chunk   the tests `tests` (a JSON list) in one evaluation, one line each, `<name>\tok:<sha256 of its
#           value>` or `<name>\terr` where forcing it refused (`tryEval`)
#   test    the one test `tests` names, its value's sha256 forced without `tryEval`, so a refusal reaches
#           stderr
#   walk    the docs walk over `set` (`bar-walk.nix`, published entries only)
#   docsLen the conservation read for that walk
#   node    the one walk node `route` names, forced without `tryEval`
# A test's value is `{act, nFiles, files}`: what the generation writes (`home.file`, each target with its
# text's sha256 or its source), and `act`, `home.activationPackage.drvPath`, which is EVIDENCE riding in the
# value (ADR-0039), never the acceptance read. Every read answers `{ v, gen }`: `gen` is the control that
# the arm ran the engine it names, a field gen-merge's evaluation answers and nixpkgs' does not.
{
  srcs,
  engine,
  read,
  set ? "hm",
  tests ? "[]",
  route ? "[]",
}:
let
  s = import srcs;
  nplib = import "${s.nixpkgs}/lib";
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
      throw "hm-bar: engine must be ref or gen, not ${engine}";
  # Explicit `config` and `overlays`, as home-manager's flake hands its own suite `legacyPackages`: no
  # host's `~/.config/nixpkgs` reaches an arm.
  pkgs =
    import s.nixpkgs {
      system = "x86_64-linux";
      config = { };
      overlays = [ ];
    }
    // {
      inherit lib;
    };
  t = import "${s.hm}/tests" { inherit pkgs; };
  evalTest =
    name:
    t.lib.evalModules {
      modules = [
        (
          { config, ... }:
          {
            nmt.name = name;
            nmt.tested = t.lib.getAttrFromPath t.testedAttrPath config;
          }
        )
        "${s.nmt}/nmt.nix"
        t.tests.${name}
      ]
      ++ t.modules;
    };
  fileVal =
    f:
    {
      inherit (f) target;
    }
    // (
      if f.text or null != null then
        { text = builtins.hashString "sha256" f.text; }
      else
        { source = toString f.source; }
    );
  valOf =
    name:
    let
      cfg = (evalTest name).config;
    in
    builtins.hashString "sha256" (
      builtins.toJSON {
        act = cfg.home.activationPackage.drvPath;
        nFiles = builtins.length (builtins.attrNames cfg.home.file);
        files = builtins.hashString "sha256" (
          builtins.toJSON (builtins.mapAttrs (_: fileVal) cfg.home.file)
        );
      }
    );
  names = builtins.fromJSON tests;
  docsEval =
    (import "${s.hm}/docs" {
      inherit pkgs;
      inherit (nplib.importJSON "${s.hm}/release.json") release isReleaseBranch;
    })._internal.${
      {
        hm = "hmOptionsDocs";
        nixos = "nixosOptionsDocs";
        darwin = "nixDarwinOptionsDocs";
      }
      .${set}
    }.docsEval;
  # `buildOptionsDocs`' own `includeModuleSystemOptions`: true for the hm set only.
  bw = import s.walkFile {
    inherit nplib route;
    options = if set == "hm" then docsEval.options else removeAttrs docsEval.options [ "_module" ];
    published = true;
  };
  isGen = e: e ? deprecations && e ? freeformConfig;
  reads = {
    names = builtins.attrNames t.tests;
    chunk = builtins.concatStringsSep "\n" (
      map (
        n:
        let
          r = builtins.tryEval (valOf n);
        in
        if r.success then "${n}\tok:${r.value}" else "${n}\terr"
      ) names
    );
    test = valOf (builtins.head names);
    inherit (bw) walk node docsLen;
  };
in
{
  v = reads.${read};
  gen =
    if read == "walk" || read == "docsLen" || read == "node" then
      isGen docsEval
    else
      isGen (evalTest (builtins.head (if names == [ ] then reads.names else names)));
}
