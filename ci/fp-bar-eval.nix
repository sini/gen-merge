# ONE EVALUATION of the stage-4 replacement-bar arm (den-hoag-stage4-flake-parts-3qh4l, `fp-bar.nix`):
# flake-parts' own `flake.nix`, unmodified, called with its `nixpkgs-lib` input replaced by a hand-built input
# whose `lib` is nixpkgs' (engine "ref"), the lib `modules-sh-lib.nix` builds (engine "gen": nixpkgs' lib with
# `evalModules` and `lib.modules.evalModules` = gen-merge's `evalModuleTree`), or nixpkgs' lib with top-level
# `evalModules` a throw of the run's token (engine "poison"). flake-parts' `lib.nix` receives it exactly where it receives `nixpkgs-lib.lib`
# upstream, so every `evalModules` flake-parts makes runs through the engine named. A real flake's own
# `pkgs.lib` evaluations (treefmt-nix's, a NixOS test's) stay nixpkgs' on every engine: those are stages 2-3.
#
# read:
#   names     every unit's path: each attribute of `dev/tests/nix-unit.nix` that is a test (`test…` with `expr`)
#   templates the names of flake-parts' own `templates` output
#   unit      the unit at `path`, under `tryEval`: `{ ok, unit }`, `ok` the sha256 of `toJSON (canon expr)` or
#             null where forcing it refused, `unit` flake-parts' own verdict (`expr == expected`, or refused for
#             an `expectedError` unit)
#   unitRaw   the same hash without `tryEval`, so a refusal reaches stderr
#   memo      `dev/tests/perSystem-memoize`'s `result`, upstream's own test flake (its traces are on stderr)
#   template  the sha256 of template `name`'s outputs: names per system, x86_64-linux's derivations canon
#   flake     real flake `flake` at `plane`: `names` (its output names) or packages / checks / devShells
#             (x86_64-linux, each name to its drvPath)
# Every read on ref and gen answers `{ v, gen }`: `gen` is the control that flake-parts ran the engine named,
# its `evalFlakeModule` answering fields gen-merge's evaluation has and nixpkgs' does not. A poison read answers
# `v` alone, so the only expression that can throw its token is the read itself.
{
  srcs,
  engine,
  read,
  path ? "[]",
  name ? "",
  flake ? "",
  plane ? "",
  token ? "",
}:
let
  # The sources as strings, as stage 2-3's `import srcs` reads them: `fromJSON` refuses a string with context.
  s = builtins.fromJSON (builtins.unsafeDiscardStringContext (builtins.readFile srcs));
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
    else if engine == "poison" && token != "" then
      nplib.extend (_: _: { evalModules = _: throw token; })
    else
      throw "fp-bar: engine must be ref, gen or poison (with a token), not ${engine}";
  # A flake as `builtins.getFlake` hands it over, minus the fetch: its outputs over the given inputs.
  callFlake =
    src: inputs:
    let
      outputs = (import "${src}/flake.nix").outputs (inputs // { self = me; });
      me = outputs // {
        _type = "flake";
        outPath = src;
        inherit inputs outputs;
        sourceInfo.outPath = src;
      };
    in
    me;
  systems = [
    "x86_64-linux"
    "aarch64-linux"
    "x86_64-darwin"
    "aarch64-darwin"
  ];
  # Explicit `config` and `overlays`, so no host's `~/.config/nixpkgs` reaches an arm.
  nixpkgs = {
    _type = "flake";
    outPath = s.nixpkgs;
    lib = nplib;
    legacyPackages = nplib.genAttrs systems (
      system:
      import s.nixpkgs {
        inherit system;
        config = { };
        overlays = [ ];
      }
    );
  };
  fp = callFlake s.fp {
    nixpkgs-lib = {
      _type = "flake";
      outPath = s.nixpkgs;
      inherit lib;
    };
    inherit nixpkgs;
  };
  # A real flake's inputs, as `fp-bar.nix` wired them off its lock: flake-parts is this arm's, nixpkgs is
  # gen-merge's, and each other input is its own locked tree, called with the inputs its lock node follows.
  wire =
    f:
    {
      flake-parts = fp;
      inherit nixpkgs;
    }
    // builtins.mapAttrs (_: p: callFlake p.src (builtins.mapAttrs (_: _: nixpkgs) p.follows)) f.pins;
  tests = import "${s.fp}/dev/tests/nix-unit.nix" { flake-parts = fp; };
  isTest = n: v: nplib.hasPrefix "test" n && builtins.isAttrs v && v ? expr;
  collect =
    pre: set:
    builtins.concatLists (
      map (
        n:
        let
          v = set.${n};
        in
        if isTest n v then
          [ (pre ++ [ n ]) ]
        else if builtins.isAttrs v && !(v ? expr) then
          collect (pre ++ [ n ]) v
        else
          [ ]
      ) (builtins.attrNames set)
    );
  # flake-parts' own `expr == expected` cannot compare functions either, so `canon` loses nothing it reads.
  canon =
    v:
    if builtins.isAttrs v && (v.type or null) == "derivation" then
      {
        type = "derivation";
        inherit (v) drvPath name system;
      }
    else if builtins.isAttrs v then
      builtins.mapAttrs (_: canon) v
    else if builtins.isList v then
      map canon v
    else if builtins.isFunction v then
      "<lambda>"
    else
      v;
  hashOf = v: builtins.hashString "sha256" (builtins.toJSON (canon v));
  c = nplib.getAttrFromPath (builtins.fromJSON path) tests;
  r = builtins.tryEval (hashOf c.expr);
  tpl = callFlake "${s.fp}/template/${name}" {
    flake-parts = fp;
    inherit nixpkgs;
  };
  perSys = [
    "packages"
    "checks"
    "devShells"
    "apps"
    "formatter"
  ];
  tplVal = builtins.mapAttrs (
    o: v:
    if builtins.elem o perSys then
      builtins.mapAttrs (
        sys: xs:
        if sys == "x86_64-linux" then
          (if o == "formatter" then canon xs else builtins.mapAttrs (_: canon) xs)
        else
          (if o == "formatter" then "fmt" else builtins.attrNames xs)
      ) v
    else if builtins.isAttrs v then
      builtins.attrNames v
    else
      builtins.typeOf v
  ) tpl.outputs;
  real = callFlake s.flakes.${flake}.src (wire s.flakes.${flake});
  reads = {
    names = collect [ ] tests;
    templates = builtins.attrNames fp.outputs.templates;
    unit = {
      ok = if r.success then r.value else null;
      unit = if c ? expectedError then !r.success else r.success && canon c.expr == canon c.expected;
    };
    unitRaw = hashOf c.expr;
    memo = (callFlake "${s.fp}/dev/tests/perSystem-memoize" { flake-parts = fp; }).result;
    template = hashOf tplVal;
    flake =
      if plane == "names" then
        builtins.attrNames real.outputs
      else
        builtins.mapAttrs (_: d: d.drvPath) (real.outputs.${plane}.x86_64-linux or { });
  };
  probe = fp.lib.evalFlakeModule { inputs.self = { }; } { systems = [ ]; };
in
{
  v = reads.${read};
}
// nplib.optionalAttrs (engine != "poison") {
  gen = probe ? deprecations && probe ? freeformConfig;
}
