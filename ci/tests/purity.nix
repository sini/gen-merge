# Purity invariant (design spec §5): the gen-merge library (./lib) is nixpkgs-lib-free — it is the
# REPLACEMENT for `lib.evalModules` + `lib.types`-merge, so it must never CALL them. It depends only
# on gen-prelude (+ the injected gen-types leaf checkers). A stray `lib.`/`lib.types`/`evalModules`/
# `nixpkgs` in the library source fails CI.
#
# NB gen-merge legitimately DEFINES `mkOption`/`mkOptionType`/`mkMerge` (its own API — the nixpkgs
# replacements), so those bare tokens are NOT forbidden; only the nixpkgs TETHER is. `evalModules`
# is safe to forbid — it is not an infix of gen-merge's own `evalModuleTree`.
#
# Scope: lib/**.nix + the root flake.nix + default.nix. NOT ci/ (the harness + the oracle's
# reference side legitimately use nixpkgs.lib).
{ genPrelude, lib, ... }:
let
  libDir = ../../lib;

  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  walk =
    dir:
    lib.concatLists (
      lib.mapAttrsToList (
        name: type:
        if type == "directory" then
          walk (dir + "/${name}")
        else if lib.hasSuffix ".nix" name then
          [ (dir + "/${name}") ]
        else
          [ ]
      ) (builtins.readDir dir)
    );

  sources =
    map (p: {
      name = toString p;
      code = stripComments (builtins.readFile p);
    }) (walk libDir)
    ++
      map
        (rel: {
          name = rel;
          code = stripComments (builtins.readFile (../.. + "/${rel}"));
        })
        [
          "flake.nix"
          "default.nix"
        ];

  # The nixpkgs / module-system tether. gen-merge's own API names are intentionally absent.
  forbidden = [
    "nixpkgs"
    "lib.types"
    "lib.mkOption"
    "lib.mkMerge"
    "lib.evalModules"
    "evalModules"
    "{ lib }"
    "{ lib,"
  ];

  violations = lib.concatMap (
    src: map (tok: "${src.name}: '${tok}'") (lib.filter (tok: genPrelude.hasInfix tok src.code) forbidden)
  ) sources;
in
{
  flake.tests.purity.test-library-source-is-nixpkgs-free = {
    expr = violations;
    expected = [ ];
  };
}
