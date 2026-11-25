# The declaration fold ASKS a joined record's shorthand flag; it never forces it (den-hoag-fsgy9). A gen
# `refusingSubmodule` (flag true) redeclared beside a nixpkgs `submoduleWith { }` (flag false) joins to nixpkgs' record,
# whose flag is nixpkgs' lazy conflict refusal, read only where nixpkgs merges a definition or a default
# (`../tests-error.nix`, `fold-hosted-flag-ask`, holds that refusal). The record's metadata is served as nixpkgs' own
# engine serves it. Red where the fold's hosting predicate forces the flag: `.name` throws the conflict, both orders.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  stating = gm.refusingSubmodule null [ "config" ] [ ];
  foreign = nixpkgsLib.types.submoduleWith { modules = [ ]; };
  name =
    ts:
    (gm.evalModuleTree { } (
      map (type: {
        options.x = gm.mkOption { inherit type; };
      }) ts
    )).options.x.type.name;
in
{
  flake.tests.fold-hosted-flag-ask = {
    test-a-conflicting-flag-join-serves-its-name-gen-first = {
      expr = name [
        stating
        foreign
      ];
      expected = "submodule";
    };
    test-a-conflicting-flag-join-serves-its-name-foreign-first = {
      expr = name [
        foreign
        stating
      ];
      expected = "submodule";
    };
  };
}
