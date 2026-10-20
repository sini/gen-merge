# THE ENGINE'S OWN OPTION NAMES (`engineOptionNames`, den-hoag-jbddy) — the names an option tree serves
# beside the declared ones, per shape, read without evaluating a submodule. Each shape's record is the
# root of that shape's `getSubOptions` here and in nixpkgs. The process plane pins that reading it runs
# no evaluation (`engine-option-names`, ci/tests-process.nix).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  names = t: builtins.attrNames (t.getSubOptions [ ]);
  shapes = types: submodule: {
    submodule = names (submodule { });
    freeformSubmodule = names (submodule {
      freeformType = types.lazyAttrsOf types.raw;
    });
  };
in
{
  flake.tests.engine-option-names = {
    # The published record is what this engine's `getSubOptions` serves over an empty module set, at
    # both shapes: a name the engine starts serving is published with no edit here. A declared
    # option is the control: it sits beside the engine's published names, never in them.
    test-the-published-names-are-the-served-roots = {
      expr = {
        served = gm.engineOptionNames == shapes gm.types gm.submodule;
        declared =
          names (gm.submodule { options.ctl = gm.mkOption { type = gm.types.int; }; })
          == builtins.sort builtins.lessThan (gm.engineOptionNames.submodule ++ [ "ctl" ]);
      };
      expected = {
        served = true;
        declared = true;
      };
    };

    test-the-published-names = {
      expr = gm.engineOptionNames;
      expected = {
        submodule = [ "_module" ];
        freeformSubmodule = [
          "_freeformOptions"
          "_module"
        ];
      };
    };

    # nixpkgs' `internalModule` and `submoduleWith` serve the same names at the same shapes.
    test-the-published-names-are-nixpkgs-roots = {
      expr = gm.engineOptionNames == shapes nixpkgsLib.types nixpkgsLib.types.submodule;
      expected = true;
    };
  };
}
