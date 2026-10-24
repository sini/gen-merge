# THE ONE SUBSTITUTED FILE in the copy of nixpkgs `lib/` that `modules-sh.nix` runs `lib/tests/modules.sh`
# over (den-hoag-06toi stage 1). Every `import ../..` in `lib/tests/modules` lands here, so every fixture
# reads nixpkgs' lib with its evalModules replaced by gen-merge's `evalModuleTree` under BOTH names it
# exposes: top-level `lib.evalModules`, and `lib.modules.evalModules`, the one nixpkgs' `submoduleWith`
# reads (`lib/types.nix`), so every submodule interior is gen's too. Types and every `mk*` stay nixpkgs'.
# Sources arrive as arguments, wired as `tests-process-cells.nix` does.
{
  orig,
  libSrc,
  genPreludeSrc,
  genIdentitySrc,
  genGraphSrc,
  genTypesSrc,
  genAlgebraSrc,
  genMemoSrc,
  genScopeSrc,
}:
let
  prelude = import "${genPreludeSrc}/lib";
  identity = import "${genIdentitySrc}/lib";
  algebra = import "${genAlgebraSrc}/lib";
  graph = import "${genGraphSrc}/lib" { inherit prelude; };
in
orig.extend (
  self: super:
  let
    # gen-merge instantiated with the `lib` its modules receive, as nixpkgs' `lib/modules.nix` is `{ lib }:`.
    gen = import libSrc {
      inherit prelude;
      lib = self;
      types = import "${genTypesSrc}/lib" { inherit algebra identity prelude; };
      memo = import "${genMemoSrc}/lib" { inherit graph prelude; };
      scope = import "${genScopeSrc}/lib" {
        inherit
          algebra
          graph
          identity
          prelude
          ;
      };
    };
  in
  rec {
    # `evalRequest`'s bridge (`flake.nix`). nixpkgs' `lib` is the engine's instantiation, so it reaches
    # every evaluation the engine makes, nested ones included. Every request field other than `modules`
    # is handed through, so one the door does not take is refused by name.
    evalModules = r: gen.evalModuleTree (removeAttrs r [ "modules" ]) (r.modules or [ ]);
    modules = super.modules // {
      inherit evalModules;
    };
  }
)
