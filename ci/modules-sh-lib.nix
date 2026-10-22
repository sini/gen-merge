# THE ONE SUBSTITUTED FILE in the copy of nixpkgs `lib/` that `modules-sh.nix` runs `lib/tests/modules.sh`
# over (den-hoag-06toi stage 1). Every `import ../..` in `lib/tests/modules` lands here, so every fixture
# reads nixpkgs' lib with ONE binding replaced: top-level `lib.evalModules` is gen-merge's
# `evalModuleTree`. Types, every `mk*` and `lib.modules` stay nixpkgs', so a nixpkgs `submoduleWith`
# still evaluates its own interior. Sources arrive as arguments, wired as `tests-process-cells.nix` does.
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
  self: _:
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
  {
    # `evalRequest`'s bridge (`flake.nix`). nixpkgs' `lib` is the engine's instantiation, so it reaches
    # every evaluation the engine makes, nested ones included. Every request field other than `modules`
    # is handed through, so one the door does not take is refused by name.
    evalModules = r: gen.evalModuleTree (removeAttrs r [ "modules" ]) (r.modules or [ ]);
  }
)
