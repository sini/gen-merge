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
  gen = import libSrc {
    inherit prelude;
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
orig.extend (
  self: _: {
    # `evalRequest`'s bridge (`flake.nix`), plus nixpkgs' `lib` module argument. Every request field
    # other than `modules` is handed through, so one the door does not take is refused by name.
    evalModules =
      r:
      gen.evalModuleTree (
        removeAttrs r [ "modules" ]
        // {
          specialArgs = {
            lib = self;
          }
          // (r.specialArgs or { });
        }
      ) (r.modules or [ ]);
  }
)
