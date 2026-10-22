# The descriptions of the engine's own `_module` options (`lib/modules.nix` `moduleOwn`): nixpkgs'
# `internalModule` text, which the docs walker renders, so documentation equals nixpkgs' (ADR-0039).
# The file holds strings only (`ci/tests/purity.nix` exempts it by name and asserts that).
#
# nixpkgs, verbatim: ported from nixpkgs `lib/modules.nix` (02c087f):
#
#   Copyright (c) 2003-2026 Eelco Dolstra and the Nixpkgs/NixOS contributors
#
#   Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
#   associated documentation files (the "Software"), to deal in the Software without restriction,
#   including without limitation the rights to use, copy, modify, merge, publish, distribute,
#   sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
#   furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in all copies or
#   substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
#   NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
#   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES
#   OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
#   CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
{
  args = ''
    Additional arguments passed to each module in addition to ones
    like `lib`, `config`,
    and `pkgs`, `modulesPath`.

    This option is also available to all submodules. Submodules do not
    inherit args from their parent module, nor do they provide args to
    their parent module or sibling submodules. The sole exception to
    this is the argument `name` which is provided by
    parent modules to a submodule and contains the attribute name
    the submodule is bound to, or a unique generated name if it is
    not bound to an attribute.

    Some arguments are already passed by default, of which the
    following *cannot* be changed with this option:
    - {var}`lib`: The nixpkgs library.
    - {var}`config`: The results of all options after merging the values from all modules together.
    - {var}`options`: The options declared in all modules.
    - {var}`specialArgs`: The `specialArgs` argument passed to `evalModules`.
    - All attributes of {var}`specialArgs`

      Whereas option values can generally depend on other option values
      thanks to laziness, this does not apply to `imports`, which
      must be computed statically before anything else.

      For this reason, callers of the module system can provide `specialArgs`
      which are available during import resolution.

      For NixOS, `specialArgs` includes
      {var}`modulesPath`, which allows you to import
      extra modules from the nixpkgs package tree without having to
      somehow make the module aware of the location of the
      `nixpkgs` or NixOS directories.
      ```
      { modulesPath, ... }: {
        imports = [
          (modulesPath + "/profiles/minimal.nix")
        ];
      }
      ```

    For NixOS, the default value for this option includes at least this argument:
    - {var}`pkgs`: The nixpkgs package set according to
      the {option}`nixpkgs.pkgs` option.
  '';
  freeformType = ''
    If set, merge all definitions that don't have an associated option
    together using this type. The result then gets combined with the
    values of all declared options to produce the final `
    config` value.

    If this is `null`, definitions without an option
    will throw an error unless {option}`_module.check` is
    turned off.
  '';
  specialArgs = ''
    Externally provided module arguments that can't be modified from
    within a configuration, but can be used in module imports.
  '';
}
