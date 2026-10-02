# `showOption` is nixpkgs' `lib.options.showOption`, segment for segment: an identifier prints bare,
# anything else (a dot, a space, a leading digit, a keyword, `listOf`'s `[definition n-entry m]`)
# prints as a string literal with `$` escaped, and the placeholders `*` and `<...>` print bare.
{ genMerge, nixpkgsLib, ... }:
let
  segments = [
    "plain"
    "with-dash_and'prime"
    "dotted.key"
    "spaced key"
    "[definition 1-entry 1]"
    "*"
    "<name>"
    "0"
    "in"
    "inherit"
    ""
    "a$b"
    "q\"uote\\back"
  ];
  paths = map (s: [ s ]) segments ++ [
    [
      "s"
      "[definition 2-entry 1]"
      "a"
    ]
    [
      "a"
      "b.c"
    ]
    [
      "a.b"
      "c"
    ]
    [ ]
  ];
in
{
  flake.tests.show-option = {
    test-show-option-is-nixpkgs-show-option = {
      expr = map genMerge.showOption paths;
      expected = map nixpkgsLib.showOption paths;
    };
  };
}
