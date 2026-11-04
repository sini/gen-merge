# THE TWO SUBMODULE RECORD LITERALS ARE ONE TEXT BUT FOR `refusedArgs` (den-hoag-xrh86 Q1). `mkSubmodule`
# (lib/types.nix) writes its type record twice, branched on whether the type refuses a key, so a type refusing
# nothing carries no `refusedArgs` slot. The two must not drift: this reads the source and holds the record a
# refusing type gets equal to the plain one with that one line added. The branch's own delimiters are the only
# lines at their indentation, so the split reads exactly the two records.
_:
let
  src = builtins.readFile ../../lib/types.nix;
  open = "\n        (\n          if refusedKeys == [ ] then\n";
  sep = "\n          else\n";
  close = "\n        )\n";
  slot = "              refusedArgs = refusedKeys;\n";
  # the text between delimiter `d`s, each read literally
  pieces =
    s: d:
    builtins.filter builtins.isString (
      builtins.split (builtins.replaceStrings [ "(" ")" "[" "]" ] [ "[(]" "[)]" "[[]" "[]]" ] d) s
    );
  opened = pieces src open;
  branch = builtins.head (pieces (builtins.elemAt opened 1) close);
  arms = pieces branch sep;
  plain = builtins.elemAt arms 0;
  refusing = builtins.elemAt arms 1;
in
{
  flake.tests.refused-args-literals = {
    # the delimiters each occur once, so the split is the branch and nothing else
    test-the-branch-is-one-open-and-two-arms = {
      expr = {
        opens = builtins.length opened;
        arms = builtins.length arms;
        slots = builtins.length (pieces refusing slot);
      };
      expected = {
        opens = 2;
        arms = 2;
        slots = 2;
      };
    };
    test-the-refusing-record-is-the-plain-one-with-its-slot = {
      expr = builtins.replaceStrings [ slot ] [ "" ] refusing == plain;
      expected = true;
    };
  };
}
