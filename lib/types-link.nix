# The right side of the `types` link: gen-merge's own strategies, less the five that are not types.
{ strategies }:
{
  library = "gen-merge";
  exports = builtins.removeAttrs strategies [
    "defineEmbedded"
    "partialAttrsOf"
    "mkSubmodule"
    "completeType"
    "verifyValue"
  ];
}
