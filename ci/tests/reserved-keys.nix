# THE RESERVATION SCOPE — what still composes beside it. Its refusals are `ci/tests-error.nix`'s
# `reserved-keys` group (a refusal's message is only assertable there); this file holds the routes
# the scope must NOT refuse, and the first-occurrence rule it inherits from `_file`.
{ genMerge, ... }:
let
  gm = genMerge;
  t = gm.types;
  int0 = gm.mkOption {
    type = t.int;
    default = 0;
  };
  raw = gm.mkOption {
    type = t.raw;
    default = null;
  };
  # `kind` and `__mint` are declared so the exempt-shape control is not refused as undeclared config.
  decl.options = {
    k = int0;
    other = int0;
    kind = raw;
    __mint = raw;
  };
  res = {
    names.k = "RESERVED-k";
    exempt = [
      [ "kind" ]
      [
        "__mint"
        "minted"
      ]
    ];
  };
  scoped = child: {
    __reservedKeys = res;
    imports = [ child ];
  };
  k =
    mods:
    let
      r = builtins.tryEval (gm.evalModuleTree { modules = [ decl ] ++ mods; }).config.k;
    in
    if r.success then r.value else "REFUSED";
in
{
  flake.tests.reserved-keys = {
    # Five routes, one reading each. Outside any scope `k` writes. The marked module's OWN top level
    # is not in its scope (the library marking it checks that level itself). An explicit `config.k`
    # in a scoped import is the instance route. A scoped module declaring options only reads the
    # default. A scoped module carrying every `exempt` path is not checked.
    test-routes-that-still-compose = {
      expr = {
        outsideScope = k [ { k = 1; } ];
        markedModuleItself = k [
          {
            __reservedKeys = res;
            k = 1;
          }
        ];
        explicitConfig = k [ (scoped { config.k = 1; }) ];
        structuredOptionsOnly = k [ (scoped { options.unread = int0; }) ];
        exemptShape = k [
          (scoped {
            kind = "x";
            __mint.minted = "m";
            k = 1;
          })
        ];
      };
      expected = {
        outsideScope = 1;
        markedModuleItself = 1;
        explicitConfig = 1;
        structuredOptionsOnly = 0;
        exemptShape = 1;
      };
    };
    # THE SCOPE BELONGS TO A MODULE'S FIRST OCCURRENCE, as `_file` does. The path module is reached
    # first at the root, outside any scope, so the scoped re-import is deduplicated and not checked:
    # `k` writes. The control: the same path reached only through the scope refuses.
    test-scope-belongs-to-the-first-occurrence = {
      expr = {
        firstUnscoped = k [
          ./_fixtures/reserved-k.nix
          (scoped ./_fixtures/reserved-k.nix)
        ];
        onlyScoped = k [ (scoped ./_fixtures/reserved-k.nix) ];
      };
      expected = {
        firstUnscoped = 1;
        onlyScoped = "REFUSED";
      };
    };
    # The marker is gen-merge's own module key: stripped from config like `__pureModule`, and
    # published in both key lists a consumer's structured/shorthand guard reads.
    test-marker-is-a-module-key-in-both-lists = {
      expr = {
        structured = builtins.elem "__reservedKeys" gm.moduleSyntax.structured;
        shorthandMeta = builtins.elem "__reservedKeys" gm.moduleSyntax.shorthandMeta;
      };
      expected = {
        structured = true;
        shorthandMeta = true;
      };
    };
  };
}
