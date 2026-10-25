# A SUBMODULE MINTED OVER ITS STATED CONSTRUCTION (den-hoag-dwln8). `refusingSubmodule stated keys
# mods` mints over the constructor and argument components another library states, in place of the
# module list's seal: twins over equal arguments are one type, a differing argument or constructor two,
# and the constructor keeps the stating library's namespace. A rebuild keeps the statement and seals
# the rebuilt set beside it. `null` states nothing and mints over the module list's seal, as before.
{ genMerge, ... }:
let
  gm = genMerge;
  gt = gm.types;
  # `typeEq`, never `idOf`: a module list, and a rebuilt set, are sealed components
  mods = [ { options.a = gm.mkOption { default = 1; }; } ];
  stating = ctor: n: {
    inherit ctor;
    members = [ ];
    args = _: { inherit n; };
    sealed = [ ];
  };
  over = s: gm.refusingSubmodule s [ "config" ] mods;
  eq = gt.typeEq;
  rebuilt = t: t.substructure.rebuild mods;
in
{
  flake.tests.refusing-submodule-over = {
    test-twin-statements-mint-one-type = {
      expr = eq (over (stating "lib-a.inst" 1)) (over (stating "lib-a.inst" 1));
      expected = true;
    };
    test-a-stated-argument-decides = {
      expr = eq (over (stating "lib-a.inst" 1)) (over (stating "lib-a.inst" 2));
      expected = false;
    };
    # the mint is the stated one, spelled as stated: never `gen-merge.lib-a.inst`
    test-the-constructor-keeps-its-namespace = {
      expr =
        gt.idOf (over (stating "lib-a.inst" 1)) == (gt.mkIdentity "lib-a.inst" [ ] (_: {
          n = 1;
          specialArgs = { };
          refusedArgs = [ "config" ];
        }) [ ] "submodule").__mint.minted;
      expected = true;
    };
    test-a-statement-replaces-the-module-list-seal = {
      expr = eq (over (stating "lib-a.inst" 1)) (over null);
      expected = false;
    };
    # the control: stating nothing mints what the type minted before the operand existed (the digest
    # pinned at gen-merge b78f70b, read off `refusingSubmodule [ "config" "options" "prefix" ] { }` there)
    test-null-mints-the-module-list-seal = {
      expr = (gm.refusingSubmodule null [ "config" "options" "prefix" ] { }).__mint.minted;
      expected = "type:2930c401b7082acb4e330fae0da7df64ddf87b1ede3d3a6e698b4f0f893cf13a";
    };
    test-a-rebuild-keeps-the-statement = {
      expr = {
        twins = gt.typeEq (rebuilt (over (stating "lib-a.inst" 1))) (
          rebuilt (over (stating "lib-a.inst" 1))
        );
        apart = gt.typeEq (rebuilt (over (stating "lib-a.inst" 1))) (
          rebuilt (over (stating "lib-a.inst" 2))
        );
      };
      expected = {
        twins = true;
        apart = false;
      };
    };
  };
}
