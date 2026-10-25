# A SUBMODULE MINTED OVER ITS STATED CONSTRUCTION (den-hoag-dwln8). `refusingSubmoduleOver stated keys
# mods` mints over the constructor and argument components another library states, in place of the
# module list's seal: twins over equal arguments are one type, a differing argument or constructor two,
# and the constructor keeps the stating library's namespace. A rebuild keeps the statement and seals
# the rebuilt set beside it. `null` states nothing and is `refusingSubmodule`.
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
  over = s: gm.refusingSubmoduleOver s [ "config" ] mods;
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
      expr = eq (over (stating "lib-a.inst" 1)) (gm.refusingSubmodule [ "config" ] mods);
      expected = false;
    };
    # the control: stating nothing is the module list's seal
    test-null-is-refusing-submodule = {
      expr = eq (over null) (gm.refusingSubmodule [ "config" ] mods);
      expected = true;
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
