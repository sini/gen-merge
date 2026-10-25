# A WHOLE `_module.args` DEFINITION UNDER A PROPERTY SERVES NIXPKGS' VALUE (den-hoag-b44rx). nixpkgs' override pass
# runs over each module's whole definition, the engine's own `extendModules`, `moduleType` and position `name`
# among them at the default priority: `mkForce { q = 1; }` serves `{ q }` alone, and `mkDefault { q = 1; }` loses
# to the engine's own definitions. One cell per form × position × read nixpkgs serves (`test-<form>-<pos>-<read>`),
# gen's value against nixpkgs' (`./_fixtures/module-args-whole-set.nix`); the reads nixpkgs leaves undefined
# refuse by name (`../tests-error.nix`). `lib` is outside: the engine is built with no `lib` (den-hoag-6v35f).
# RED before the landing: every forced form's `keys` and child `nameVal`, and `dflt`/`odflt`'s `keys` (served the
# engine's arguments beside the set, or the set beside the engine's).
#
# Stated departure, both sides pinned:
#   iff  `_module.args = mkIf false { q = 1; }`: nixpkgs drops `q` from the keys; gen keeps the key, whose read
#        refuses as every definition disabled. A condition at the default stays per key so that deciding the keys
#        forces no condition (`conditional-*`), and this cell stays open on den-hoag-b44rx.

{ genMerge, nixpkgsLib, ... }:

let
  fx = import ./_fixtures/module-args-whole-set.nix {
    gm = genMerge;
    np = nixpkgsLib;
  };
  served =
    form: pos:
    builtins.filter (
      r: !(builtins.elem r (fx.undefinedAt form pos)) && !(form == "iff" && r == "keys")
    ) (fx.readsAt pos);
in
{
  flake.tests.module-args-whole-set =
    builtins.listToAttrs (
      builtins.concatMap (
        form:
        builtins.concatMap (
          pos:
          map (read: {
            name = "test-${form}-${pos}-${read}";
            value = {
              expr = fx.cell "gm" form pos read;
              expected = fx.cell "np" form pos read;
            };
          }) (served form pos)
        ) fx.positions
      ) fx.forms
    )
    // builtins.listToAttrs (
      map (pos: {
        name = "test-iff-${pos}-keys-pinned-b44rx";
        value = {
          expr = {
            gen = fx.cell "gm" "iff" pos "keys";
            nixpkgs = fx.cell "np" "iff" pos "keys";
          };
          expected =
            let
              engine = [
                "extendModules"
                "moduleType"
              ]
              ++ (if pos == "root" then [ ] else [ "name" ]);
            in
            {
              gen = engine ++ [ "q" ];
              nixpkgs = engine;
            };
        };
      }) fx.positions
    )
    // {
      # an argument-reading condition over a set at the default reaches its fixpoint
      test-conditional-reading-an-argument-flag = {
        expr = fx.conditional "gm" "reads" "flag";
        expected = true;
      };
      test-conditional-reading-an-argument-q = {
        expr = fx.conditional "gm" "reads" "q";
        expected = 1;
      };
      test-conditional-ctl-flag = {
        expr = fx.conditional "gm" "ctl" "flag";
        expected = fx.conditional "np" "ctl" "flag";
      };
      test-conditional-ctl-q = {
        expr = fx.conditional "gm" "ctl" "q";
        expected = fx.conditional "np" "ctl" "q";
      };
      # the re-declaring child's `name`, unforced
      test-declaring-child-name-unforced = {
        expr = fx.declaring false;
        expected = "s";
      };
    };
}
