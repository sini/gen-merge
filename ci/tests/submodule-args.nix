# The caller-supplied base module arg inlet — `(submodule mods).withArgs { … }`.
#
# ★★★ THESE CELLS TEST THE CHANNEL, NOT THE SYMPTOM, AND THAT IS THE LOAD-BEARING DECISION HERE.
# The user-facing symptom the inlet exists to remove is an INFINITE RECURSION — a module needing
# `lib` can only get it from `_module.args`, reading which forces the config fixpoint that module is
# part of. That abort is uncatchable: there is no `tryEval` door, so a cell asserting "this no longer
# diverges" CANNOT BE DRIVEN RED — seeding the defect hangs the suite rather than failing it, and a
# cell nobody can see fail is not an oracle. So the subject here is the CHANNEL: a module forcing its
# `lib` arg at its own WHNF evaluates, and the value it sees is the one the caller passed. Seeded —
# inlet removed, or the args not threaded at one of the rebuild sites — each cell below fails with a
# catchable, NAMED refusal, which is what makes them discriminating.
#
# ★★ AND THE REBUILD SITES ARE THE HALF THAT LOOKS OPTIONAL. Threading the args into the two
# `evalModuleTree` calls is not enough: three expressions rebuild a submodule type, and a rebuild
# that re-enters the args-less published constructor drops the caller's args SILENTLY. Two of them
# are on the ordinary path — a foreign engine calls `substSubModules` on every option whose type has
# a module set, including a single declaration, and gen's own containers delegate their rebuild to
# their element's — so `attrsOf ((submodule mods).withArgs …)` reaches it without crossing any
# boundary. Both are cells here; the refusal arms live in `../tests-error.nix`, where a throwing
# `expr` belongs.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  inherit (gm) evalModuleTree mkOption;

  # THE SUBJECT MODULE. It forces `lib` at its OWN WHNF — the shape the blocked user's config has —
  # so it cannot be satisfied out of `_module.args` and only a BASE module arg reaches it.
  forcesLib =
    { lib, ... }:
    {
      options.seen = mkOption {
        type = t.str;
        default = if lib ? version then "LIB-ARRIVED" else "NOT-A-LIB";
      };
    };

  # A DISTINGUISHABLE value, so the cells read "the arg IS what the caller passed" rather than the
  # weaker "something named lib was in scope" — which a hardcoded base arg would also satisfy.
  tagged = nixpkgsLib // {
    inletTag = "PASSED-BY-CALLER";
  };
  readsTag =
    { lib, ... }:
    {
      options.tag = mkOption {
        type = t.str;
        default = lib.inletTag or "ABSENT";
      };
    };

  # Mount a type at one option and merge one empty definition through it, which is the shortest path
  # that drives BOTH strata: the declaration fold reads `substructure.declares`, the value fold reads
  # `mergeDefs`.
  mountedAt =
    type:
    (evalModuleTree {
      modules = [
        { options.o = mkOption { inherit type; }; }
        { config.o = { }; }
      ];
    }).config.o;

  withLib = mods: (t.submodule mods).withArgs { lib = tagged; };
in
{
  flake.tests.submodule-args = {
    # ── the gating oracle ───────────────────────────────────────────────────────────────────────
    test-a-module-forcing-its-lib-arg-evaluates-under-withArgs = {
      expr = (mountedAt (withLib [ forcesLib ])).seen;
      expected = "LIB-ARRIVED";
    };
    test-the-arg-is-the-value-the-caller-passed = {
      expr = (mountedAt (withLib [ readsTag ])).tag;
      expected = "PASSED-BY-CALLER";
    };
    # LIVE CONTROL, same run: with no inlet used, the SAME module is refused — by name, and not by a
    # divergence. Without this the two cells above are consistent with `lib` arriving from somewhere
    # else entirely, which is the state this landing exists to distinguish from.
    test-the-same-module-without-withArgs-is-refused-control = {
      expr =
        (builtins.tryEval (builtins.deepSeq (mountedAt (t.submodule [ forcesLib ])).seen null)).success;
      expected = false;
    };

    # ── the rebuild sites ───────────────────────────────────────────────────────────────────────
    # `substSubModules` is what a foreign engine calls to re-root a submodule's modules under the
    # option it was declared at, on EVERY declaration and not only a redeclared one.
    test-substSubModules-preserves-the-caller-s-args = {
      expr =
        let
          type = withLib [ forcesLib ];
        in
        (mountedAt (type.substSubModules type.getSubModules)).seen;
      expected = "LIB-ARRIVED";
    };
    # The same site reached from INSIDE gen: a container delegates its rebuild to its element's, so
    # `attrsOf (… .withArgs …)` loses the args here without ever crossing the boundary.
    test-a-container-rebuild-preserves-the-element-s-args = {
      expr =
        let
          type = t.attrsOf (withLib [ forcesLib ]);
          rebuilt = type.substSubModules type.getSubModules;
        in
        (rebuilt.getSubOptions [ "k" ]).seen.default;
      expected = "LIB-ARRIVED";
    };
    # `recarry` is the third: the boundary rebuilds the type over its own payload to derive the
    # relation, and the round trip must not drop what the caller stated.
    test-recarry-preserves-the-args-across-the-boundary-round-trip = {
      expr =
        let
          type = withLib [ forcesLib ];
        in
        (mountedAt (type.functor.type type.functor.payload)).seen;
      expected = "LIB-ARRIVED";
    };

    # ── the relation ────────────────────────────────────────────────────────────────────────────
    # Two declarations UNION their module sets, so they union their args too.
    test-two-declarations-union-their-args = {
      expr =
        builtins.attrNames
          (((t.submodule [ { } ]).withArgs { p = 1; }).typeMergeRel (
            (t.submodule [ { } ]).withArgs { q = 2; }
          )).merged.specialArgs;
      expected = [
        "p"
        "q"
      ];
    };
    # Agreeing on a key is not a conflict — and this is the ordinary case, because both sides come
    # from one flake input and share a pointer.
    test-two-declarations-agreeing-on-an-arg-merge = {
      expr =
        (((t.submodule [ { } ]).withArgs { lib = tagged; }).typeMergeRel (
          (t.submodule [ { } ]).withArgs { lib = tagged; }
        ))
          ? merged;
      expected = true;
    };
    # The engine path: `lib` reaches each declaring module as a `specialArgs` formal and both hand it
    # to `withArgs`. The declaration stratum's `callD` binds the formal to `specialArgs`' own slot,
    # so the relation meets one cell; a per-application copy walks nixpkgs `lib` on Nix and
    # Determinate and throws on its removed aliases.
    test-lib-from-specialArgs-in-two-declarations-merges = {
      expr =
        let
          declares =
            file:
            { lib, ... }:
            {
              _file = file;
              options.o = mkOption { type = (t.submodule [ forcesLib ]).withArgs { inherit lib; }; };
            };
        in
        (evalModuleTree {
          specialArgs.lib = nixpkgsLib;
          modules = [
            (declares "/warp.nix")
            (declares "/weft.nix")
            { config.o = { }; }
          ];
        }).config.o.seen;
      expected = "LIB-ARRIVED";
    };
    # One function bound once and passed by both declarations is one value: it merges.
    test-one-function-passed-by-two-declarations-merges = {
      expr =
        let
          f = x: x;
        in
        (((t.submodule [ { } ]).withArgs { g = f; }).typeMergeRel (
          (t.submodule [ { } ]).withArgs { g = f; }
        ))
          ? merged;
      expected = true;
    };
    # A key only ONE declaration states is never compared, so its value is never forced: a throwing
    # value there merges on every evaluator rather than throwing on two of them.
    test-an-arg-only-one-declaration-states-is-not-forced = {
      expr =
        (
          ((t.submodule [ { } ]).withArgs {
            p = 1;
            q = throw "an arg only one declaration states was forced";
          }).typeMergeRel
            ((t.submodule [ { } ]).withArgs { p = 1; })
        )
          ? merged;
      expected = true;
    };
    # Disagreeing is, and it is REFUSED BY NAME rather than resolved by declaration order.
    test-two-declarations-disagreeing-on-an-arg-refuse-by-name = {
      expr =
        (((t.submodule [ { } ]).withArgs { lib = "LEFT"; }).typeMergeRel (
          (t.submodule [ { } ]).withArgs { lib = "RIGHT"; }
        )).refused;
      expected = "two `submodule' declarations stating different values for the base module argument `lib'";
    };
    # LIVE CONTROL for the function cell: two distinct closures are two values, refused by name.
    test-two-distinct-functions-refuse-by-name-control = {
      expr =
        (((t.submodule [ { } ]).withArgs { g = x: x; }).typeMergeRel (
          (t.submodule [ { } ]).withArgs { g = y: y; }
        )).refused;
      expected = "two `submodule' declarations stating different values for the base module argument `g'";
    };

    # ── nothing moved for a caller who does not use the inlet ───────────────────────────────────
    # LIVE CONTROL: the substrate's own `name` still arrives, and the published constructor's
    # signature is unchanged.
    test-a-submodule-with-no-args-still-binds-name-control = {
      expr =
        (evalModuleTree {
          modules = [
            {
              options.sub = mkOption {
                type = t.submodule ({ name, ... }: { options.n = mkOption { default = name; }; });
                default = { };
              };
            }
            { config.sub = { }; }
          ];
        }).config.sub.n;
      expected = "sub";
    };
  };
}
