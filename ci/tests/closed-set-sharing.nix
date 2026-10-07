# THE CLOSED-SET SHARING (den-hoag-i1ovm) — on a closed module set the declaration guard hands the
# value stratum its collection instead of the body computing it a second time (`lib/modules.nix`,
# THE DECLARATION GUARD). Sharing is common-subexpression elimination, so it must change no answer.
# Each cell evaluates one set twice: as written (closed, shared), and with every module wrapped as
# `_: m` (open, so the guard returns `null` and the body computes its own). The two arms must agree
# on success, on config, on provenance, on undeclared and on each option's `loc` and `declarations`
# (an option record here is the declaration; it answers no value). Eliding the guard on closed sets
# instead of sharing it admits the refusal cells silently, and reds them.
{ genMerge, ... }:
let
  gm = genMerge;
  t = gm.types;
  int0 = gm.mkOption {
    type = t.int;
    default = 0;
  };
  decl = {
    _file = "/real/D.nix";
    options.a = int0;
    options.foo = int0;
  };
  sub = gm.mkOption {
    type = t.attrsOf (
      t.submodule {
        options.x = int0;
        options.y = int0;
      }
    );
    default = { };
  };

  outcome =
    ms:
    let
      r = gm.evalModuleTree { } ms;
      v = {
        inherit (r) config provenance undeclared;
        options = builtins.mapAttrs (_: o: {
          inherit (o) loc declarations;
        }) r.options;
      };
      e = builtins.tryEval (builtins.deepSeq v v);
    in
    if e.success then e.value else "REFUSED";
  parity = ms: {
    closed = outcome ms;
    open = outcome (map (m: _: m) ms);
  };
  same =
    ms:
    let
      p = parity ms;
    in
    p.closed != "REFUSED" && p.closed == p.open;
in
{
  flake.tests.closed-set-sharing = {
    # Admitted sets: the shared collection publishes what the unshared one does, and it is a value
    # (two equal refusals would agree vacuously).
    test-admitted-sets-agree-shared-and-unshared = {
      expr = {
        plain = same [
          decl
          { config.a = 7; }
        ];
        nested = same [
          decl
          { options.s = sub; }
          {
            config.s.m.x = 3;
            config.s.n.y = 4;
          }
        ];
        dupKey = same [
          decl
          {
            key = "k";
            config.a = 1;
          }
          {
            key = "k";
            config.a = 2;
          }
        ];
      };
      expected = {
        plain = true;
        nested = true;
        dupKey = true;
      };
    };
    # Refused sets: the declaration-plane refusals the guard alone forces refuse on both arms, so
    # sharing the guard's collection keeps them eager.
    test-declaration-refusals-refuse-shared-and-unshared = {
      expr = builtins.mapAttrs (_: parity) {
        typo = [
          decl
          {
            _file = "/real/T.nix";
            options.b = int0;
            option.c = int0;
          }
        ];
        surplus = [
          decl
          {
            _file = "/real/S.nix";
            config.a = 1;
            bogus = 2;
          }
        ];
        disabled = [
          decl
          {
            _file = "/real/X.nix";
            disabledModules = [ ];
            config.a = 1;
          }
        ];
        keylessKeyEq = [
          decl
          {
            _file = "/real/K.nix";
            __keyEq = _: _: true;
            config.a = 1;
          }
        ];
        leafGroup = [
          decl
          { options.p = int0; }
          { options.p.q = int0; }
        ];
      };
      expected =
        let
          refused = {
            closed = "REFUSED";
            open = "REFUSED";
          };
        in
        {
          typo = refused;
          surplus = refused;
          disabled = refused;
          keylessKeyEq = refused;
          leafGroup = refused;
        };
    };
  };
}
