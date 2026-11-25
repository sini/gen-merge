# A check-rewritten copy of gen's `submodule` as an `either` member is served under the copy's check, in
# gen's engine and in nixpkgs' `evalModules` over the same gen declarations (den-hoag-i7giw).
#
# The copy `S // { check }` over gen's submodule S, declared once as `either copy path`, raw and through
# both doors (`mkOptionType`, `types.mkOptionType`), alone and beside a `mkIf` default the definition
# outranks. gen's `either` chooses the member by its check and head judgement, so the copy is chosen and
# its value served wherever its check admits the value, and refused where it does not (ADR-0039 Not
# covered: an ad-hoc override is enforced as a foreign `addCheck` is, accepted values served and rejected
# values refused). In nixpkgs' engine the `either` and the member fold are still gen's, so the same holds
# there. nixpkgs' own twin refuses the copy inside its `either` (its v2 coherence guard), but serves its
# own `addCheck`, and that value is the oracle the served value must equal. Over gen's submodule, which
# publishes no `merge.v2`, `addCheck` is key for key the copy, so it is the control served in both engines.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins) deepSeq tryEval mapAttrs;

  ok = {
    t = "a";
  };
  bad = {
    t = "";
  };
  admits = x: x != bad;
  sub = gt.submodule {
    options.t = gm.mkOption {
      type = gt.nullOr gt.str;
      default = null;
    };
  };
  copy = sub // {
    check = x: sub.check x && admits x;
  };
  # the copy's three routes: the record itself and each gen door
  forms = {
    raw = copy;
    door1 = gm.mkOptionType copy;
    door2 = gt.mkOptionType copy;
  };
  # the two engines over gen declarations, each with its own `mkOption` and `mkIf`
  engines = {
    gen = {
      inherit (gm) mkOption mkIf;
      eval = mods: (gm.evalModuleTree { } mods).config.x;
    };
    npg = {
      inherit (nl) mkOption mkIf;
      eval = mods: (nl.evalModules { modules = mods; }).config.x;
    };
  };
  # declared once (A), or once beside a `mkIf` default the definition outranks (Ad)
  words = {
    A = _: { };
    Ad = E: { default = E.mkIf true ok; };
  };
  read =
    v:
    let
      o = tryEval (deepSeq v v);
    in
    if o.success then o.value else "REFUSED";
  cell =
    E: T: w: v:
    read (
      E.eval [
        { options.x = E.mkOption ({ type = gt.either T gt.path; } // w E); }
        { config.x = v; }
      ]
    );
  # engine × form × word, each reading what the value `v` becomes
  table = v: mapAttrs (_: E: mapAttrs (_: T: mapAttrs (_: w: cell E T w v) words) forms) engines;
  every = r: mapAttrs (_: _: mapAttrs (_: _: mapAttrs (_: _: r) words) forms) engines;

  # nixpkgs' own twin: its `addCheck` over its submodule, in its `either`, in its engine
  twin = read (
    (nl.evalModules {
      modules = [
        {
          options.x = nl.mkOption {
            type = np.either (np.addCheck (np.submodule {
              options.t = nl.mkOption {
                type = np.nullOr np.str;
                default = null;
              };
            }) admits) np.path;
          };
        }
        { config.x = ok; }
      ];
    }).config.x
  );
in
{
  flake.tests.either-submodule-copy-served = {
    # The value the copy's check admits is served, in both engines, by every form and word.
    test-a-submodule-copy-in-either-is-served-in-both-engines = {
      expr = table ok;
      expected = every ok;
    };
    # The value the copy's check rejects is refused, in both engines, by every form and word: the copy is
    # chosen under its own check, not its base's.
    test-a-rejected-value-of-a-submodule-copy-in-either-is-refused-in-both-engines = {
      expr = table bad;
      expected = every "REFUSED";
    };
    # The genuine `addCheck` over gen's submodule, the record the copy equals key for key, is served in both.
    test-add-check-over-gen-submodule-in-either-is-served-in-both-engines = {
      expr = mapAttrs (_: E: cell E (np.addCheck sub admits) words.A ok) engines;
      expected = mapAttrs (_: _: ok) engines;
    };
    # The value oracle: every served value equals what nixpkgs' twin serves for its own `addCheck`, and the
    # twin serves it (an oracle that refused would make the equality vacuous).
    test-the-served-value-equals-the-twin-add-check-value = {
      expr = {
        inherit twin;
        served = table ok;
      };
      expected = {
        twin = ok;
        served = every twin;
      };
    };
  };
}
