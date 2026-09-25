# THE PER-PROCESS CELLS — fixtures whose verdict is a PROCESS EXIT, one fixture per process.
#
# WHY THESE CANNOT BE SUITE CELLS. The subject cell observes `infinite recursion encountered`,
# which aborts the evaluator: `tryEval` does not catch it, so there is no message a suite cell
# could read and no boolean it could return. The assertion IS the exit status and the channel it
# died on, read by the runner in `tests-process.nix`, which evaluates each arm in its OWN process.
#
# Wiring: each dependency through its own `lib/` entry with explicit arguments, the way
# `../lib/default.nix`'s formals name them. Sources arrive as ARGUMENTS rather than through
# `fetchTree` because the runner evaluates inside the build sandbox, where fetching is impossible.
{
  arm,
  libSrc,
  genPreludeSrc,
  genIdentitySrc,
  genGraphSrc,
  genTypesSrc,
  genMemoSrc,
  genScopeSrc,
}:
let
  prelude = import "${genPreludeSrc}/lib";
  identity = import "${genIdentitySrc}/lib";
  graph = import "${genGraphSrc}/lib" { inherit prelude; };
  m = import libSrc {
    inherit prelude;
    types = import "${genTypesSrc}/lib" { inherit identity prelude; };
    memo = import "${genMemoSrc}/lib" { inherit graph prelude; };
    scope = import "${genScopeSrc}/lib" { inherit graph identity prelude; };
  };
  opt = m.mkOption {
    type = m.types.str;
    default = "d";
  };
  on = m.mkOption {
    type = m.types.str;
    default = "on";
  };
  eval = modules: m.evalModuleTree { inherit modules; };

  cells = {
    # THE OUTER FIXPOINT (den-hoag-xzchx, C3). A PLAIN attrset — no formals, no `imports`, no
    # `__functor` — whose option KEY SET under `a` reads the evaluation's own `options` through
    # the lexical binding `r`. That is ADR-0033's in-flight clause read literally, reached through
    # a channel the guard's by-name refusal cannot see: the module is never applied, so no
    # poisoned argument is ever demanded. What the guard still guarantees is that NO VALUE is
    # produced — forcing the declaration spine closes the cycle and the evaluator dies. An
    # admission that skips the guard for a module with no formals answers `{ a.b = "d"; y = "on"; }`
    # here instead: "takes no arguments" is not "closed term", since a thunk's free variables are
    # invisible to any predicate over the module's shape.
    outer-options-read =
      let
        r = eval [
          {
            options.y = on;
            options.a = if r.options ? y then { b = opt; } else { };
          }
        ];
      in
      r.config;

    # The SAME clause in the in-module form: the guard is live in this library and refuses it BY
    # NAME. The positive twin of the death above, on the same runner and the same wiring.
    in-module-options-read =
      (eval [
        (
          { options, ... }:
          {
            options.y = on;
            options.a = if options ? y then { b = opt; } else { };
          }
        )
      ]).config;

    # The same outer fixpoint read at a stratum-2 position ADR-0033 admits — an option DEFAULT —
    # ANSWERS: the wiring evaluates, and the death above is the cycle, not the fixture.
    outer-default-read =
      let
        r = eval [
          {
            options.y = on;
            options.x = m.mkOption {
              type = m.types.str;
              default = r.config.y;
            };
          }
        ];
      in
      r.config.x;
  };
in
cells.${arm}
