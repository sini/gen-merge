# O5 — WHAT THE PROTOCOL BOUNDARY COSTS PER TYPE INSTANCE, and where that cost is now optional.
#
# The concern this answers is a measured one: stamping the full foreign protocol onto every type
# instance, through every structural constructor, is a per-instance cost that used to be unavoidable
# because a type had to be stamped to be usable by this engine AT ALL. The engine read the foreign
# fields, so there was no such thing as a type that skipped them.
#
# THE BOUNDARY MAKES THAT COST OPTIONAL, AND THIS IS WHERE THE CLAIM IS MEASURED RATHER THAN ASSERTED.
# Two arms build the SAME number of types over the SAME descriptor, declare an option for each, define
# each once, and force the whole resolved config:
#
#   gen       — `mkType`: the gen record alone. The engine folds it, verifies it and answers for it
#               without the foreign protocol ever being stamped.
#   exported  — `defineType`: the same record PLUS its expression in the foreign protocol, which is
#               what every published type is and what the pre-boundary constructor always produced.
#
# ★★ THE TWO ARMS MUST RETURN THE SAME VALUE, and the sweep checks that FIRST. "Fewer thunks" is not
# a result if the cheaper arm did less work — a gen arm that failed to merge anything would be the
# cheapest of all. Agreement on the resolved config is what makes the counter difference a reading of
# the protocol stamping and not of the work skipped.
#
# ★ THE ROW IS `nrThunks`, NAMED. Cpu rows are load-dependent theatre — they move with what else the
# machine is doing and are not comparable between runs — while thunk and allocation counts are
# deterministic for a fixed expression. Any claim from this bench states which row it read.
#
# ★ MARGINAL, NOT TOTAL. The claim is about a PER-INSTANCE cost, so the sweep runs each arm at two
# sizes and reads the difference: a fixed set-up overhead cancels, and what is left is what one more
# type costs. A total-only reading would be consistent with a constant overhead and no per-instance
# term at all.
#
# RUN (per arm; the sweep is `interface-cost.sh`):
#   nix-instantiate --eval --strict --json --argstr arm gen --argstr n 64 ./ci/bench/interface-cost.nix
{
  arm ? "exported",
  n ? "64",
}:
let
  fromLock =
    name:
    let
      lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
      node = lock.nodes.${name}.locked;
    in
    builtins.fetchTree {
      inherit (node)
        type
        owner
        repo
        rev
        narHash
        ;
    };
  prelude = import "${fromLock "gen-prelude"}/lib";
  # Through gen-types' own standalone entry, never its bare `./lib` — the root shim's rule: a
  # hand-named formal list is a SECOND SIGNATURE nothing compares against the first, and this
  # site carried the same untracked `identity` as either-totality.nix, latent because no arm
  # here forces the leaf checkers.
  genTypes = import "${fromLock "gen-types"}" { inherit prelude; };
  gm = import ../../lib {
    inherit prelude;
    types = genTypes;
  };
  core = import ../../lib/modules.nix {
    inherit prelude;
    priority = import ../../lib/priority.nix { inherit prelude; };
  };
  vocab = import ../../lib/types.nix { inherit prelude core; };

  count = builtins.fromJSON n;
  idx = builtins.genList (i: i) count;

  # ONE DESCRIPTOR, built two ways. Everything about the type is identical between the arms — the
  # name, the value predicate, the fold — so the only difference between them is whether the foreign
  # protocol was stamped on top.
  descriptor = i: {
    name = "probe${toString i}";
    verify = v: if builtins.isInt v then null else "expected an int";
    mergeDefs = _loc: defs: (builtins.head defs).value * 2;
  };

  # The engine does REAL WORK in both arms: one declared option per type, one definition each, the
  # whole resolved config forced by `--strict`. A bench that only CONSTRUCTED the types would measure
  # the constructor and say nothing about whether the engine can use what it built.
  run =
    mk:
    (gm.evalModuleTree {
      modules = [
        {
          _file = "decl.nix";
          options = builtins.listToAttrs (
            map (i: {
              name = "o${toString i}";
              value = gm.mkOption { type = mk i; };
            }) idx
          );
        }
        {
          _file = "def.nix";
          config = builtins.listToAttrs (
            map (i: {
              name = "o${toString i}";
              value = i;
            }) idx
          );
        }
      ];
    }).config;
in
if arm == "gen" then
  run (i: vocab.mkType (descriptor i))
else if arm == "exported" then
  run (i: vocab.defineType (descriptor i))
else
  throw "unknown arm"
