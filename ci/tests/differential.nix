# THE DIFFERENTIAL — MODULE SYSTEM COMPATIBILITY, held by the extracted apparatus.
#
# ★★★ WHAT THIS SUITE CLOSES. A promise of this ecosystem stood for eight days with no gate behind
# it. Its predecessor (`rehost-byte-parity`, retired 2026-08-13 by owner ruling) was recorded as
# GATE SUSPENDED / PROMISE STANDS, and the successor named in that record — the parity apparatus
# extracted, generalized, and given a formalized API contract — is `gen-differential`. ADR-0025
# item 2 names this repository as its first consumer: *the engine the apparatus was built to hold
# accountable finally being held by it*. This file is that wiring.
#
# ★★ THE PROMISE, NAMED, BECAUSE AN UNNAMED PROMISE IS THE DEFECT THE PREDECESSOR DIED OF.
# **Module system compatibility** — gen's module system agrees with nixpkgs' on the shared grammar,
# which is what anyone migrating FROM nixpkgs modules relies on. It is a claim about an EXTERNAL
# interface, which is why it needs an oracle with a reference at all: internal correctness is
# provable against this repository's own suites, compatibility is not.
#
# ★★★ WHY EVERY CELL CARRIES A `claim` FIELD, STATED AS THE FAILURE IT PREVENTS. The retired
# instrument asserted a CONJUNCTION nobody had written down — (P1) the pure engine computes what
# nixpkgs computes, AND (P2) the published grammar is semantically unchanged since a freeze — and
# its reference side was frozen pre-re-host, so it could never follow a ruled grammar change. It
# therefore reddened on every deliberate improvement and could not say WHICH CONJUNCT a red
# belonged to. The contract's required `claim` field is the structural fix: a red here names the
# claim it belongs to, and `oracles.explain` prints that name. `test-teeth-*` below measures that it
# does, rather than asserting it in a comment.
#
# ★ AND P2 IS NOT SILENTLY RE-ASSERTED HERE. This subject's reference is nixpkgs' LIVE `lib`,
# resolved through the same `lib` the equivalence oracle uses — not a frozen witness — so there is
# no second conjunct to confound the first. What a red here means is exactly P1.
#
# ── WHAT THIS DOES NOT ASSERT, NAMED SO THE GAP IS NOT READ AS COVERED ──────────────────────────
# The retired instrument's unique contribution over `rehost-den-parity` was the ASPECT-GRAMMAR
# layer, and that grammar does not live in this repository. This suite closes the SHARED-GRAMMAR
# CORE of the promise — the module system itself, which is the layer everything above it inherits —
# and it does not close the aspect layer. That belongs to an instantiation which has one.
#
# ── HOW THIS RELATES TO `oracle.nix`, WHICH IT DOES NOT REPLACE ─────────────────────────────────
# `oracle.nix` is the design spec's §3 C1 acceptance gate: `gmConfigOf fx == npConfigOf fx`, a
# boolean per fixture. It stays, and this suite reads THE SAME CORPUS (`_fixtures/corpus.nix`, also
# the portable-subset lint's accept-set) rather than growing a second one — a differential whose
# corpus drifts from the oracle's is two claims wearing one name.
#
# What the machinery adds over the `==` is not coverage but READABILITY AND STRUCTURE: a red names
# its claim, its arms, its comparison kind, its assertion class (equivalence / identity / refusal)
# and the first coordinate at which the two parted company, instead of `false`. It adds the
# SEAM-ROUTED IDENTITY CONTROL, which the `==` has no analogue of. It adds the anti-vacuity keys as
# structure — `both-evaluated` distinguishes "the two agree" from "neither produced anything", which
# a bare `==` cannot. And it adds the DIVERGENCE REGISTER, so a deliberate grammar change becomes a
# named divergence with its ruling attached rather than a red nobody can attribute.
{
  lib,
  genMerge,
  genMergeCompat,
  differential,
  ...
}:
let
  d = differential;

  # The shared parity corpus — ONE source of truth with `oracle.nix` and `lint.nix`. Each fixture is
  # already `P -> [ modules ]`, which is exactly the contract's own shape: a fixture's modules are a
  # FUNCTION OF THE ARM'S VOCABULARY, so both arms run the same source through their own
  # `mkOption`/`types`/`mkMerge` rather than one arm's source being read by two engines.
  corpus = import ./_fixtures/corpus.nix;

  # ── THE BODIES ────────────────────────────────────────────────────────────────────────────────
  #
  # A module-system BODY is the complete surface a migrating consumer swaps: the constructor
  # vocabulary their modules are written against, plus the evaluation entry point. It is the
  # operand the seam installs, and naming it separately from the ARM is what lets the identity
  # control exist at all — the reference's body has to be installable somewhere.
  packOf = s: {
    inherit (s)
      mkOption
      mkMerge
      mkIf
      mkForce
      mkDefault
      mkOverride
      types
      ;
  };

  nixpkgsBody = {
    name = "nixpkgs";
    vocab = packOf lib;
    evalModules = lib.evalModules;
  };

  genMergeBody = {
    name = "gen-merge";
    vocab = packOf genMerge;
    evalModules = genMerge.evalModuleTree;
  };

  # ── THE SEAM ──────────────────────────────────────────────────────────────────────────────────
  #
  # ★★ THE SUBSTITUTION POINT IS THE ONE A CONSUMER ACTUALLY USES, WHICH IS WHY IT IS THIS ONE.
  # gen-merge's supported migration is a `lib`-shaped surface swap: `lib.evalModules` becomes
  # `evalModuleTree` and `lib.types` becomes the unified `types` namespace, which
  # `lib/default.nix` describes in exactly those terms ("the `lib.types` drop-in the re-host points
  # at"). `install` is that swap, made a function.
  #
  # ★★★ THE IDENTITY ARM IS WHY THE SEAM IS A CONTRACT FIELD AND NOT A CONVENIENCE. A control
  # specified as reference-against-reference is `x == x`: trivially true, and — the part that
  # matters — IMPOSSIBLE TO SEED WITH A FAULT. The control here is the REFERENCE'S OWN BODY
  # INSTALLED AT THE CANDIDATE'S SEAM. Semantically it is nixpkgs; structurally it travels the
  # candidate's construction path, so any perturbation of that path moves it while leaving the bare
  # reference standing. `test-control-identity-*` below seeds exactly that and measures the red.
  #
  # The arm's name carries `@seam` so a red says which route the evaluator took — the bare
  # reference and the identity arm are the same evaluator reached two ways, and a reader of a
  # failure needs the two distinguishable without already knowing the design.
  installAt =
    body:
    d.mkArm {
      name = "${body.name}@seam";
      inherit (body) vocab;
      eval =
        req:
        body.evalModules {
          inherit (req) modules specialArgs;
        };
    };

  seam = d.mkSeam {
    name = "lib-surface-swap";
    install = installAt;
    referenceBody = nixpkgsBody;
  };

  # ── THE SECOND SEAM — a different substitution point, not a second candidate at the first ──────
  #
  # ★★ THE TWO SEAMS ARE DIFFERENT MIGRATION POSTURES, AND THAT IS WHY THERE ARE TWO. The first
  # swaps the whole `lib`-shaped surface, so a consumer's modules are re-read through gen's own
  # vocabulary. This one swaps ONLY THE EVALUATION ENTRY POINT and leaves the modules written
  # against nixpkgs' own `mkOption` and `lib.types` exactly as they are — the escape hatch
  # `compat-nixpkgs-types.nix` pins, where nixpkgs types plug INTO the engine because they carry a
  # `.merge` the `(loc, defs)` dispatch calls. It is the sharpest form of the promise: a consumer
  # changes one call and nothing else.
  #
  # ★ THE VOCABULARY HERE IS DELIBERATELY NIXPKGS', AND REACHING FOR `genMergeCompat.types` INSTEAD
  # IS A MEASURED REFUSAL RATHER THAN A STYLE CHOICE. That namespace merges nixpkgs leaf checkers
  # with gen-merge's structural strategies through the linkset, and the two overlap at nine
  # undeclared names (`submodule`, `nullOr`, `either`, `oneOf`, `raw`, `anything`, `lazyAttrsOf`,
  # `deferredModule`, `mkOptionType`), so forcing it refuses by design — Cardelli 1997's
  # disjointness precondition, enforced. The compat mode's vocabulary IS nixpkgs' `lib.types`, and
  # this seam says so structurally rather than in a comment somewhere else.
  installEvaluator =
    body:
    d.mkArm {
      name = "${body.name}@eval-seam";
      vocab = packOf lib;
      eval =
        req:
        body.evalModules {
          inherit (req) modules specialArgs;
        };
    };

  evaluatorSeam = d.mkSeam {
    name = "evaluator-swap";
    install = installEvaluator;
    referenceBody = {
      name = "nixpkgs";
      evalModules = lib.evalModules;
    };
  };

  # THE BARE REFERENCE — constructed DIRECTLY rather than through `installAt`, and that is the whole
  # content of the control. If the reference were built by the same function the identity arm is
  # built by, the two would be one expression and the comparison would be a tautology.
  referenceArm = d.mkArm {
    inherit (nixpkgsBody) name vocab;
    eval =
      req:
      lib.evalModules {
        inherit (req) modules specialArgs;
      };
  };

  # ── THE OBSERVABLES ───────────────────────────────────────────────────────────────────────────
  #
  # ★ THE `_module` FILTER IS A DECLARED NARROWING, NOT A TIDY-UP, and it is stated where it is
  # applied. `_module` is nixpkgs' own synthetic pseudo-option; this engine does not publish one,
  # and that difference is not a compatibility failure — no claim here covers it. So the value
  # observable drops it, exactly as `oracle.nix`'s `stripModule` does, which is also what keeps the
  # two instruments reading the SAME surface rather than two that happen to agree.
  #
  # ★★ AND AT THE PINNED nixpkgs IT IS CURRENTLY A NO-OP, WHICH IS A MEASUREMENT AND NOT A GUESS:
  # `lib.evalModules` publishes `_module` as a TOP-LEVEL result key, and `config` carries only the
  # declared options (measured at the locked nixpkgs — result keys `_module`, `_type`, `class`,
  # `config`, `extendModules`, `graph`, `options`, `type`). The strip stays because the placement is
  # nixpkgs' to change and a differential should not redden on a reference's internal reshuffle.
  # THE COST, SAID OUT LOUD: a candidate that wrongly emitted a `_module` key inside its config is
  # invisible at this observable.
  configSansModule = result: builtins.removeAttrs result.config [ "_module" ];

  # ★★ THE OBSERVABLE AXIS IS A SET PER FIXTURE, AND HERE IT EARNS ITS KEEP RATHER THAN
  # DEMONSTRATING A FEATURE. `optionNames` sees the DECLARED SURFACE, which a value comparison
  # cannot: an engine that computes every value correctly while declaring a different option set
  # agrees at `config` and diverges here. `oracle.nix`'s `==` has no second surface at all, so this
  # is the first thing the machinery buys that the boolean could not express.
  valueOnly = {
    config = configSansModule;
  };
  valueAndShape = {
    config = configSansModule;
    optionSurface = d.observables.optionNames;
  };

  # ── THE FIXTURES ──────────────────────────────────────────────────────────────────────────────
  #
  # The whole corpus at the value surface, plus the declared-surface observable on the three
  # fixtures whose option TREE is the interesting part: nested option paths that must merge by
  # recursion rather than by clobbering, a keyed submodule collection, and the integrated
  # aspect-shaped surface.
  shapeAlso = [
    "nested-options"
    "submodule-name-selfref"
    "aspect-shaped"
  ];

  valueFixtures = builtins.mapAttrs (
    name: fx:
    d.mkFixture {
      comparison = "value";
      observables = if builtins.elem name shapeAlso then valueAndShape else valueOnly;
      modules = fx;
    }
  ) corpus;

  # ── REFUSAL AS A COMPATIBILITY PROPERTY ───────────────────────────────────────────────────────
  #
  # ★ A REFUSAL IS AN ANSWER, AND AGREEING ABOUT IT IS PART OF THE PROMISE. An engine that silently
  # accepts what nixpkgs rejects is not a more permissive implementation of the same grammar; it is
  # a different language, and a consumer migrating a module that nixpkgs refuses would get no
  # diagnostic at all. These are `oracle.nix`'s AC#3 and AC#4 properties, re-asserted here under the
  # `throws` comparison kind — which records its assertion class as `refusal`, so a reader cannot
  # mistake mutual refusal for equivalence.
  #
  # ★★ AND THE KIND'S DOMAIN IS THE `tryEval`-CATCHABLE SUBCLASS, which is the honest scope: it
  # asserts that both arms DECLINE, never that they declined for the same reason.
  refusalFixtures = {
    nested-leaf-vs-group-collision = d.mkFixture {
      comparison = "throws";
      observables = valueOnly;
      modules = P: [
        { options.a.b = P.mkOption { type = P.types.int; }; }
        { options.a.b.c = P.mkOption { type = P.types.int; }; }
        { config.a.b.c = 1; }
      ];
    };
    nested-undeclared-key = d.mkFixture {
      comparison = "throws";
      observables = valueOnly;
      modules = P: [
        {
          options.a.b.c = P.mkOption {
            type = P.types.int;
            default = 1;
          };
        }
        { config.a.b.z = 9; }
      ];
    };
  };

  fixtures = valueFixtures // refusalFixtures;

  # ── THE SUBJECTS ──────────────────────────────────────────────────────────────────────────────
  #
  # ★★ TWO SUBJECTS AT TWO SEAMS, AND THE SEAM COUNT IS ASSERTED RATHER THAN ASSUMED.
  # `oracles.distinctSubjects` refuses a run whose subjects share a seam, because a harness
  # parameterized against exactly one substitution point is indistinguishable from one hard-coded to
  # it — the very defect this library was commissioned to remove, reproduced one level up in the
  # consumer. The two seams above are genuinely different substitution points, not one seam spelled
  # twice, and `test-two-distinct-seams` measures that at the oracle rather than trusting the names.
  claimA = "module system compatibility at the surface seam: modules re-read through gen's own vocabulary agree with nixpkgs' evalModules on the shared grammar";
  claimB = "module system compatibility at the evaluator seam: modules authored against nixpkgs' own vocabulary agree when only the evaluation entry point is replaced by gen-merge's engine";

  subjectA = d.mkSubject {
    reference = referenceArm;
    candidate = installAt genMergeBody;
    inherit seam;
    claim = claimA;
  };

  subjectB = d.mkSubject {
    reference = referenceArm;
    candidate = installEvaluator {
      name = "gen-merge+nixpkgs-leaves";
      evalModules = genMergeCompat.evalModuleTree;
    };
    seam = evaluatorSeam;
    claim = claimB;
  };

  # ── THE RUNS ──────────────────────────────────────────────────────────────────────────────────
  #
  # THE REGISTER IS EMPTY, AND THAT IS AN ASSERTION RATHER THAN AN OMISSION. An entry states that a
  # named divergence OCCURS; an empty register therefore says no divergence is authorized anywhere
  # in this corpus, and any divergence at all is a red. The register's own machinery is measured
  # below (`test-register-*`) against a seeded divergence, so the field is exercised rather than
  # merely defaulted.
  runA = d.mkRun {
    subject = subjectA;
    inherit fixtures;
  };
  runB = d.mkRun {
    subject = subjectB;
    inherit fixtures;
  };

  # ── HOW A CELL REPORTS ────────────────────────────────────────────────────────────────────────
  #
  # ★ A RED PRINTS ITS OWN ATTRIBUTION. `expected` is `true`; a failing cell yields the claim's full
  # explanation instead, so the nix-unit diff IS the diagnosis — which claim, which arms, which
  # comparison kind and assertion class, which observable, and the first coordinate at which the two
  # parted company. A cell that yielded a bare `false` would put the reader back where the retired
  # instrument left them.
  verdict = c: if c.green then true else d.oracles.explain c;

  # Flatten `run.cells.<fixture>.<observable>.<role>` into nix-unit cells.
  cellsOf =
    prefix: run:
    builtins.listToAttrs (
      builtins.concatMap (
        fixtureName:
        builtins.concatMap (
          observableName:
          map
            (role: {
              name = "test-${prefix}-${fixtureName}-${observableName}-${role}";
              value = {
                expr = verdict run.cells.${fixtureName}.${observableName}.${role};
                expected = true;
              };
            })
            [
              "identity"
              "candidate"
            ]
        ) (builtins.attrNames run.cells.${fixtureName})
      ) (builtins.attrNames run.cells)
    );

  # ── WHICH ENGINE ACTUALLY RAN ─────────────────────────────────────────────────────────────────
  #
  # ★★★ AN ARM'S NAME IS A LABEL, AND A COMPARISON THAT TRUSTS ITS LABELS CAN BE COMPARING ONE
  # ENGINE WITH ITSELF AND READING GREEN. That is the tautology this repository's own ci flake
  # already warns about at a different seam ("two separate `gen-prelude.lib` expressions would let
  # the cell pass while comparing two different builds"), and a differential is exactly where it
  # would be invisible: if `installEvaluator` had closed over the wrong body, every cell would agree
  # perfectly and every anti-vacuity key would still pass.
  #
  # So the engine is measured rather than named, and BY A POSITIVE MARKER ON EACH SIDE rather than
  # by one marker and its absence — an absence is also what a broken reading returns. gen-merge's
  # `evalModuleTree` publishes a `provenance` attribute nixpkgs has no analogue of; nixpkgs'
  # `evalModules` publishes `extendModules`, which this engine does not. Each arm must carry its own
  # engine's marker AND lack the other's.
  engineFingerprint =
    arm:
    let
      r = d.compare.run arm toothFixture;
    in
    {
      genProvenance = r ? provenance;
      nixpkgsExtendModules = r ? extendModules;
    };
  nixpkgsFingerprint = {
    genProvenance = false;
    nixpkgsExtendModules = true;
  };
  genFingerprint = {
    genProvenance = true;
    nixpkgsExtendModules = false;
  };

  # ── THE TEETH ─────────────────────────────────────────────────────────────────────────────────
  #
  # ★★★ A HARNESS THAT CANNOT BE SHOWN TO FAIL IS INDISTINGUISHABLE FROM `true`, and this is where
  # that is measured rather than argued. Perturbing the fixture must move the compared observable;
  # if it does not, every green above is compatible with the comparison reading a constant.
  toothFixture = valueFixtures.typed-and-priority;
  candidateA = installAt genMergeBody;

  # `b` is the plain (unforced) definition in that fixture, so a forced override wins outright.
  perturbB = fx: fx // { modules = v: (fx.modules v) ++ [ { b = v.mkForce 99; } ]; };
  # THE POSITIVE CONTROL'S TWIN: a perturbation that changes NOTHING must leave the observable
  # standing. Without it, `moved = true` is compatible with a reading that always moves.
  perturbNothing = fx: fx // { modules = v: (fx.modules v) ++ [ { } ]; };

  toothMoved = d.oracles.mutationTeeth {
    arm = candidateA;
    fixture = toothFixture;
    observableName = "config";
    perturb = perturbB;
  };
  toothStill = d.oracles.mutationTeeth {
    arm = candidateA;
    fixture = toothFixture;
    observableName = "config";
    perturb = perturbNothing;
  };

  # ── THE COVERAGE FLOOR ────────────────────────────────────────────────────────────────────────
  #
  # The retired instrument's gate keys are the coverage the successor INHERITS rather than
  # renegotiates. Three of its four are met here and asserted individually; the fourth is
  # `den-realism`, a property of a real domain tree, which this repository does not have and which
  # the library's own `floorKeys` correctly omits. Naming the shortfall is the difference between a
  # deferral and a silent gap.
  floorA = d.oracles.floor {
    run = runA;
    teeth = toothMoved.moved;
  };
  floorB = d.oracles.floor {
    run = runB;
    teeth = toothMoved.moved;
  };

  # ── THE SEEDED DIVERGENCE — the REQUIRED mutation-teeth contract feature ───────────────────────
  #
  # ★★ A DELIBERATE DIVERGENCE, CARRIED AS A PERMANENT CELL RATHER THAN DEMONSTRATED ONCE. The arm
  # below is the real candidate with one config value overwritten after evaluation, so the
  # comparison has a known divergence at a known coordinate. The cells assert that the run goes RED,
  # that the red carries the CLAIM it belongs to, and that the first divergence is located exactly
  # where the fault was seeded. A demonstration run by hand at wiring time proves nothing next
  # month; this cell fails the day the comparison stops detecting differences.
  seededCandidate = d.mkArm {
    name = "gen-merge@seeded";
    inherit (genMergeBody) vocab;
    eval =
      req:
      let
        r = genMerge.evalModuleTree { inherit (req) modules specialArgs; };
      in
      r
      // {
        config = r.config // {
          a = "SEEDED";
        };
      };
  };

  seededSubject = d.mkSubject {
    reference = referenceArm;
    candidate = seededCandidate;
    inherit seam;
    claim = claimA;
  };

  seededRun = d.mkRun {
    subject = seededSubject;
    fixtures.typed-and-priority = toothFixture;
  };
  seededClaim = seededRun.cells.typed-and-priority.config.candidate;

  # ── THE REGISTER, IN BOTH DIRECTIONS ──────────────────────────────────────────────────────────
  #
  # ★★ AN ENTRY IS AN ASSERTION, NOT A MUTE, AND BOTH HALVES ARE MEASURED HERE. Registering the
  # seeded divergence turns the cell green and lists it as `registered` — that is the P1/P2
  # separability the retired instrument lacked, made concrete: a ruled change is expressible as a
  # named divergence carrying its ruling instead of a red nobody can attribute. Registering a
  # divergence that does NOT occur leaves the entry `missing` and the cell RED — which is what stops
  # the register decaying into a suppression list.
  seededEntry = d.register.mkEntry {
    path = [ "a" ];
    values = {
      reference = "forced";
      candidate = "SEEDED";
    };
    ruling = "this suite's own seeded divergence (`test-teeth-*`), registered here to measure that the register admits a named divergence rather than suppressing a class";
  };
  staleEntry = d.register.mkEntry {
    path = [ "b" ];
    values = {
      reference = 7;
      candidate = 999;
    };
    ruling = "a divergence that does not occur, registered to measure that an unsatisfied entry reddens rather than passing quietly";
  };

  registeredRun = d.mkRun {
    subject = seededSubject;
    fixtures.typed-and-priority = toothFixture;
    register = [ seededEntry ];
  };
  registeredClaim = registeredRun.cells.typed-and-priority.config.candidate;

  staleRun = d.mkRun {
    subject = seededSubject;
    fixtures.typed-and-priority = toothFixture;
    register = [
      seededEntry
      staleEntry
    ];
  };
  staleClaim = staleRun.cells.typed-and-priority.config.candidate;

  # ── THE IDENTITY CONTROL, SEEDED ──────────────────────────────────────────────────────────────
  #
  # ★★★ THE CONTROL MUST BE SHOWN TO FAIL, OR IT IS INDISTINGUISHABLE FROM `true` — and this is the
  # defect class this whole corpus hunts, so it is measured here and not asserted in prose. The seam
  # below installs bodies through a path that has been perturbed: `mkForce` is mapped to the WRONG
  # priority constructor, which is the shape a surface swap actually fails in. The reference arm
  # does NOT travel that path and is untouched; the identity arm does, and diverges from it.
  #
  # ★★ THE FIRST SEEDING TRIED HERE WAS A NO-OP, AND THE CONTROL CAUGHT IT — which is worth
  # recording, because it is the same lesson one level down. Replacing `mkForce` with the IDENTITY
  # function leaves this fixture's answer unchanged: `a` still carries a plain definition beside a
  # `mkDefault` one, and plain still beats default, so the seeded arm agreed and the cell stayed
  # green. A seeding that does not move the observable proves nothing about whether the control can
  # fail. Mapping to `mkDefault` instead puts two same-priority definitions on a `str` option, which
  # both grammars refuse — so the identity arm declines where the reference answers.
  brokenInstall =
    body:
    d.mkArm {
      name = "${body.name}@broken-seam";
      vocab = body.vocab // {
        mkForce = body.vocab.mkDefault;
      };
      eval =
        req:
        body.evalModules {
          inherit (req) modules specialArgs;
        };
    };

  brokenSubject = d.mkSubject {
    reference = referenceArm;
    candidate = installAt genMergeBody;
    seam = d.mkSeam {
      name = "lib-surface-swap@perturbed";
      install = brokenInstall;
      referenceBody = nixpkgsBody;
    };
    claim = claimA;
  };

  brokenRun = d.mkRun {
    subject = brokenSubject;
    fixtures.typed-and-priority = toothFixture;
  };
  brokenIdentity = brokenRun.cells.typed-and-priority.config.identity;
in
{
  flake.tests.differential =
    cellsOf "A" runA
    // cellsOf "B" runB
    // {
      # ── THE RUN VERDICTS ──────────────────────────────────────────────────────────────────────
      test-run-A-green = {
        expr = runA.green;
        expected = true;
      };
      test-run-B-green = {
        expr = runB.green;
        expected = true;
      };

      # Every cell in the run carries the subject's claim. The retired instrument's defect was a red
      # that could not say which proposition it belonged to; this asserts the field is populated
      # everywhere rather than on the cells a reader happens to look at.
      test-every-claim-names-its-proposition = {
        expr = builtins.all (c: c.claim == claimA) runA.allClaims;
        expected = true;
      };
      test-the-two-claims-are-distinct = {
        expr = claimA != claimB && runB.claim == claimB;
        expected = true;
      };
      # The run travels the seam it declares — a subject whose cells did not route through the
      # substitution point would have an identity arm in name only.
      test-run-declares-its-seam = {
        expr = {
          a = runA.seam;
          b = runB.seam;
        };
        expected = {
          a = "lib-surface-swap";
          b = "evaluator-swap";
        };
      };
      # ★★ THE PARAMETERIZATION IS REAL AT THIS CONSUMER, NOT ONLY AT THE LIBRARY. A run carrying one
      # subject — or two whose seams are the same — is indistinguishable from a harness hard-coded to
      # one substrate. Two distinct substitution points, measured at the oracle rather than read off
      # the names.
      test-two-distinct-seams = {
        expr = d.oracles.distinctSubjects [
          subjectA
          subjectB
        ];
        expected = {
          count = 2;
          distinctSeams = 2;
          seams = [
            "lib-surface-swap"
            "evaluator-swap"
          ];
          claims = [
            claimA
            claimB
          ];
          ok = true;
        };
      };

      # ── WHICH ENGINE ACTUALLY RAN — the arms are not taken on their labels ─────────────────────
      # Both arms of both subjects, fingerprinted by a structural feature only one engine has. If
      # the seam had installed the wrong body, every comparison above would agree perfectly and
      # every anti-vacuity key would still pass; this is the cell that would not.
      test-arms-run-the-engines-they-name = {
        expr = {
          reference = engineFingerprint referenceArm;
          identityA = engineFingerprint (d.contract.identityArm subjectA);
          candidateA = engineFingerprint subjectA.candidate;
          identityB = engineFingerprint (d.contract.identityArm subjectB);
          candidateB = engineFingerprint subjectB.candidate;
        };
        expected = {
          # The reference and BOTH identity arms are nixpkgs — the identity arm is the reference's
          # own body, so it must fingerprint as nixpkgs however it travelled to get there.
          reference = nixpkgsFingerprint;
          identityA = nixpkgsFingerprint;
          identityB = nixpkgsFingerprint;
          # Both candidates are gen-merge's engine: subject A through the full surface swap, subject
          # B through the evaluator swap with nixpkgs' own leaf types injected.
          candidateA = genFingerprint;
          candidateB = genFingerprint;
        };
      };

      # ── THE COVERAGE FLOOR — the retired gate's keys, individually ─────────────────────────────
      test-floor-A-met = {
        expr = floorA.met;
        expected = true;
      };
      test-floor-B-met = {
        expr = floorB.met;
        expected = true;
      };
      test-floor-key-all-identical = {
        expr = floorA."all-identical";
        expected = true;
      };
      # THE ANTI-VACUITY KEY. Two arms that agree through a shared refusal have not been shown to
      # agree about anything else; without this, a corpus that threw everywhere would read green.
      test-floor-key-both-evaluated = {
        expr = floorA."both-evaluated";
        expected = true;
      };
      test-floor-key-teeth-mutation-diverges = {
        expr = floorA."teeth-mutation-diverges";
        expected = true;
      };
      # The floor this consumer meets is THREE keys, not the retired gate's four. `den-realism` is a
      # property of a real domain tree and is not met here — asserted so the shortfall is a
      # measurement rather than something a reader has to notice is missing.
      test-floor-keys-are-the-three-not-four = {
        expr = d.oracles.floorKeys;
        expected = [
          "all-identical"
          "both-evaluated"
          "teeth-mutation-diverges"
        ];
      };

      # ── THE TEETH ─────────────────────────────────────────────────────────────────────────────
      test-teeth-perturbation-moves-the-observable = {
        expr = toothMoved.moved;
        expected = true;
      };
      # The teeth's own control: a no-op perturbation must NOT move it, else `moved` is stuck true
      # and the tooth measures nothing.
      test-control-teeth-noop-does-not-move = {
        expr = toothStill.moved;
        expected = false;
      };

      # ── THE SEEDED DIVERGENCE — the REQUIRED mutation-teeth contract feature ───────────────────
      test-teeth-seeded-divergence-is-red = {
        expr = seededClaim.green;
        expected = false;
      };
      # ★ THE ATTRIBUTION, WHICH IS THE WHOLE REASON THE `claim` FIELD IS REQUIRED. A red names the
      # claim it belongs to, without an operator who already knows what was seeded.
      test-teeth-red-names-its-claim = {
        expr = seededClaim.claim;
        expected = claimA;
      };
      test-teeth-red-locates-the-divergence = {
        expr = seededClaim.firstDivergence.path;
        expected = [ "a" ];
      };
      test-teeth-red-carries-both-sides = {
        expr = {
          inherit (seededClaim.firstDivergence) aValue bValue;
        };
        expected = {
          aValue = "forced";
          bValue = "SEEDED";
        };
      };
      # The explanation renders as a red rather than as a green — `explain` is the operator-facing
      # surface, so its verdict prefix is asserted rather than assumed.
      test-teeth-explanation-reads-as-red = {
        expr = builtins.substring 0 4 (d.oracles.explain seededClaim);
        expected = "RED:";
      };
      test-control-explanation-reads-as-green = {
        expr = builtins.substring 0 5 (d.oracles.explain runA.cells.typed-and-priority.config.candidate);
        expected = "green";
      };
      # The seeded arm still EVALUATED — so the red is a genuine disagreement and not two arms
      # failing to produce anything, which the anti-vacuity key would otherwise let pass as one.
      test-teeth-seeded-red-is-a-disagreement-not-a-shared-throw = {
        expr = seededClaim.bothEvaluated;
        expected = true;
      };

      # ── THE REGISTER, BOTH DIRECTIONS ─────────────────────────────────────────────────────────
      test-register-admits-a-named-divergence = {
        expr = registeredClaim.green;
        expected = true;
      };
      test-register-lists-what-it-admitted = {
        expr = {
          registered = map (x: x.path) registeredClaim.registered;
          unregistered = registeredClaim.unregistered;
        };
        expected = {
          registered = [ [ "a" ] ];
          unregistered = [ ];
        };
      };
      # ★ THE ANTI-SUPPRESSION HALF. An entry whose divergence stops occurring goes RED; a register
      # that only ever silenced reds would pass this cell green.
      test-control-register-stale-entry-reddens = {
        expr = staleClaim.green;
        expected = false;
      };
      test-control-register-stale-entry-is-reported-missing = {
        expr = map (e: e.path) staleClaim.missing;
        expected = [ [ "b" ] ];
      };

      # ── THE IDENTITY CONTROL ──────────────────────────────────────────────────────────────────
      # The identity arm is the reference's own body travelling the candidate's seam, so it must
      # agree with the bare reference outright.
      test-identity-control-agrees-with-the-reference = {
        expr = builtins.all (c: c.arms != "reference↔identity" || c.green) runA.allClaims;
        expected = true;
      };
      # ★★★ AND IT CAN BE SEEDED TO FAIL, WHICH IS THE ONLY THING THAT DISTINGUISHES IT FROM `true`.
      # Perturbing the SEAM moves the identity arm and leaves the bare reference standing.
      test-control-identity-is-seedable = {
        expr = brokenIdentity.green;
        expected = false;
      };
      test-control-identity-seeded-red-names-its-claim = {
        expr = brokenIdentity.claim;
        expected = claimA;
      };
      # The perturbation is confined to the seam: the CANDIDATE arm in the same run does not travel
      # the broken install, so it stays green. A seeding that reddened everything would not have
      # shown the control is seedable — it would have shown the run is.
      test-control-identity-seeding-is-confined-to-the-seam = {
        expr = brokenRun.cells.typed-and-priority.config.candidate.green;
        expected = true;
      };

      # ── THE CORPUS IS THE ORACLE'S, NOT A SECOND ONE ──────────────────────────────────────────
      # A differential whose corpus drifts from the equivalence oracle's is two claims wearing one
      # name. This asserts the two read the same source rather than two files agreeing by habit.
      test-corpus-is-the-shared-parity-corpus = {
        expr = builtins.attrNames valueFixtures == builtins.attrNames corpus;
        expected = true;
      };
      # The refusal fixtures are the addition, and the count says so.
      test-fixture-count = {
        expr = builtins.length (builtins.attrNames fixtures);
        expected = builtins.length (builtins.attrNames corpus) + 2;
      };
    };
}
