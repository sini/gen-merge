# THE FIRST CONSUMER — a pure module-merge engine held against the reference on synthetic fixtures.
#
# ★ THIS IS THE INSTANTIATION THE LIBRARY WAS SPECIFIED FOR, AND IT NEEDS NO DOMAIN SUITE. The
# candidate is a from-scratch reimplementation of the definition→value fold: a genuinely different
# program, not a re-host of the reference's own body. That is what makes it a candidate in
# McKeeman's sense — "two or more comparable systems", one input, divergence as the signal — rather
# than a second reading of one system.
#
# ★★ THE DEPENDENCY ARROW POINTS SUBJECT → INSTRUMENT: the consumer pins the instrument and runs the
# differential in its own CI, and the instrument stays ignorant of its subjects. This file lived in
# gen-differential's `ci/` with the arrow reversed, and since this repository's `ci/` pins
# gen-differential that reversal closed a revision cycle (ADR-0037); it moved here, body verbatim.
{
  nixpkgsLib,
  genMerge,
  genDifferential,
}:
let
  gd = genDifferential;

  # ── THE CORE VOCABULARY ──────────────────────────────────────────────────────────────────────
  # ★ THE CANDIDATE DOES NOT PUBLISH THE ORDERING COMBINATORS, AND THE SUITE SAYS SO RATHER THAN
  # DISCOVERING IT MID-RUN. Each suite entry declares the vocabulary TIER it needs; drawing the
  # `core` tier is how a candidate with a smaller surface takes the fixtures it can actually run,
  # instead of aborting on a missing attribute halfway through and leaving a reader to work out
  # which fixture was the problem.
  coreNames = [
    "mkOption"
    "mkMerge"
    "mkOverride"
    "mkIf"
    "mkForce"
    "mkDefault"
    "types"
  ];
  coreVocab =
    impl:
    builtins.listToAttrs (
      map (n: {
        name = n;
        value = impl.${n};
      }) coreNames
    );

  # ── THE SEAM ─────────────────────────────────────────────────────────────────────────────────
  #
  # The module-system surface substitution: an implementation supplies its own vocabulary and its
  # own evaluator, and the seam adapts both to the comparison's shape. The adaptation is real work —
  # the two implementations do not agree on their request shape (the candidate's evaluator takes a
  # module list and nothing else) nor on their result shape (the reference's config and option trees
  # carry the module system's own synthetic pseudo-option, the candidate's do not).
  #
  # ★★★ AND THAT IS EXACTLY WHAT THE IDENTITY CONTROL ASSERTS HERE: *the adapter that makes the
  # candidate comparable does not itself change the answer **at the observables each fixture
  # declares***. Routing the REFERENCE through it must be invisible there. Without that claim, every
  # green in this file would be a green about the adapter as much as about the candidate, and there
  # would be no way to tell which.
  #
  # ★★ THE SCOPE IS NOT DECORATION — THE UNSCOPED SENTENCE IS MEASURABLY FALSE. The adapter really
  # does change the reference's result: `options._module` is present on the bare reference and
  # absent through the seam. The control is green because NO DECLARED OBSERVABLE REACHES THAT
  # SURFACE — `at [ "config" … ]` never descends into `options`, and `optionNames` filters the
  # pseudo-option on both sides. So the honest claim is bounded by the observable set, and widening
  # that set is what would put the adapter's own change back in view.
  install =
    impl:
    gd.mkArm {
      name = "${impl.name}@surface";
      vocab = coreVocab impl.vocab;
      eval =
        request:
        let
          r = impl.evalModules { inherit (request) modules; };
        in
        {
          config = builtins.removeAttrs r.config [ "_module" ];
          options = builtins.removeAttrs r.options [ "_module" ];
        };
    };

  referenceBody = {
    name = "nixpkgs";
    vocab = nixpkgsLib;
    evalModules = nixpkgsLib.evalModules;
  };

  candidateBody = {
    name = "gen-merge";
    vocab = genMerge;
    evalModules = r: genMerge.evalModuleTree (removeAttrs r [ "modules" ]) r.modules;
  };

  seam = gd.mkSeam {
    name = "module-system-surface";
    inherit install referenceBody;
  };

  # The bare reference — NOT routed through the seam, which is what keeps the identity arm a claim
  # rather than a tautology.
  reference = gd.mkArm {
    name = "nixpkgs";
    vocab = coreVocab nixpkgsLib;
    eval = nixpkgsLib.evalModules;
  };

  subject = gd.mkSubject {
    inherit reference seam;
    candidate = install candidateBody;
    claim = "P1 · the pure merge engine computes what the reference module system computes on the shared grammar";
  };

  # THE FIXTURES THE CANDIDATE'S VOCABULARY ADMITS, selected by the registry's declared tier rather
  # than by a hand-kept list that would drift from it.
  coreEntries = gd.suite.ofTier "core";
  fixtures = builtins.mapAttrs (
    name: entry:
    gd.contract.instantiate entry (
      if name == "synthetic" then
        {
          n = 6;
          ndecls = 4;
          layers = 2;
        }
      else
        { }
    )
  ) coreEntries;

  run = gd.mkRun { inherit subject fixtures; };
in
{
  inherit
    coreNames
    coreVocab
    install
    referenceBody
    candidateBody
    seam
    reference
    subject
    coreEntries
    fixtures
    run
    ;
}
