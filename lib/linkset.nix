# linkset.nix — merging two libraries' EXPORT ENVIRONMENTS by declared disjointness.
#
# ★ THE RELATUM IS A LINKSET, NOT A ROW, and that is what decides the mechanism. `lib/default.nix`
# assembles its published `types` by merging two libraries' export sets. Cardelli 1997 calls a set
# of named fragments a LINKSET and gates its merge on the export sets being disjoint — Definition
# 5-7's precondition, `exp(L) ∩ exp(L') = ∅`. The other merge in this tree, `redeclareDecl`, merges
# the FIELDS OF ONE OPTION RECORD, which is a row and takes Leijen's remedy. The two files are not
# inconsistent about one principle; they are two different objects.
#
# ★★ WHAT NIX `//` IS, EXACTLY. Cardelli Definition 5-5 (`used/markdown/cardelli-1997-program-
# fragments-linking.md:1080-1103`) defines compatible environments — `E1 ÷ E2` iff the two agree on
# every name they share — and merge as `E1+E2 ≜ E1, (E2\dom(E1))`, which is LEFT-biased. Nix `//` is
# RIGHT-biased, so `A // B` is the MIRROR: Cardelli's `B + A`. Lemma 5-6 makes commutation depend on
# `÷`, so under compatibility the bias is unobservable — and it is precisely the MISSING
# precondition that lets bias decide which library's `listOf` a consumer gets.
#
# ★★★ AND THE COMPATIBILITY TEST CANNOT BE WRITTEN AT THIS RELATUM, WHICH IS WHY THE RULE IS
# DISJOINTNESS RATHER THAN `÷`. At this site the colliding entries are CONSTRUCTORS, not types —
# `builtins.isFunction` is true on both sides — and gen's type equality is not TOTAL over functions:
# it forces `v.name` on a lambda and the abort escapes `tryEval`. A precondition that cannot be
# evaluated at the objects being merged is not a precondition. Cardelli supplies WHY the overlap
# must be decided at all; disjointness-with-a-declared-allowlist is the implementable form.
{ prelude }:
let
  inherit (builtins)
    attrNames
    concatStringsSep
    filter
    isString
    length
    ;

  # An overlap the allowlist does not name is a REFUSAL, and it names both contributors — a merge
  # that silently picked a winner is the defect this module exists to remove, and a refusal that
  # does not say who collided leaves the reader to re-derive it.
  refuseUndeclared =
    leftName: rightName: names:
    throw (
      "linkset: undeclared export collision between '${leftName}' and '${rightName}' at "
      + "${if length names == 1 then "name" else "names"} "
      + concatStringsSep ", " (map (n: "'${n}'") names)
      + ". Every overlap is decided explicitly: add an allowlist entry carrying the ground for "
      + "which side wins at that name, or rename one side."
    );

  # ★ AN ENTRY WITH NO GROUND DOES NOT CONSTRUCT. A declared exemption with an empty reason is a
  # silent drop with extra syntax — the very thing the allowlist replaces.
  refuseGroundless =
    name:
    throw (
      "linkset: allowlist entry '${name}' carries no ground. An exemption without a stated reason "
      + "is a silent shadow with extra syntax; state why the winning side wins AT THIS NAME."
    );

  # ★★ THE DISTINCTNESS FLOOR, AND ITS LIMIT IS STATED RATHER THAN PAPERED OVER. No entry's ground
  # may be byte-identical to another's. That catches the VERBATIM copy and nothing else: a
  # paraphrased ground defeats it, and no predicate writable here catches that. The substantive
  # check — does this ground actually hold OF THIS NAME? — is an honest person-oracle sitting ON TOP
  # of this floor, not instead of it. A mechanical check that cannot fail on the real hazard is a
  # false green, and a false green here is worse than an acknowledged human read.
  refuseCopiedGround =
    a: b:
    throw (
      "linkset: allowlist entries '${a}' and '${b}' carry byte-identical grounds. A ground copied "
      + "from one name to another is the hazard the allowlist exists to expose; the copy may also "
      + "be FALSE at the second name. State each entry's own reason."
    );

  duplicateGround =
    entries:
    let
      names = attrNames entries;
      pairs = prelude.concatLists (map (a: map (b: { inherit a b; }) (filter (b: b > a) names)) names);
      clash = filter (p: entries.${p.a}.ground == entries.${p.b}.ground) pairs;
    in
    if clash == [ ] then null else prelude.head clash;
in
{
  # mergeExports — Cardelli's linkset merge, gated on declared disjointness.
  #
  #   left  : { library; exports; }   the environment that LOSES an admitted collision
  #   right : { library; exports; }   the environment that WINS one (Nix `//` is right-biased)
  #   allow : { <name> = { ground = "…"; }; }   the RIGHT side's declaration of where it wins
  #
  # ★ THE RETENTION RECORD IS REQUIRED AND PERMANENT (owner-ruled). Every ADMITTED shadow carries an
  # `overridden` record naming the shadowed value and the library it came from. This is Leijen's
  # remedy — a shadowed label stays reachable rather than being destroyed — applied where the shadow
  # is ADMITTED rather than where it is refused, and the two disciplines are complementary:
  # Cardelli's decides admission, Leijen's decides what admission costs. The record is never
  # removable: a shadow whose loser is unreachable is a silent drop wearing a declaration.
  #
  # ★ AN UNDECLARED COLLISION REFUSES PER NAME. Each overlap the allowlist does not name is bound to
  # its own named refusal, and every other name publishes: a demand is judged only on the names it
  # touches, the rule `lib/default.nix` states for `scopeDefect` ("a name nothing here demands") and
  # for the `types` binding ("judged only on names this library demands"). The merge is then of the
  # DECIDED domain — Cardelli's `L\U + L'\U`, disjoint up to the allowlist — with each `u ∈ U`
  # answering by name. Lemma 5-8 makes that restriction a linkset only if no remaining fragment
  # depends on a removed export, which holds because BOTH export environments are closed: neither
  # side's exports read the merged environment. The declaration-hygiene refusals — groundless,
  # copied, stale — stay whole-merge, being defects in the right side's own declaration rather than
  # facts about a name; so a link with an undeclared collision AND a stale entry raises the stale one.
  mergeExports =
    {
      left,
      right,
      allow,
    }:
    let
      collisions = filter (n: right.exports ? ${n}) (attrNames left.exports);
      undeclared = filter (n: !(allow ? ${n})) collisions;
      declared = filter (n: allow ? ${n}) collisions;

      groundless = filter (
        n: !(allow.${n} ? ground) || !(isString allow.${n}.ground) || allow.${n}.ground == ""
      ) (attrNames allow);

      copied = duplicateGround allow;

      # An allowlist entry naming a name the RIGHT side does not export is a stale exemption — it
      # reads as a decided overlap and can decide nothing, whatever the left supplies. Named rather
      # than ignored. It is judged against `right` alone because the allowlist is right's claim: an
      # entry naming a name the LEFT lacks is inapplicable to this link (no overlap there, nothing
      # decided, nothing shadowed), not stale, and refusing on it would judge the left for the right's
      # hygiene. Whether a particular left still collides at each entry is a fact about that pair,
      # checked by whoever pins the pair.
      stale = filter (n: !(right.exports ? ${n})) (attrNames allow);

      admitted = prelude.listToAttrs (
        map (n: {
          name = n;
          value = {
            inherit (allow.${n}) ground;
            # Leijen's retention: the shadowed value stays reachable, with its provenance.
            overridden = {
              value = left.exports.${n};
              library = left.library;
            };
            shadowedBy = right.library;
          };
        }) declared
      );

      # An undecided name is BOUND TO ITS REFUSAL rather than taking the namespace with it: the
      # decision is owed per name, so the merge is of the decided domain and every undecided name
      # still answers, by name, when demanded.
      refusedAt = prelude.listToAttrs (
        map (n: {
          name = n;
          value = refuseUndeclared left.library right.library [ n ];
        }) undeclared
      );
    in
    if groundless != [ ] then
      refuseGroundless (prelude.head groundless)
    else if copied != null then
      refuseCopiedGround copied.a copied.b
    else if stale != [ ] then
      throw (
        "linkset: allowlist entry '${prelude.head stale}' names no export of '${right.library}', "
        + "the side the allowlist decides in favour of. A stale exemption reads as a decided overlap "
        + "and decides nothing; remove it or state the collision it is for."
      )
    else
      {
        exports = left.exports // right.exports // refusedAt;
        # The admitted shadows, as data a consumer can read — which is what makes the declaration
        # checkable from outside rather than a comment inside this file.
        inherit admitted;
      };
}
