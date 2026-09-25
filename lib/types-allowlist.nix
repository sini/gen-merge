{
  listOf.ground = ''
    This namespace is the drop-in a foreign module system mounts, and at this name such a
    consumer requires the CROSS-DEFINITION MERGE meaning: the strategy folds definitions
    across modules, where gen-types' constructor is a structural PREDICATE over one value.
    The cost is exactly the unqualified spelling inside this namespace — the gen-types
    predicate stays reachable through the hub's flat roster and from gen-types directly.
  '';
  attrsOf.ground = ''
    The same cross-definition merge meaning as `listOf`, over attribute sets rather than
    lists: a mounting consumer declaring `attrsOf` in a foreign module system needs
    definitions from several modules folded, not one value checked. Stated for THIS name
    rather than carried from `listOf` because the two constructors differ in what they fold.
  '';
  attrs.ground = ''
    The one name at which BOTH sides mint a nullary VALUE rather than a constructor, and the
    drop-in meaning here is the folding one twice over: a mounting consumer declaring `attrs`
    needs what several modules contribute to that option COMBINED, and needs an answer for the
    case where nobody contributed anything. Neither is sayable by a predicate over one value,
    which is what gen-types' entry is; that predicate stays reachable through the hub's flat
    roster and from gen-types directly, unchanged and still minted where it was.
  '';
  option.ground = ''
    ★ THE WEAKEST ENTRY, AND IT SAYS SO. This library's `option` is a bare alias for
    `nullOr`, so what shadows gen-types' parametric `option` is an alias rather than a
    distinct construct — the winning side wins by sitting in the drop-in namespace, not by
    meaning more. This is the first entry to retire if the namespace is ever split.
  '';
}
