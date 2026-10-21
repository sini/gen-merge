# The whole-value judgement (den-hoag-2wo5a): `verifyValue type value` is `null` exactly where gen's fold of the one
# definition `value` at `type`, read to the type's depth, serves it, and otherwise names the failing position and why.
# The judgement's descent is parallel to the fold's (lib/types.nix `judgeAt`), so this file is its drift oracle: every
# cell is judged against the fold itself, computed in the same run, and the refusals name the path the fold's own locs
# name. The drift witnesses the spec gate found (a `// { verify }` refined container, a freeform definition, a foreign
# record at any level) are cells here. A foreign refusal nixpkgs throws below its head propagates (the error plane pins
# its text, `ci/tests-error.nix` `verify-value`), and reads here as "not served", never as `null`.
# Red at gen-merge main 28653f3 (f251ddb): `verifyValue` is absent, so every key of every test here aborts.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  t = gm.types;
  nl = nixpkgsLib;
  nt = nl.types;
  inherit (builtins)
    deepSeq
    mapAttrs
    seq
    attrNames
    tryEval
    ;
  S = t.submodule { options.port = gm.mkOption { type = t.int; }; };
  nS = nt.submodule { options.port = nl.mkOption { type = nt.int; }; };
  pS = gm.partialSubmodule { options.port = gm.mkOption { type = t.int; }; };
  tree = (gm.evalModuleTree { } [ { options.port = gm.mkOption { type = t.int; }; } ]).type;
  spool = gm.deriveType { } "spool" (t.listOf t.int);
  refined = gm.mkOptionType (
    t.attrsOf t.int
    // {
      verify = v: if v ? a then null else "needs key a";
    }
  );
  FF = t.submodule {
    freeformType = t.attrsOf t.int;
    options.port = gm.mkOption {
      type = t.int;
      default = 1;
    };
  };
  # cell = { g; v; n ? nixpkgs twin; force ? the type's depth, deepSeq where unstated }
  cells = {
    attrsOf-good = {
      g = t.attrsOf t.int;
      n = nt.attrsOf nt.int;
      v.a = 1;
    };
    attrsOf-bad = {
      g = t.attrsOf t.int;
      n = nt.attrsOf nt.int;
      v = {
        a = 1;
        b = "x";
      };
    };
    attrsOf-shallow = {
      g = t.attrsOf t.int;
      n = nt.attrsOf nt.int;
      v = [ 1 ];
    };
    lazyAttrsOf-good = {
      g = t.lazyAttrsOf t.int;
      n = nt.lazyAttrsOf nt.int;
      v.a = 1;
    };
    lazyAttrsOf-bad = {
      g = t.lazyAttrsOf t.int;
      n = nt.lazyAttrsOf nt.int;
      v.a = "x";
    };
    partialAttrsOf-good = {
      g = gm.partialAttrsOf t.int;
      v.a = 1;
    };
    partialAttrsOf-bad = {
      g = gm.partialAttrsOf t.int;
      v.a = "x";
    };
    listOf-good = {
      g = t.listOf t.int;
      n = nt.listOf nt.int;
      v = [
        1
        2
      ];
    };
    listOf-bad = {
      g = t.listOf t.int;
      n = nt.listOf nt.int;
      v = [
        1
        "x"
      ];
    };
    listOf-shallow = {
      g = t.listOf t.int;
      n = nt.listOf nt.int;
      v = { };
    };
    nullOr-null = {
      g = t.nullOr t.int;
      n = nt.nullOr nt.int;
      v = null;
    };
    nullOr-good = {
      g = t.nullOr t.int;
      n = nt.nullOr nt.int;
      v = 1;
    };
    nullOr-bad = {
      g = t.nullOr t.int;
      n = nt.nullOr nt.int;
      v = "x";
    };
    nullOr-nested-bad = {
      g = t.nullOr (t.listOf t.int);
      n = nt.nullOr (nt.listOf nt.int);
      v = [ "x" ];
    };
    either-good-a = {
      g = t.either t.int t.str;
      n = nt.either nt.int nt.str;
      v = 1;
    };
    either-good-b = {
      g = t.either t.int t.str;
      n = nt.either nt.int nt.str;
      v = "s";
    };
    either-bad = {
      g = t.either t.int t.str;
      n = nt.either nt.int nt.str;
      v = true;
    };
    either-shallow-choice = {
      g = t.either (t.attrsOf t.int) (t.attrsOf t.str);
      n = nt.either (nt.attrsOf nt.int) (nt.attrsOf nt.str);
      v.a = "x";
    };
    oneOf-good = {
      g = t.oneOf [
        t.int
        t.str
        t.bool
      ];
      n = nt.oneOf [
        nt.int
        nt.str
        nt.bool
      ];
      v = true;
    };
    oneOf-bad = {
      g = t.oneOf [
        t.int
        t.str
        t.bool
      ];
      n = nt.oneOf [
        nt.int
        nt.str
        nt.bool
      ];
      v = 1.5;
    };
    submodule-good = {
      g = S;
      n = nS;
      v.port = 1;
    };
    submodule-bad = {
      g = S;
      n = nS;
      v.port = "x";
    };
    submodule-undeclared = {
      g = S;
      n = nS;
      v = {
        port = 1;
        porx = 2;
      };
    };
    submodule-missing = {
      g = S;
      n = nS;
      v = { };
    };
    submodule-shallow = {
      g = S;
      n = nS;
      v = 1;
    };
    partialSubmodule-good = {
      g = pS;
      v.port = 1;
    };
    partialSubmodule-bad = {
      g = pS;
      v.port = "x";
    };
    nested-deep-good = {
      g = t.attrsOf (t.listOf S);
      n = nt.attrsOf (nt.listOf nS);
      v.a = [ { port = 1; } ];
    };
    nested-deep-bad = {
      g = t.attrsOf (t.listOf S);
      n = nt.attrsOf (nt.listOf nS);
      v.a = [
        { port = 1; }
        { port = "x"; }
      ];
    };
    attrs-good = {
      g = t.attrs;
      n = nt.attrs;
      v.a = 1;
    };
    attrs-bad = {
      g = t.attrs;
      n = nt.attrs;
      v = 1;
    };
    deferredModule-good = {
      g = t.deferredModule;
      n = nt.deferredModule;
      v = { };
    };
    deferredModule-bad = {
      g = t.deferredModule;
      n = nt.deferredModule;
      v = 1;
    };
    optionType-bad = {
      g = t.optionType;
      n = nt.optionType;
      v = 1;
    };
    anything-good = {
      g = t.anything;
      n = nt.anything;
      v.a = [ 1 ];
    };
    unspecified-good = {
      g = t.unspecified;
      n = nt.unspecified;
      v = 1;
    };
    derived-good = {
      g = spool;
      v = [ 1 ];
    };
    derived-bad = {
      g = spool;
      v = [ "x" ];
    };
    treetype-good = {
      g = tree;
      v.port = 1;
    };
    treetype-bad = {
      g = tree;
      v.port = "x";
    };
    leaf-int-good = {
      g = t.int;
      n = nt.int;
      v = 1;
    };
    leaf-int-bad = {
      g = t.int;
      n = nt.int;
      v = "x";
    };
    # the discharge spine runs first: a marker is judged as the definition it discharges to
    marker-mkIf = {
      g = t.attrsOf t.int;
      v = {
        a = 1;
        b = gm.mkIf false "x";
      };
    };
    marker-mkIf-true = {
      g = t.attrsOf t.int;
      v.a = gm.mkIf true 1;
    };
    # the drift witnesses: a refinement's `verify` on the merged value, a freeform definition, a foreign record
    refined-good = {
      g = refined;
      v.a = 1;
    };
    refined-bad = {
      g = refined;
      v.b = 1;
    };
    freeform-good = {
      g = FF;
      v.x = 2;
    };
    freeform-bad = {
      g = FF;
      v.x = "s";
    };
    foreign-elem-good = {
      g = t.attrsOf nt.int;
      v.a = 1;
    };
    foreign-elem-bad = {
      g = t.attrsOf nt.int;
      v.a = "x";
    };
    foreign-top-leaf-bad = {
      g = nt.int;
      v = "x";
    };
    foreign-top-container-bad = {
      g = nt.attrsOf nt.int;
      v.a = "x";
    };
    foreign-nested-container-bad = {
      g = t.attrsOf (nt.attrsOf nt.int);
      v.a.b = "x";
    };
    foreign-submodule-elem-good = {
      g = t.attrsOf nS;
      v.a.port = 1;
    };
    foreign-submodule-elem-bad = {
      g = t.attrsOf nS;
      v.a.port = "x";
    };
    # laziness: `lazyAttrsOf raw` serves at the key set without reading its payload
    raw-lazy = {
      g = t.lazyAttrsOf t.raw;
      v.a = throw "payload";
      force = x: seq (attrNames x) true;
    };
  };
  twins = builtins.removeAttrs cells (builtins.filter (k: !(cells.${k} ? n)) (attrNames cells));
  fold =
    c:
    (gm.evalModuleTree { } [
      { options.o = gm.mkOption { type = c.g; }; }
      { o = c.v; }
    ]).config.o;
  serves = c: (tryEval ((c.force or (x: deepSeq x true)) (fold c))).success;
  # a judgement that throws (a foreign refusal propagating) is not a `null`
  judged =
    c:
    let
      r = tryEval (
        let
          x = gm.verifyValue c.g c.v;
        in
        deepSeq x x
      );
    in
    if r.success then r.value else "THROWS";
in
{
  flake.tests.verify-value = {
    # G1′'s GREEN, the drift oracle: `null` exactly where the fold serves, cell by cell, against the fold in this run
    test-the-judgement-is-null-exactly-where-the-fold-serves = {
      expr = mapAttrs (_: c: judged c == null) cells;
      expected = mapAttrs (_: serves) cells;
    };
    # G1 and G1′ by text: each refusal names the position by the fold's own locs, relative to the value, with the
    # leaf's own `verify` text, the domain the fold's door refuses with, or the tree's own finding after it
    test-each-refusal-names-its-position = {
      expr = mapAttrs (_: judged) cells;
      expected = {
        attrsOf-good = null;
        attrsOf-bad = "`b': expected type 'int' but value \"x\" is of type 'string'";
        attrsOf-shallow = "`<value>': `attrsOf' cannot consume a list (<value>)";
        lazyAttrsOf-good = null;
        lazyAttrsOf-bad = "`a': expected type 'int' but value \"x\" is of type 'string'";
        partialAttrsOf-good = null;
        partialAttrsOf-bad = "`a': expected type 'int' but value \"x\" is of type 'string'";
        listOf-good = null;
        listOf-bad = "`\"[definition 1-entry 2]\"': expected type 'int' but value \"x\" is of type 'string'";
        listOf-shallow = "`<value>': `listOf' cannot consume a set (<value>)";
        nullOr-null = null;
        nullOr-good = null;
        nullOr-bad = "`<value>': `nullOr' cannot consume a string (<value>)";
        nullOr-nested-bad = "`\"[definition 1-entry 1]\"': expected type 'int' but value \"x\" is of type 'string'";
        either-good-a = null;
        either-good-b = null;
        either-bad = "`<value>': `either' cannot consume a bool (<value>)";
        either-shallow-choice = "`a': expected type 'int' but value \"x\" is of type 'string'";
        oneOf-good = null;
        oneOf-bad = "`<value>': `either' cannot consume a float (<value>)";
        submodule-good = null;
        submodule-bad = "`port': expected type 'int' but value \"x\" is of type 'string'";
        submodule-undeclared = "`porx': the option does not exist";
        submodule-missing = "`port': is used but not defined";
        submodule-shallow = "`<value>': `submodule' cannot consume a int (<value>)";
        partialSubmodule-good = null;
        partialSubmodule-bad = "`port': expected type 'int' but value \"x\" is of type 'string'";
        nested-deep-good = null;
        nested-deep-bad = "`a.\"[definition 1-entry 2]\".port': expected type 'int' but value \"x\" is of type 'string'";
        attrs-good = null;
        attrs-bad = "`<value>': `attrs' cannot consume a int (<value>)";
        deferredModule-good = null;
        deferredModule-bad = "`<value>': `deferredModule' cannot consume a int (<value>)";
        optionType-bad = "`<value>': `optionType' cannot consume a int (<value>)";
        anything-good = null;
        unspecified-good = null;
        derived-good = null;
        derived-bad = "`\"[definition 1-entry 1]\"': expected type 'int' but value \"x\" is of type 'string'";
        treetype-good = null;
        treetype-bad = "`port': expected type 'int' but value \"x\" is of type 'string'";
        leaf-int-good = null;
        leaf-int-bad = "`<value>': expected type 'int' but value \"x\" is of type 'string'";
        marker-mkIf = null;
        marker-mkIf-true = null;
        refined-good = null;
        refined-bad = "`<value>': needs key a";
        freeform-good = null;
        freeform-bad = "`x': expected type 'int' but value \"s\" is of type 'string'";
        foreign-elem-good = null;
        foreign-elem-bad = "`a': is not of type `signed integer' (<value>)";
        foreign-top-leaf-bad = "`<value>': is not of type `signed integer' (<value>)";
        foreign-top-container-bad = "THROWS";
        foreign-nested-container-bad = "THROWS";
        foreign-submodule-elem-good = null;
        foreign-submodule-elem-bad = "THROWS";
        raw-lazy = null;
      };
    };
    # G2: the exported `check` stays nixpkgs' shallow per-definition predicate, cell by cell over every twin
    test-check-is-unchanged-and-agrees-with-nixpkgs = {
      expr = mapAttrs (_: c: c.g.check c.v) twins;
      expected = mapAttrs (_: c: c.n.check c.v) twins;
    };
    # G3: a leaf's own `verify` is unchanged
    test-a-leaf-verify-is-unchanged = {
      expr = {
        bad = t.int.verify "x";
        good = t.int.verify 1;
      };
      expected = {
        bad = "expected type 'int' but value \"x\" is of type 'string'";
        good = null;
      };
    };
  };
}
