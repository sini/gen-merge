# A container gen-merge itself COMPLETED crosses the `mkOptionType` door as itself where it may nest. Each value
# below is read through the door by gen's engine and, on the SAME record, by nixpkgs' `lib.evalModules`, which
# evaluates the gen record through its exported protocol. RED (every cell `"REFUSED"`) where the door refused the
# record at construction. The checked copies' rejected value is refused by name where nixpkgs drops the check, so
# it is pinned on the error plane (`ci/tests-error.nix`, `gen-container-door`), with the payload-offer element whose
# refusal is raised where the option is bound.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib.types;
  door = gm.mkOptionType;
  sub = t.submodule { options.a = gm.mkOption { type = t.int; }; };
  json =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x (builtins.toJSON x));
    in
    if r.success then r.value else "REFUSED";
  defs = v: if v == null then [ ] else [ { x = v; } ];
  gen =
    ty: v:
    json
      (gm.evalModuleTree { } (
        [
          {
            options.x = gm.mkOption {
              type = door ty;
              default = null;
            };
          }
        ]
        ++ defs v
      )).config.x;
  nixpkgs =
    ty: v:
    json
      (nixpkgsLib.evalModules {
        modules = [
          {
            options.x = nixpkgsLib.mkOption {
              type = ty;
              default = null;
            };
          }
        ]
        ++ defs v;
      }).config.x;
  # each row: the record, and the values it is read at
  vals =
    w:
    map w [
      null
      { a = 2; }
      { a = 1; }
    ];
  inAttrs = v: if v == null then null else { k = v; };
  inList = v: if v == null then null else [ v ];
  p = v: v == null || (v.a or 0) != 1;
  rows = {
    nullOr = {
      ty = t.nullOr sub;
      vs = vals (v: v);
    };
    attrsOf = {
      ty = t.attrsOf sub;
      vs = vals inAttrs;
    };
    listOf = {
      ty = t.listOf sub;
      vs = vals inList;
    };
    either = {
      ty = t.either sub t.str;
      vs = vals (v: v) ++ [ "s" ];
    };
    nullOrNullOr = {
      ty = t.nullOr (t.nullOr sub);
      vs = vals (v: v);
    };
    attrsOfNullOr = {
      ty = t.attrsOf (t.nullOr sub);
      vs = vals inAttrs;
    };
    # the door over its own output, whose record is gen's `nullOr` over the element
    doorOverItsOwnOutput = {
      ty = door (np.nullOr sub);
      vs = vals (v: v);
    };
    doorTwice = {
      ty = door (t.nullOr sub);
      vs = vals (v: v);
    };
    # the checked copies at the values their check admits
    checkCopy = {
      ty =
        let
          b = t.nullOr sub;
        in
        b // { check = v: b.check v && p v; };
      vs = [
        null
        { a = 2; }
      ];
    };
    addCheck = {
      ty = np.addCheck (t.nullOr sub) p;
      vs = [
        null
        { a = 2; }
      ];
    };
    # a cyclic gen container: `canNest` answers "may nest" at the fuel's exhaustion
    cyclic = {
      ty =
        let
          r = t.either t.int (t.listOf r);
        in
        r;
      vs = [
        1
        [
          1
          [ 2 ]
        ]
      ];
    };
    cyclicOverASubmodule = {
      ty =
        let
          r = t.either sub (t.listOf r);
        in
        r;
      vs = [
        { a = 2; }
        [
          { a = 2; }
          [ { a = 3; } ]
        ]
      ];
    };
    # an element marked `declaresNesting = true` below a gen container is bound as gen's container binds it
    overAMarkedElement = {
      ty = t.nullOr (np.attrsOf sub // { declaresNesting = true; });
      vs = vals inAttrs;
    };
  };
  readAll = read: builtins.mapAttrs (_: r: map (read r.ty) r.vs) rows;
  teq = genTypes.typeEq;
  showB =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if !r.success then
      "REFUSED"
    else if r.value then
      "true"
    else
      "false";
  identity =
    b:
    let
      copies = {
        intact = b;
        description = b // {
          description = "described";
        };
        check = b // {
          check = v: b.check v && v != 1;
        };
      };
    in
    builtins.mapAttrs (_: c: {
      base = showB (teq (door c) b);
      self = showB (teq (door c) c);
    }) copies;
in
{
  flake.tests.gen-container-door = {
    test-a-gen-container-through-the-door-reads-nixpkgs-value-on-the-same-record = {
      expr = readAll gen;
      expected = readAll nixpkgs;
    };
    # The import's own identity rule, as it is for a container over no nesting element (`listOf int`): the door's
    # result is `typeEq` to an intact record, a `description` copy keeps its base's identity and a check copy keeps
    # its witness. RED (every row `"REFUSED"`) where the door refused the nesting record.
    test-a-gen-container-through-the-door-keeps-the-import-identity-rule = {
      expr = identity (t.nullOr sub);
      expected = identity (t.listOf t.int);
    };
    test-the-identity-rule-over-no-nesting-element = {
      expr = identity (t.listOf t.int);
      expected = {
        intact = {
          base = "true";
          self = "true";
        };
        description = {
          base = "true";
          self = "REFUSED";
        };
        check = {
          base = "false";
          self = "REFUSED";
        };
      };
    };
  };
}
