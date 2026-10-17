# WHICH NIXPKGS CONTAINERS FORWARD THEIR ELEMENT IS ONE TABLE, DERIVED FROM NIXPKGS (den-hoag-j2ryo).
#
# `lib/interface.nix` `sameValue.foreignForwarding` states, per nixpkgs constructor, the role its sub-protocol reads
# forward to, whether the forward adds a `getSubOptions` segment, the roles its `getSubModules` forces, and
# whether the constructor ships a `merge.v2`. nixpkgs decides each of these in the constructor's own body, so
# every row here is DERIVED from nixpkgs' constructors by their behaviour, never read from a name: each
# constructor is applied to MARKER element types, one per role, that answer the three reads with their role
# (`getSubModules = [ role ]`, `getSubOptions = p: { ${role} = p; }`, `substSubModules` a marker over the new
# set), and the record's own answers say what it forwards. A second marker set whose `getSubModules` throws
# says which roles the record's `getSubModules` forces. The cells hold the table equal to that derivation at
# the locked nixpkgs, and every constructor in `ctors` that forwards (grouped by its functor's name, as
# nixpkgs' `defaultTypeMerge` keys a constructor) to a row. `ctors` is written by hand: applying every
# `lib.types` attribute to markers aborts uncatchably on a constructor of another arity (`attrListWith`
# without its `elemType`), so the universal is over the constructors listed, not derived.
#
# RED, evaluated at gen-merge 1d5741e (no table): `interface.sameValue.foreignForwarding` is missing and every
# cell aborts on the attribute. Driven red by a planted table whose `unique` row states `level = true`: the
# equality cell then names that row.
{
  interface,
  nixpkgsLib,
  ...
}:
let
  lib = nixpkgsLib;
  t = lib.types;
  table = interface.sameValue.foreignForwarding;
  mk =
    role: getSubModules:
    lib.mkOptionType {
      name = "marker-${role}";
      check = _: true;
      merge = _: defs: (lib.head defs).value;
      inherit getSubModules;
      getSubOptions = p: { ${role} = p; };
      substSubModules = m: mk role m;
    };
  M = role: mk role [ role ];
  R = role: mk role (throw "read ${role}");
  # `coercedTo` asserts its coerced member states no module set, so that member is a leaf marker except
  # where its own read is the one probed (its marker throws)
  leafUnlessProbed =
    k:
    let
      r = builtins.tryEval k.getSubModules;
    in
    if r.success then mk "coercedType" null else k;
  # the nixpkgs constructors of a type over element types, applied to the markers `r`, with their roles
  ctors = {
    listOf = {
      roles = [ "elemType" ];
      of = r: t.listOf (r "elemType");
    };
    nonEmptyListOf = {
      roles = [ "elemType" ];
      of = r: t.nonEmptyListOf (r "elemType");
    };
    nullOr = {
      roles = [ "elemType" ];
      of = r: t.nullOr (r "elemType");
    };
    attrsOf = {
      roles = [ "elemType" ];
      of = r: t.attrsOf (r "elemType");
    };
    lazyAttrsOf = {
      roles = [ "elemType" ];
      of = r: t.lazyAttrsOf (r "elemType");
    };
    attrsWith = {
      roles = [ "elemType" ];
      of = r: t.attrsWith { elemType = r "elemType"; };
    };
    attrListOf = {
      roles = [ "elemType" ];
      of = r: t.attrListOf (r "elemType");
    };
    unique = {
      roles = [ "elemType" ];
      of = r: t.unique { message = "m"; } (r "elemType");
    };
    uniq = {
      roles = [ "elemType" ];
      of = r: t.uniq (r "elemType");
    };
    functionTo = {
      roles = [ "elemType" ];
      of = r: t.functionTo (r "elemType");
    };
    coercedTo = {
      roles = [
        "coercedType"
        "finalType"
      ];
      of = r: t.coercedTo (leafUnlessProbed (r "coercedType")) (x: x) (r "finalType");
    };
    either = {
      roles = [
        "left"
        "right"
      ];
      of = r: t.either (r "left") (r "right");
    };
    oneOf = {
      roles = [
        "a"
        "b"
      ];
      of =
        r:
        t.oneOf [
          (r "a")
          (r "b")
        ];
    };
    attrTag = {
      roles = [ "tags" ];
      of =
        r:
        t.attrTag {
          a = lib.mkOption { type = r "tags"; };
          b = lib.mkOption { type = r "tags"; };
        };
    };
  };
  ok = x: (builtins.tryEval (builtins.deepSeq x x)).success;
  value = x: (builtins.tryEval (builtins.deepSeq x x)).value;
  # one constructor's behaviour, as a row
  derive =
    c:
    let
      v = c.of M;
      gsm = value v.getSubModules;
      forward =
        if builtins.isList gsm && builtins.length gsm == 1 && builtins.elem (builtins.head gsm) c.roles then
          builtins.head gsm
        else
          null;
      seg = if forward == null then null else (value (v.getSubOptions [ "P" ])).${forward} or null;
      reads = builtins.filter (
        role: !(ok (c.of (x: if x == role then R x else M x)).getSubModules)
      ) c.roles;
    in
    {
      inherit forward;
      level = if seg == null then null else seg != [ "P" ];
      # a record forcing every member it states (`attrTag`'s tags) states no fixed role list
      reads = if forward == null && reads != [ ] then null else reads;
      v2 = v ? merge.v2;
      functorName = v.functor.name;
    };
  derived = lib.mapAttrs (_: derive) (lib.filterAttrs (n: _: t ? ${n}) ctors);
  # the forwarding constructors, grouped by functor name, each group's rows equal
  forwarding = lib.filterAttrs (_: r: r.forward != null || r.reads == null) derived;
  byFunctor = lib.groupBy (r: r.functorName) (builtins.attrValues forwarding);
  row = r: {
    inherit (r)
      forward
      level
      reads
      v2
      ;
  };
in
{
  flake.tests.forwarding-table = {
    # every forwarding constructor in `ctors` has its row, under its functor's name, and no row names a
    # constructor that does not forward
    test-the-table-names-every-forwarding-constructor = {
      expr = builtins.attrNames table;
      expected = builtins.attrNames byFunctor;
    };
    # each row is what nixpkgs' constructor does
    test-each-row-is-the-constructor-behaviour = {
      expr = lib.mapAttrs (_: row) table;
      expected = lib.mapAttrs (_: rs: row (builtins.head rs)) byFunctor;
    };
    # the constructors sharing a functor's name (`attrsOf`, `lazyAttrsOf`, `attrsWith`; `unique`, `uniq`;
    # `listOf`, `nonEmptyListOf`) behave alike, so one row per name states them
    test-one-functor-name-is-one-behaviour = {
      expr = lib.mapAttrs (_: rs: builtins.length (lib.unique (map row rs))) byFunctor;
      expected = lib.mapAttrs (_: _: 1) byFunctor;
    };
    # a union forwards nothing and forces no member, so it is not a row (live control: the derivation can
    # answer "none")
    test-a-union-forwards-nothing = {
      expr = map (n: row derived.${n}) [
        "either"
        "oneOf"
      ];
      expected = [
        {
          forward = null;
          level = null;
          reads = [ ];
          v2 = true;
        }
        {
          forward = null;
          level = null;
          reads = [ ];
          v2 = true;
        }
      ];
    };
    # the spine steps every forwarding row but the one its comment prices (`attrListOf`)
    test-the-spine-steps-every-forwarding-row-but-attrListOf = {
      expr = builtins.attrNames (lib.filterAttrs (_: r: (r.forward != null) != r.spine) table);
      expected = [ "attrListOf" ];
    };
  };
}
