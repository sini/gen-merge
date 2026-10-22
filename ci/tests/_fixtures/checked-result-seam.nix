# AN EVALUATION'S RESULT, READ THROUGH ITS REFUSAL, on two engines: nixpkgs' `evalModules` (np, the reference) and
# gen-merge's `evalModuleTree` (gm). Read by the value cells (`../checked-result-seam.nix`).
#
# nixpkgs binds `checked = seq checkUnmatched` and returns `options`, `config` and `_module` through it, so a read of
# any of the three refuses where `_module.check` holds and a definition is undeclared, or where `_module.check` or
# `_module.freeformType` itself refuses. `submoduleWith` reads its base evaluation's `_module` (`nestedTypes`) and its
# documentation evaluation's (`description`, `getSubOptions`) through the same seam.
#
# `result`: eleven module sets (three nixpkgs serves: `clean`, `lax`, `ff`) × every read of the result's attributes,
# an evaluation's own `.type` among them. `nested`: seven type-module and definition states of a submodule × the
# reads `submoduleWith` routes through its two evaluations. A refusal reads `<error>`; a missing attribute reads
# `<absent>`, tested with `?` first, so an uncatchable abort on a direct read is a value here and not a dead file.
{ gm, np }:
let
  inherit (builtins)
    tryEval
    deepSeq
    attrNames
    isFunction
    length
    ;
  safe =
    v:
    let
      r = tryEval (deepSeq v v);
    in
    if r.success then r.value else "<error>";
  rd =
    r: n: f:
    let
      h = tryEval (r ? ${n});
    in
    if !h.success then
      "<error>"
    else if !h.value then
      "<absent>"
    else
      safe (f r.${n});

  base = L: {
    options.a = L.mkOption {
      type = L.types.int;
      default = 1;
    };
  };
  states = {
    clean = L: [ (base L) ];
    stray = L: [
      (base L)
      { config.bogus = 1; }
    ];
    strayDeep = L: [
      (base L)
      { options.g.x = L.mkOption { default = 0; }; }
      { config.g.y = 1; }
    ];
    lax = L: [
      (base L)
      { config.bogus = 1; }
      { config._module.check = false; }
    ];
    ff = L: [
      (base L)
      { freeformType = L.types.attrsOf L.types.int; }
      { config.bogus = 1; }
    ];
    checkConflict = L: [
      (base L)
      { config._module.check = L.mkForce true; }
      { config._module.check = L.mkForce false; }
    ];
    checkType = L: [
      (base L)
      { config._module.check = "yes"; }
    ];
    checkThrow = L: [
      (base L)
      { config._module.check = throw "planted"; }
    ];
    ffConflict = L: [
      (base L)
      { config._module.freeformType = L.mkForce (L.types.attrsOf L.types.int); }
      { config._module.freeformType = L.mkForce (L.types.attrsOf L.types.str); }
    ];
    ffThrow = L: [
      (base L)
      { config._module.freeformType = throw "planted"; }
    ];
    laxFfThrow = L: [
      (base L)
      { config._module.check = false; }
      { config._module.freeformType = throw "planted"; }
    ];
  };
  reads = L: r: {
    optNames = rd r "options" attrNames;
    optAValue = rd r "options" (o: o.a.value);
    optAType = rd r "options" (o: o.a.type.name);
    optADecls = rd r "options" (o: length o.a.declarations);
    optADefs = rd r "options" (o: o.a.definitions);
    optAIsDefined = rd r "options" (o: o.a.isDefined);
    optModCheck = rd r "options" (o: o._module.check.value);
    cfgNames = rd r "config" attrNames;
    cfgA = rd r "config" (c: c.a);
    modNames = rd r "_module" attrNames;
    modCheck = rd r "_module" (m: m.check);
    modArgs = rd r "_module" (m: attrNames m.args);
    typeName = rd r "type" (t: t.name);
    typeSub = rd r "type" (t: attrNames (t.getSubOptions [ ]));
    typeDesc = rd r "type" (t: t.description);
    typeNestedFf = rd r "type" (
      t: if t.nestedTypes ? freeformType then t.nestedTypes.freeformType.name else "none"
    );
    typeFfOpts = rd r "type" (t: attrNames ((t.getSubOptions [ "p" ])._freeformOptions or { }));
    extIsFn = rd r "extendModules" isFunction;
    extLaxCfgA = rd r "extendModules" (
      x: (x { modules = [ { config._module.check = L.mkForce false; } ]; }).config.a
    );
    graphLen = rd r "graph" length;
    cls = rd r "class" (c: c);
    tag = rd r "_type" (t: t);
  };

  inner = L: {
    options.x = L.mkOption {
      type = L.types.int;
      default = 1;
    };
  };
  nestedStates = {
    clean = {
      tm = L: [ (inner L) ];
      def = { };
    };
    defStray = {
      tm = L: [ (inner L) ];
      def = {
        bogus = 1;
      };
    };
    tmStray = {
      tm = L: [
        (inner L)
        { config.bogus = 1; }
      ];
      def = { };
    };
    tmLax = {
      tm = L: [
        (inner L)
        { config.bogus = 1; }
        { config._module.check = false; }
      ];
      def = { };
    };
    tmForce = {
      tm = L: [
        (inner L)
        { config._module.check = L.mkForce true; }
      ];
      def = { };
    };
    tmCheckThrow = {
      tm = L: [
        (inner L)
        { config._module.check = throw "planted"; }
      ];
      def = { };
    };
    tmFfThrow = {
      tm = L: [
        (inner L)
        { config._module.freeformType = throw "planted"; }
      ];
      def = { };
    };
  };
  nestedReads =
    a: s:
    let
      inherit (a) L;
      T = a.sub (s.tm L);
      r = a.ev [
        {
          options.sub = L.mkOption {
            type = T;
            default = { };
          };
        }
        { config.sub = s.def; }
      ];
      r0 = a.ev [ { options.sub = L.mkOption { type = T; }; } ];
    in
    {
      cfgSubX = safe r.config.sub.x;
      optSubValue = safe r.options.sub.value.x;
      typeDesc = safe T.description;
      typeNestedFf = safe (if T.nestedTypes ? freeformType then T.nestedTypes.freeformType else "none");
      typeSubOpts = safe (attrNames (T.getSubOptions [ "p" ]));
      emptyValue = safe (attrNames (T.emptyValue.value or { }));
      outerOptNames = safe (attrNames r0.options);
    };

  arms = {
    np = {
      L = np;
      ev = ms: np.evalModules { modules = ms; };
      sub =
        tm:
        np.types.submoduleWith {
          modules = tm;
          shorthandOnlyDefinesConfig = true;
        };
    };
    gm = {
      L = gm;
      ev = ms: gm.evalModuleTree { } ms;
      sub = tm: gm.types.submodule tm;
    };
  };
in
{
  result = builtins.mapAttrs (_: a: builtins.mapAttrs (_: s: reads a.L (a.ev (s a.L))) states) arms;
  nested = builtins.mapAttrs (_: a: builtins.mapAttrs (_: nestedReads a) nestedStates) arms;
}
