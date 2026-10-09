# A record carrying a module set in gen's spelling never has that set evaluated by the import door
# (den-hoag-60hql; `evaluatesOwnRoles`, the gen recogniser beside the rider's).
#
# A gen submodule states `nestedTypes` as its own module set evaluated with no definitions, and
# gen-merge's import of a nixpkgs submodule keeps the same field as `unroledNested`. A copy of either
# re-entering `mkOptionType` (gen-schema's `refined`, a `//` wrapper, a second door) used to read that
# field to learn its roles, which evaluates the set; a set that reads back into the registry being
# built then recursed uncatchably. The laziness is asserted as a property: the module set is POISONED
# and forcing each record to WHNF still succeeds. The controls are the routes that never crossed the
# door twice.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  np = nixpkgsLib.types;
  inherit (builtins)
    attrNames
    deepSeq
    removeAttrs
    seq
    tryEval
    ;
  P = {
    imports = throw "gen-module-set-laziness: module set evaluated 4c1d9e07";
  };
  sub = gm.types.submodule P;
  nsub = np.submodule P;
  ok = x: (tryEval (seq x true)).success;
  roles =
    x:
    let
      v = attrNames (x.carries or { });
      e = tryEval (deepSeq v v);
    in
    if e.success then e.value else "refused";
  # a gen nesting record copied the way a wrapper copies it, re-entering the door
  copyOf =
    s:
    gm.mkOptionType (
      removeAttrs s [
        "functor"
        "typeMerge"
        "__mint"
        "__okAt"
        "__payload"
        "__sealed"
        "__typeSelf"
      ]
      // {
        name = "copy";
      }
    );
  # a hand-built record claiming gen's carrying spelling
  forged =
    extra:
    {
      name = "forged";
      check = _: true;
      merge = _loc: defs: (builtins.head defs).value;
      nests = { };
      functor = {
        name = "forged";
        type = _: null;
        payload = null;
        binOp = _: _: null;
      };
    }
    // extra;
  withSubProtocol = forged {
    carries.moduleSet = [ ];
    getSubOptions = _: { };
    getSubModules = [ ];
    substSubModules = _: withSubProtocol;
  };
in
{
  flake.tests.gen-module-set-laziness = {
    test-the-door-never-evaluates-a-carried-module-set = {
      expr = {
        doorSub = ok (gm.mkOptionType sub);
        doorCopy = ok (copyOf sub);
        doorDoor = ok (gm.mkOptionType (gm.mkOptionType sub));
        doorDoorNixSub = ok (gm.mkOptionType (gm.mkOptionType nsub));
        withArgs = ok (gm.mkOptionType (sub.withArgs { x = 1; }));
      };
      expected = {
        doorSub = true;
        doorCopy = true;
        doorDoor = true;
        doorDoorNixSub = true;
        withArgs = true;
      };
    };
    # the routes that cross the door once, or not at all, never evaluated it; nor did a door over
    # `evalModuleTree`'s `.type`
    test-the-single-crossings-never-did = {
      expr = {
        sub = ok sub;
        evalTreeType = ok (
          gm.mkOptionType (gm.evalModuleTree { } [ { options.x = gm.mkOption { type = sub; }; } ]).type
        );
        attrsOfSub = ok (gm.types.attrsOf sub);
        doorNixSub = ok (gm.mkOptionType nsub);
      };
      expected = {
        sub = true;
        attrsOfSub = true;
        doorNixSub = true;
        evalTreeType = true;
      };
    };
    # the role read without the evaluation is the one the evaluation gave
    test-the-role-is-the-carried-module-set = {
      expr = {
        doorSub = roles (gm.mkOptionType sub);
        doorCopy = roles (copyOf sub);
        doorDoorNixSub = roles (gm.mkOptionType (gm.mkOptionType nsub));
      };
      expected = {
        doorSub = [ "moduleSet" ];
        doorCopy = [ "moduleSet" ];
        doorDoorNixSub = [ "moduleSet" ];
      };
    };

    # ★ THE STATED RESIDUE, pinned so a change to it is a red cell (`evaluatesOwnRoles`' comment). A
    # forged record stating `carries.moduleSet` is served as a module set: a throwing `nestedTypes` is
    # never read, a static `nestedTypes.elemType` role is unread, and a record stating NO sub-protocol,
    # with a function as its module set, refused by name before as a carrier missing
    # `getSubModules`, is served with that function crossing unvalidated.
    test-a-forged-gen-module-set-record-is-served = {
      expr = {
        throwNested = roles (gm.mkOptionType (withSubProtocol // { nestedTypes = throw "forged"; }));
        staticRole = roles (gm.mkOptionType (withSubProtocol // { nestedTypes.elemType = gm.types.str; }));
        noSubProtocol = roles (
          gm.mkOptionType (forged {
            carries.moduleSet = _: [ ];
            nestedTypes.elemType = gm.types.str;
          })
        );
      };
      expected = {
        throwNested = [ "moduleSet" ];
        staticRole = [ "moduleSet" ];
        noSubProtocol = [ "moduleSet" ];
      };
    };
  };
}
