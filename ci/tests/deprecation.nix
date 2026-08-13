# The deprecation report — `evalModuleTree`'s result gains a lazy `deprecations` attr naming every
# declared option whose TYPE carries a `deprecationMessage`.
#
# WHY: `deprecationMessage` is one of the 14 protocol fields lib/types.nix stamps onto every completed
# type, and it was the one field the engine stored and never consulted. A stored field nobody reads is
# not a neutral placeholder — it makes a conformance check that asserts PRESENCE pass while the
# BEHAVIOUR the field exists for is absent, so a deprecated type declared here was indistinguishable
# from an undeprecated one. The reference engine's answer (nixpkgs `warnDeprecation`) reports the
# type's name, the option loc and the declaring files; those are the data these records carry.
#
# ON THE RESULT, NOT ON STDERR, on mechanism: Nix's eval cache swallows `trace`/`warn`, so a printed
# deprecation shows up once and never again — a report that vanishes when the answer is reused reports
# nothing. Every cell below reads a FIELD, which is why they are ordinary suite cells at all.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption;
  t = gm.types;

  deprecatedType = gm.mkOptionType {
    name = "depA";
    check = _: true;
    deprecationMessage = "use `plainA' instead";
  };
  # The armed control's type: same surface, same construction, no deprecation.
  plainType = gm.mkOptionType {
    name = "plainA";
    check = _: true;
  };

  # One declared option `d` of the given type, declared in `DECL.nix`.
  reportFor =
    ty:
    (evalModuleTree {
      modules = [
        {
          _file = "DECL.nix";
          options.d = mkOption {
            type = ty;
            default = 1;
          };
        }
      ];
    }).deprecations;
in
{
  flake.tests.deprecation = {
    # 1 — the oracle AND its armed control in ONE cell, so the control cannot be dropped while the
    # claim stays: the deprecated type is reported with its message, its option path and its type
    # NAME; the non-deprecated type on the same surface reports NOTHING. Without the second arm this
    # cell would pass for a report that fires on every declared option.
    test-deprecated-type-reported-with-message-path-and-type-name = {
      expr = {
        deprecated = reportFor deprecatedType;
        nonDeprecated = reportFor plainType;
      };
      expected = {
        deprecated = [
          {
            path = [ "d" ];
            type = "depA";
            message = "use `plainA' instead";
            declarations = [ "DECL.nix" ];
          }
        ];
        nonDeprecated = [ ];
      };
    };

    # 2 — the loc is the one a refusal would name: absolute against `prefix`, and multi-segment for a
    # leaf declared inside option GROUPS (the decl tree is walked, not just its top level).
    test-path-is-absolute-against-prefix-and-multi-segment = {
      expr =
        (evalModuleTree {
          prefix = [ "sub" ];
          modules = [
            {
              _file = "P.nix";
              options.a.b.d = mkOption {
                type = deprecatedType;
                default = 1;
              };
            }
          ];
        }).deprecations;
      expected = [
        {
          path = [
            "sub"
            "a"
            "b"
            "d"
          ];
          type = "depA";
          message = "use `plainA' instead";
          declarations = [ "P.nix" ];
        }
      ];
    };

    # 3 — a deprecation is fixed at the DECLARATION, so the record names every module that declared the
    # option, in authored order — not just whichever one supplied the type. The second module here is
    # gen-schema's ref-binding shape (an `apply` layer carrying no `type` of its own), which is exactly
    # the case where "the file that declared the type" and "the files that declare the option" differ.
    test-record-names-every-declaring-site = {
      expr =
        (evalModuleTree {
          modules = [
            {
              _file = "A.nix";
              options.grp.d = mkOption {
                type = deprecatedType;
                default = 1;
              };
            }
            {
              _file = "B.nix";
              options.grp.d = mkOption { apply = x: x; };
            }
          ];
        }).deprecations;
      expected = [
        {
          path = [
            "grp"
            "d"
          ];
          type = "depA";
          message = "use `plainA' instead";
          declarations = [
            "A.nix"
            "B.nix"
          ];
        }
      ];
    };

    # 4 — an option declared with NO type at all does not abort the walk and reports nothing. Live
    # control in the same cell: a deprecated option beside it is still reported, so this cell cannot
    # pass by the report having failed silently.
    test-untyped-declaration-reports-nothing = {
      expr =
        (evalModuleTree {
          modules = [
            {
              _file = "U.nix";
              options.untyped = mkOption { default = 1; };
              options.d = mkOption {
                type = deprecatedType;
                default = 1;
              };
            }
          ];
        }).deprecations;
      expected = [
        {
          path = [ "d" ];
          type = "depA";
          message = "use `plainA' instead";
          declarations = [ "U.nix" ];
        }
      ];
    };

    # 5 — reading the report forces DECLARATIONS, never DEFINITIONS: it reads each declared leaf's
    # type, where the field lives, and no def value. The bomb is live — the control forces `config`
    # on the same eval and does abort.
    test-report-does-not-force-definition-values = {
      expr =
        let
          r = evalModuleTree {
            modules = [
              {
                _file = "D.nix";
                options.d = mkOption { type = deprecatedType; };
              }
              {
                _file = "V.nix";
                config.d = throw "BOOM";
              }
            ];
          };
          forced = x: (builtins.tryEval (builtins.deepSeq x null)).success;
        in
        {
          reportOk = forced r.deprecations;
          configAborts = forced r.config;
        };
      expected = {
        reportOk = true;
        configAborts = false;
      };
    };

    # 6 — the report is a SIBLING of `config` and changes nothing about it: declaring a deprecated type
    # neither grows a key nor perturbs a byte of the merged value.
    test-report-stays-out-of-config = {
      expr =
        let
          r = evalModuleTree {
            modules = [
              {
                _file = "C.nix";
                options.d = mkOption {
                  type = deprecatedType;
                  default = 1;
                };
              }
            ];
          };
        in
        {
          keys = builtins.attrNames r.config;
          json = builtins.toJSON r.config;
        };
      expected = {
        keys = [ "d" ];
        json = "{\"d\":1}";
      };
    };

    # 7 — the record carries the type's NAME, not the type VALUE, and that is what makes the report
    # something a consumer can print, diff or hand on: it survives a JSON round trip unchanged. Live
    # control in the same cell — the type value carries functions, so a record holding one could not
    # be serialised at all (`toJSON` on a function is not even catchable by `tryEval`, which is why
    # this control asserts the function's presence rather than the failure).
    test-report-round-trips-through-json = {
      expr = {
        roundTripped = builtins.fromJSON (builtins.toJSON (reportFor deprecatedType));
        typeValueCarriesFunctions = builtins.isFunction deprecatedType.merge;
      };
      expected = {
        roundTripped = [
          {
            path = [ "d" ];
            type = "depA";
            message = "use `plainA' instead";
            declarations = [ "DECL.nix" ];
          }
        ];
        typeValueCarriesFunctions = true;
      };
    };

    # 8 — SCOPE, one eval, asserted so the boundary is a decision rather than an accident. A
    # `submodule`'s inner options are declared in a NESTED `evalModuleTree` that runs INSIDE the
    # type's `merge`, and `merge` returns the merged VALUE — byte-compat pins that shape, so the
    # nested eval cannot hand its report back alongside the value it was called for. That is the
    # whole of the boundary: the nested view is NOT unreachable. The live control in this cell is the
    # re-derivation the protocol already allows — `getSubModules` are the sub-modules, so evaluating
    # them as their own tree yields the nested records with `merge` never entered. It reports
    # `declarations = [ "<gen-merge>" ]` because sub-modules carry no `_file`, which is the reason
    # the parent does not fold this view into its own report rather than a reason it could not.
    test-scope-is-this-eval-not-nested-ones = {
      expr =
        let
          subTy = t.submodule {
            options.inner = mkOption {
              type = deprecatedType;
              default = 1;
            };
          };
        in
        {
          throughSubmodule =
            (evalModuleTree {
              modules = [
                {
                  _file = "S.nix";
                  options.s = mkOption {
                    type = subTy;
                    default = { };
                  };
                }
              ];
            }).deprecations;
          reDerivedFromTheDeclarationStratum =
            (evalModuleTree {
              prefix = [ "s" ];
              modules = subTy.getSubModules;
            }).deprecations;
        };
      expected = {
        throughSubmodule = [ ];
        reDerivedFromTheDeclarationStratum = [
          {
            path = [
              "s"
              "inner"
            ];
            type = "depA";
            message = "use `plainA' instead";
            declarations = [ "<gen-merge>" ];
          }
        ];
      };
    };

    # 9 — the report reads the PROTOCOL field, so a NIXPKGS type declared inside gen-merge is reported
    # by the same rule as a gen-merge one. This is the field's whole point: `deprecationMessage` means
    # the same thing on both sides of the protocol, and the engine that stores it is now the engine
    # that reads it, whichever library minted the type.
    test-a-nixpkgs-type-carrying-a-deprecation-is-reported = {
      expr =
        (evalModuleTree {
          modules = [
            {
              _file = "N.nix";
              options.d = mkOption {
                type = nixpkgsLib.mkOptionType {
                  name = "depNp";
                  check = _: true;
                  deprecationMessage = "a nixpkgs-minted deprecation";
                };
                default = 1;
              };
            }
          ];
        }).deprecations;
      expected = [
        {
          path = [ "d" ];
          type = "depNp";
          message = "a nixpkgs-minted deprecation";
          declarations = [ "N.nix" ];
        }
      ];
    };
  };
}
