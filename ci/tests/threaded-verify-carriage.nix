# A `verify` is read on the settled value through a threaded nixpkgs wrapper and at the meet, never per definition
# (den-hoag-x7qe5; owner Ruling 8, ADR-0039). These are the served cells: a value the verify admits is nixpkgs' own
# value, on gen's engine and, where gen's door code runs inside it, on nixpkgs' (`twin` is nixpkgs over its own
# types). The refusals are on the error plane (`../tests-error.nix`, `threaded-verify-carriage`), and the shapes are
# `./_fixtures/threaded-verify-carriage.nix`. RED before the landing: `listMirror`, `uniqDefineMember` and
# `rawThirdMember` (a per-definition reading of a merged-value verify refused or aborted where nixpkgs serves).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  fx = import ./_fixtures/threaded-verify-carriage.nix {
    gm = genMerge;
    nl = nixpkgsLib;
  };
  read =
    engine: name:
    let
      o = builtins.tryEval (fx.run engine name);
    in
    if o.success then o.value else "REFUSED";
  served = engine: name: {
    value = read engine name;
    twin = read engine name == read "twin" name;
  };
in
{
  flake.tests.threaded-verify-carriage = {
    # np.uniq over a raw copy: an admitted value is served, and reading one member forces no other
    test-a-threaded-copy-serves-an-admitted-value = {
      expr = {
        ok = served "gen" "uniqCopyOk";
        lazy = (fx.config "gen" "uniqCopyLazy").x.a;
      };
      expected = {
        ok = {
          value = {
            a = 1;
            b = 0;
          };
          twin = true;
        };
        lazy = 1;
      };
    };
    # the mkOptionType door over a both-copy, met with a plain declaration: an admitted value is served
    test-a-met-door-copy-serves-an-admitted-value = {
      expr = served "gen" "doorBothOk";
      expected = {
        value.k = {
          a = 1;
          b = 0;
        };
        twin = true;
      };
    };
    # a verify reading the merged value is not read per definition: two one-element lists meet a verify wanting two
    test-a-merged-value-verify-is-not-read-per-definition = {
      expr = {
        gen = served "gen" "listMirror";
        np = served "np" "listMirror";
      };
      expected = {
        gen = {
          value.k = [
            2
            1
          ];
          twin = true;
        };
        np = {
          value.k = [
            2
            1
          ];
          twin = true;
        };
      };
    };
    # a member-reading verify: through defineType under np.uniq, and a raw copy third of three
    test-a-member-reading-verify-serves-an-admitted-value = {
      expr = {
        defineGen = served "gen" "uniqDefineMember";
        defineNp = served "np" "uniqDefineMember";
        rawGen = served "gen" "rawThirdMember";
        rawNp = served "np" "rawThirdMember";
      };
      expected =
        let
          v = {
            a = 1;
            b = 0;
          };
        in
        {
          defineGen = {
            value = v;
            twin = true;
          };
          defineNp = {
            value = v;
            twin = true;
          };
          rawGen = {
            value.k = v;
            twin = true;
          };
          rawNp = {
            value.k = v;
            twin = true;
          };
        };
    };
    # the wrapper's own check, over a threaded copy and over the wrapper the in-place close rebuilds: admitted
    test-a-wrapper-check-over-a-threaded-copy-serves-an-admitted-value = {
      expr = {
        check = served "gen" "checkOverUniqCopyOk";
        uniq = served "gen" "uniqCheckOverUniqCopyOk";
      };
      expected = {
        check = {
          value = {
            a = 1;
            b = 0;
          };
          twin = true;
        };
        uniq = {
          value = {
            a = 1;
            b = 0;
          };
          twin = true;
        };
      };
    };
    # door copies declared last of four, and a door copy below two threaded np.uniq: admitted, on both engines
    test-door-copies-declared-last-serve-an-admitted-value = {
      expr = {
        lastGen = served "gen" "twoDoorCopiesLastOk";
        lastNp = served "np" "twoDoorCopiesLastOk";
        uniqUniqGen = served "gen" "uniqUniqDoorCopyThirdOk";
        uniqUniqNp = served "np" "uniqUniqDoorCopyThirdOk";
      };
      expected =
        let
          v = {
            value = {
              a = 1;
              b = 0;
            };
            twin = true;
          };
        in
        {
          lastGen = v;
          lastNp = v;
          uniqUniqGen = v;
          uniqUniqNp = v;
        };
    };
  };
}
