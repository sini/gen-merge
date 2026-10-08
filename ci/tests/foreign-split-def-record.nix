# A FOREIGN MERGE BELOW A THREADED SPLIT IS HANDED NIXPKGS' `{ file; value; }` (den-hoag-j5gfg;
# ADR-0039's serve half, ADR-0025 item 1, ADR-0034). When a foreign container's chain is threaded
# (a step-free foreign wrapper such as `coercedTo`, or an overridden record) the split's foreign merge
# receives the definition records nixpkgs hands it, so a merge reading `file` (order, coercion,
# attribute name, equality, type, keys) serves nixpkgs' value. A definition that merge built has no
# declaration address: a `nests.declAt` read on it is refused by name, catchably
# (`tests-error.nix` `foreign-split-def-record` holds the message), while gen's own `listOf` keeps its
# addresses. Every `expected` below is nixpkgs' `evalModules` value for the same modules. Fixtures:
# `_fixtures/foreign-split-def-record.nix`.
{ genMerge, nixpkgsLib, ... }:
let
  fx = import ./_fixtures/foreign-split-def-record.nix { inherit genMerge nixpkgsLib; };
in
{
  # G1: a merge reading its definitions' `file`, at every position the chain is reached from.
  flake.tests.foreign-split-reads-file = {
    test-reads-top-obs = {
      expr = fx.readFiles "top" "obs" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 2;
            string = 0;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 1;
            string = 0;
          };
        }
      ];
    };
    test-reads-top-sort = {
      expr = fx.readFiles "top" "sort" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-top-cmp = {
      expr = fx.readFiles "top" "cmp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "ne"
          ];
          leaves = {
            j = 2;
            ne = 0;
          };
        }
        {
          a = 1;
          keys = [
            "eq"
            "j"
          ];
          leaves = {
            eq = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-top-str = {
      expr = fx.readFiles "top" "str" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-top-dk = {
      expr = fx.readFiles "top" "dk" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-top-grp = {
      expr = fx.readFiles "top" "grp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-top-identity-control = {
      expr = fx.readFiles "top" "obs" "nid";
      expected = [
        {
          a = 2;
          keys = [ "j" ];
          leaves = {
            j = 2;
          };
        }
        {
          a = 1;
          keys = [ "j" ];
          leaves = {
            j = 1;
          };
        }
      ];
    };
    test-reads-gatt-obs = {
      expr = fx.readFiles "gatt" "obs" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 2;
            string = 0;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 1;
            string = 0;
          };
        }
      ];
    };
    test-reads-gatt-sort = {
      expr = fx.readFiles "gatt" "sort" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-gatt-cmp = {
      expr = fx.readFiles "gatt" "cmp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "ne"
          ];
          leaves = {
            j = 2;
            ne = 0;
          };
        }
        {
          a = 1;
          keys = [
            "eq"
            "j"
          ];
          leaves = {
            eq = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-gatt-str = {
      expr = fx.readFiles "gatt" "str" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-gatt-dk = {
      expr = fx.readFiles "gatt" "dk" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-gatt-grp = {
      expr = fx.readFiles "gatt" "grp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-gatt-identity-control = {
      expr = fx.readFiles "gatt" "obs" "nid";
      expected = [
        {
          a = 2;
          keys = [ "j" ];
          leaves = {
            j = 2;
          };
        }
        {
          a = 1;
          keys = [ "j" ];
          leaves = {
            j = 1;
          };
        }
      ];
    };
    test-reads-natt-obs = {
      expr = fx.readFiles "natt" "obs" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 2;
            string = 0;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 1;
            string = 0;
          };
        }
      ];
    };
    test-reads-natt-sort = {
      expr = fx.readFiles "natt" "sort" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-natt-cmp = {
      expr = fx.readFiles "natt" "cmp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "ne"
          ];
          leaves = {
            j = 2;
            ne = 0;
          };
        }
        {
          a = 1;
          keys = [
            "eq"
            "j"
          ];
          leaves = {
            eq = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-natt-str = {
      expr = fx.readFiles "natt" "str" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-natt-dk = {
      expr = fx.readFiles "natt" "dk" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-natt-grp = {
      expr = fx.readFiles "natt" "grp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-natt-identity-control = {
      expr = fx.readFiles "natt" "obs" "nid";
      expected = [
        {
          a = 2;
          keys = [ "j" ];
          leaves = {
            j = 2;
          };
        }
        {
          a = 1;
          keys = [ "j" ];
          leaves = {
            j = 1;
          };
        }
      ];
    };
    test-reads-nlst-obs = {
      expr = fx.readFiles "nlst" "obs" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 2;
            string = 0;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 1;
            string = 0;
          };
        }
      ];
    };
    test-reads-nlst-sort = {
      expr = fx.readFiles "nlst" "sort" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-nlst-cmp = {
      expr = fx.readFiles "nlst" "cmp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "ne"
          ];
          leaves = {
            j = 2;
            ne = 0;
          };
        }
        {
          a = 1;
          keys = [
            "eq"
            "j"
          ];
          leaves = {
            eq = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-nlst-str = {
      expr = fx.readFiles "nlst" "str" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-nlst-dk = {
      expr = fx.readFiles "nlst" "dk" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-nlst-grp = {
      expr = fx.readFiles "nlst" "grp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-nlst-identity-control = {
      expr = fx.readFiles "nlst" "obs" "nid";
      expected = [
        {
          a = 2;
          keys = [ "j" ];
          leaves = {
            j = 2;
          };
        }
        {
          a = 1;
          keys = [ "j" ];
          leaves = {
            j = 1;
          };
        }
      ];
    };
    test-reads-wrap-obs = {
      expr = fx.readFiles "wrap" "obs" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 2;
            string = 0;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 1;
            string = 0;
          };
        }
      ];
    };
    test-reads-wrap-sort = {
      expr = fx.readFiles "wrap" "sort" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-wrap-cmp = {
      expr = fx.readFiles "wrap" "cmp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "ne"
          ];
          leaves = {
            j = 2;
            ne = 0;
          };
        }
        {
          a = 1;
          keys = [
            "eq"
            "j"
          ];
          leaves = {
            eq = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-wrap-str = {
      expr = fx.readFiles "wrap" "str" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-wrap-dk = {
      expr = fx.readFiles "wrap" "dk" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-wrap-grp = {
      expr = fx.readFiles "wrap" "grp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-wrap-identity-control = {
      expr = fx.readFiles "wrap" "obs" "nid";
      expected = [
        {
          a = 2;
          keys = [ "j" ];
          leaves = {
            j = 2;
          };
        }
        {
          a = 1;
          keys = [ "j" ];
          leaves = {
            j = 1;
          };
        }
      ];
    };
    test-reads-nsub-obs = {
      expr = fx.readFiles "nsub" "obs" "nest";
      expected = [
        {
          a = 1;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 1;
            string = 0;
          };
        }
        {
          a = 2;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 2;
            string = 0;
          };
        }
      ];
    };
    test-reads-nsub-sort = {
      expr = fx.readFiles "nsub" "sort" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-nsub-cmp = {
      expr = fx.readFiles "nsub" "cmp" "nest";
      expected = [
        {
          a = 1;
          keys = [
            "eq"
            "j"
          ];
          leaves = {
            eq = 0;
            j = 1;
          };
        }
        {
          a = 2;
          keys = [
            "j"
            "ne"
          ];
          leaves = {
            j = 2;
            ne = 0;
          };
        }
      ];
    };
    test-reads-nsub-str = {
      expr = fx.readFiles "nsub" "str" "nest";
      expected = [
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
      ];
    };
    test-reads-nsub-dk = {
      expr = fx.readFiles "nsub" "dk" "nest";
      expected = [
        {
          a = 1;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 1;
          };
        }
        {
          a = 2;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 2;
          };
        }
      ];
    };
    test-reads-nsub-grp = {
      expr = fx.readFiles "nsub" "grp" "nest";
      expected = [
        {
          a = 1;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 1;
          };
        }
        {
          a = 2;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 2;
          };
        }
      ];
    };
    test-reads-nsub-identity-control = {
      expr = fx.readFiles "nsub" "obs" "nid";
      expected = [
        {
          a = 1;
          keys = [ "j" ];
          leaves = {
            j = 1;
          };
        }
        {
          a = 2;
          keys = [ "j" ];
          leaves = {
            j = 2;
          };
        }
      ];
    };
    test-reads-ffree-obs = {
      expr = fx.readFiles "ffree" "obs" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 2;
            string = 0;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "string"
          ];
          leaves = {
            j = 1;
            string = 0;
          };
        }
      ];
    };
    test-reads-ffree-sort = {
      expr = fx.readFiles "ffree" "sort" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-ffree-cmp = {
      expr = fx.readFiles "ffree" "cmp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "j"
            "ne"
          ];
          leaves = {
            j = 2;
            ne = 0;
          };
        }
        {
          a = 1;
          keys = [
            "eq"
            "j"
          ];
          leaves = {
            eq = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-ffree-str = {
      expr = fx.readFiles "ffree" "str" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "aa"
            "j"
          ];
          leaves = {
            aa = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "j"
            "zz"
          ];
          leaves = {
            j = 1;
            zz = 0;
          };
        }
      ];
    };
    test-reads-ffree-dk = {
      expr = fx.readFiles "ffree" "dk" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "file,value"
            "j"
          ];
          leaves = {
            "file,value" = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-ffree-grp = {
      expr = fx.readFiles "ffree" "grp" "nest";
      expected = [
        {
          a = 2;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 2;
          };
        }
        {
          a = 1;
          keys = [
            "g1"
            "j"
          ];
          leaves = {
            g1 = 0;
            j = 1;
          };
        }
      ];
    };
    test-reads-ffree-identity-control = {
      expr = fx.readFiles "ffree" "obs" "nid";
      expected = [
        {
          a = 2;
          keys = [ "j" ];
          leaves = {
            j = 2;
          };
        }
        {
          a = 1;
          keys = [ "j" ];
          leaves = {
            j = 1;
          };
        }
      ];
    };
  };
  # G2: merges that reorder, filter, group or rewrite the definitions serve nixpkgs' value.
  flake.tests.foreign-split-reordering-merges = {
    test-serves-stock-ab = {
      expr = fx.addresses "nest" "stock" "val" "ab";
      expected = [
        "r"
        "s"
        "q"
        "p"
      ];
    };
    test-serves-stock-ba = {
      expr = fx.addresses "nest" "stock" "val" "ba";
      expected = [
        "p"
        "q"
        "r"
        "s"
      ];
    };
    test-serves-id-ab = {
      expr = fx.addresses "nest" "id" "val" "ab";
      expected = [
        "r"
        "s"
        "q"
        "p"
      ];
    };
    test-serves-id-ba = {
      expr = fx.addresses "nest" "id" "val" "ba";
      expected = [
        "p"
        "q"
        "r"
        "s"
      ];
    };
    test-serves-rev-ab = {
      expr = fx.addresses "nest" "rev" "val" "ab";
      expected = [
        "p"
        "q"
        "s"
        "r"
      ];
    };
    test-serves-rev-ba = {
      expr = fx.addresses "nest" "rev" "val" "ba";
      expected = [
        "s"
        "r"
        "q"
        "p"
      ];
    };
    test-serves-drop-ab = {
      expr = fx.addresses "nest" "drop" "val" "ab";
      expected = [
        "s"
        "q"
        "p"
      ];
    };
    test-serves-drop-ba = {
      expr = fx.addresses "nest" "drop" "val" "ba";
      expected = [
        "q"
        "r"
        "s"
      ];
    };
    test-serves-sortf-ab = {
      expr = fx.addresses "nest" "sortf" "val" "ab";
      expected = [
        "q"
        "r"
        "s"
        "p"
      ];
    };
    test-serves-sortf-ba = {
      expr = fx.addresses "nest" "sortf" "val" "ba";
      expected = [
        "q"
        "p"
        "r"
        "s"
      ];
    };
    test-serves-grp-ab = {
      expr = fx.addresses "nest" "grp" "val" "ab";
      expected = [
        "q"
        "r"
        "s"
        "p"
      ];
    };
    test-serves-grp-ba = {
      expr = fx.addresses "nest" "grp" "val" "ba";
      expected = [
        "q"
        "p"
        "r"
        "s"
      ];
    };
    test-serves-dk-ab = {
      expr = fx.addresses "nest" "dk" "val" "ab";
      expected = [
        "r"
        "s"
        "q"
        "p"
      ];
    };
    test-serves-dk-ba = {
      expr = fx.addresses "nest" "dk" "val" "ba";
      expected = [
        "p"
        "q"
        "r"
        "s"
      ];
    };
    test-serves-nest-fileset-ab = {
      expr = fx.addresses "nest" "fileset" "val" "ab";
      expected = [
        "r"
        "s"
        "q"
        "p"
      ];
    };
    test-serves-nest-fileset-ba = {
      expr = fx.addresses "nest" "fileset" "val" "ba";
      expected = [
        "p"
        "q"
        "r"
        "s"
      ];
    };
    test-serves-wlazy-fileset-ab = {
      expr = fx.addresses "wlazy" "fileset" "val" "ab";
      expected = [
        "p"
        "q"
        "r"
        "s"
      ];
    };
    test-serves-wlazy-fileset-ba = {
      expr = fx.addresses "wlazy" "fileset" "val" "ba";
      expected = [
        "p"
        "q"
        "r"
        "s"
      ];
    };
    test-serves-nest2i-fileset-ab = {
      expr = fx.addresses "nest2i" "fileset" "val" "ab";
      expected = [
        "r"
        "s"
        "q"
        "p"
      ];
    };
    test-serves-nest2i-fileset-ba = {
      expr = fx.addresses "nest2i" "fileset" "val" "ba";
      expected = [
        "p"
        "q"
        "r"
        "s"
      ];
    };
    test-serves-nest2o-fileset-ab = {
      expr = fx.addresses "nest2o" "fileset" "val" "ab";
      expected = [
        "r"
        "s"
        "q"
        "p"
      ];
    };
    test-serves-nest2o-fileset-ba = {
      expr = fx.addresses "nest2o" "fileset" "val" "ba";
      expected = [
        "p"
        "q"
        "r"
        "s"
      ];
    };
  };
  # G3: the declaration address. gen's own `listOf` keeps it in both orders (8hlo3 A6); below a
  # threaded foreign split every definition is built by the foreign merge, and the read is refused
  # catchably, including where the merge writes an attrset `file` of its own (`fileset`) and below a
  # foreign `coercedTo` over gen's own `attrsOf` (`ncogatt`), whose element definitions that wrapper's
  # merge builds.
  flake.tests.foreign-split-declaration-address = {
    test-gen-listof-keeps-addresses = {
      expr = fx.addresses "glist" "stock" "at" "ab";
      expected = [
        [
          "r"
          [
            [
              "kmC"
              "xs"
              "contents"
              0
              0
            ]
          ]
        ]
        [
          "s"
          [
            [
              "kmC"
              "xs"
              "contents"
              1
              0
            ]
          ]
        ]
        [
          "q"
          [
            [
              "kmB"
              "xs"
              0
            ]
          ]
        ]
        [
          "p"
          [
            [
              "kmA"
              "xs"
              0
            ]
          ]
        ]
      ];
    };
    test-gen-listof-keeps-addresses-reordered = {
      expr = fx.addresses "glist" "stock" "at" "ba";
      expected = [
        [
          "p"
          [
            [
              "kmA"
              "xs"
              0
            ]
          ]
        ]
        [
          "q"
          [
            [
              "kmB"
              "xs"
              0
            ]
          ]
        ]
        [
          "r"
          [
            [
              "kmC"
              "xs"
              "contents"
              0
              0
            ]
          ]
        ]
        [
          "s"
          [
            [
              "kmC"
              "xs"
              "contents"
              1
              0
            ]
          ]
        ]
      ];
    };
    test-gen-listof-read-succeeds-control = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "glist" "stock" "atc" "ab");
      expected = [
        true
        true
        true
        true
      ];
    };
    # a reader testing for the attribute sees it, so it refuses rather than falling back to a position
    test-refused-address-is-present = {
      expr = fx.addresses "nest" "stock" "has" "ab";
      expected = [
        [
          "r"
          [ true ]
        ]
        [
          "s"
          [ true ]
        ]
        [
          "q"
          [ true ]
        ]
        [
          "p"
          [ true ]
        ]
      ];
    };
    test-catchable-nest-stock-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest" "stock" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest-stock-ba = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest" "stock" "atc" "ba");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest-rev-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest" "rev" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest-rev-ba = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest" "rev" "atc" "ba");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest-fileset-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest" "fileset" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest-fileset-ba = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest" "fileset" "atc" "ba");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-wlazy-stock-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "wlazy" "stock" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-wlazy-stock-ba = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "wlazy" "stock" "atc" "ba");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-wlazy-rev-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "wlazy" "rev" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-wlazy-rev-ba = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "wlazy" "rev" "atc" "ba");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-wlazy-fileset-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "wlazy" "fileset" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-wlazy-fileset-ba = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "wlazy" "fileset" "atc" "ba");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-ncoatt-stock-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "ncoatt" "stock" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-ncogatt-stock-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "ncogatt" "stock" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest2i-fileset-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest2i" "fileset" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest2i-fileset-ba = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest2i" "fileset" "atc" "ba");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest2o-fileset-ab = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest2o" "fileset" "atc" "ab");
      expected = [
        false
        false
        false
        false
      ];
    };
    test-catchable-nest2o-fileset-ba = {
      expr = map (e: builtins.elemAt e 1) (fx.addresses "nest2o" "fileset" "atc" "ba");
      expected = [
        false
        false
        false
        false
      ];
    };
  };
}
