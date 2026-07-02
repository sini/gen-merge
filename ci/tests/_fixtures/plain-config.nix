# Engine-agnostic, config-only module — a BARE path leaf both engines import identically.
# No constructors (no `mkOption`/`types`): just contributes `config.value`, so an inline module
# using the `P` param pack DECLARES the option while this file stays ctor-free. This is the
# minimal exercise of `callM`'s path branch (path leaf + path-in-`imports`), the enabler for a
# downstream consumer loading a module tree from `(import-tree ./dir).files` (a bare path list).
{ config.value = 42; }
