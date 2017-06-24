btree
=====

This library provides in-memory b-trees stored in GHC compact regions
to reduce pressure from the garbage collector. Note that this requires
using GHC 8.2.

For the time being, these are the build instructions:

- Make sure you have GHC 8.2 (release candidate) installed
- `git submodule init && git submodule update`
- `cabal new-build test && ./dist-newstyle/build/btree-0.1.0.0/build/test/test`
- `cabal new-build bench && ./dist-newstyle/build/btree-0.1.0.0/build/bench/bench`

