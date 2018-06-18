{ pkgs }:

self: super:

with { inherit (pkgs.stdenv) lib; };

with pkgs.haskell.lib;

{
  primitive = dontBenchmark (dontHaddock (dontCheck (self.callPackage ./deps/primitive.nix {})));

  btree = (
    with rec {
      btreeSource = pkgs.lib.cleanSource ../.;
      btreeBasic = self.callCabal2nix "btree" btreeSource {};
    };
    overrideCabal btreeBasic (old: {
    })
  );
}
