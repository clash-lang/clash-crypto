{ pkgs }:
pkgs.callPackage
  (import (pkgs.path + "/pkgs/development/compilers/ghc/common-hadrian.nix") {
    version = "10.1";
    rev = "70dc4e611ba6ad79ec51e34363326ec6a62c25de";
    sha256 = "sha256-o4+1dwLa2ObTMn58RnnO6eQ5yuAECZmtYy07ztbUy2s=";
  })
  {
    bootPkgs = pkgs.haskell.packages.ghc9124;
    inherit (pkgs.python3Packages) sphinx;
    inherit (pkgs.darwin) xattr autoSignDarwinBinariesHook;
    llvmPackages = pkgs.llvmPackages_20;
    buildTargetLlvmPackages = pkgs.llvmPackages_20;
  }
