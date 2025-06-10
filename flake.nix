{
  description = "A flake enabling tooling for clash-crypto";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    ecpprog.url = "github:diegodiv/ecpprog";
  };
  outputs = { self, nixpkgs, flake-utils, ecpprog, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
          serialportSrc = pkgs.fetchFromGitHub {
            owner = "standardsemiconductor";
            repo = "serialport";
            rev = "ce42a5afebb55d2e2e84be7f5386d69c343e3942";
            sha256 = "sha256-oBG8DylFwzUu212AiNOg2x+D1jmI2hAvMJQT0F8wWlE=";
          };
          clashProtocolsSrc = pkgs.fetchFromGitHub {
            owner = "clash-lang";
            repo = "clash-protocols";
            rev = "ba433847cfa2d7d5d241f123520a104ddfc6d72c";
            sha256 = "sha256-qqR4kZ1OwTcx/XnPJf3k1RupehYakks5Lcw2uR1ejmU=";
          };
          clashCompilerSrc = pkgs.fetchFromGitHub {
            owner = "clash-lang";
            repo = "clash-compiler";
            rev = "462de2c8ae81eb525ad0df04a69ac73384baa309";
            sha256 = "sha256-P/7iDg+35Bz4KwyixcAgPpmx71TfpommpuvOiyZ3T9Q=";
          };

          inherit (pkgs.haskell.lib) dontCheck doJailbreak markUnbroken;
          overlay = final: prev: {
            clash-protocols = doJailbreak (prev.callCabal2nix "clash-protocols"
              (clashProtocolsSrc + "/clash-protocols") { });
            clash-protocols-base = prev.callCabal2nix "clash-protocols-base"
              (clashProtocolsSrc + "/clash-protocols-base") { };
            clash-prelude = prev.callCabal2nix "clash-prelude"
              (clashCompilerSrc + "/clash-prelude") { };
            clash-prelude-hedgehog = prev.callCabal2nix "clash-prelude-hedgehog"
              (clashCompilerSrc + "/clash-prelude-hedgehog") { };
            clash-lib = prev.callCabal2nix "clash-lib"
              (clashCompilerSrc + "/clash-lib") { };
            clash-ghc = prev.callCabal2nix "clash-ghc"
              (clashCompilerSrc + "/clash-ghc") { };
            # Otherwise fails on `template-haskell < 2.22`.
            serialport = dontCheck (prev.callCabal2nix "serialport" serialportSrc { });
            clash-crypto = final.callCabal2nix "clash-crypto" ./. { };
          };
          myHsPkgs = pkgs.haskell.packages.ghc910.extend overlay;
      in
      {
        devShells.default = myHsPkgs.shellFor {
          name = "ghc910";
          packages = p: [ p.clash-crypto ];
          inputsFrom = [];
          nativeBuildInputs =
            with pkgs; [
              gnumake yosys nextpnr trellis
            ] ++
            (with myHsPkgs; [ cabal-install ])
            ++ [ecpprog.defaultPackage.${system}]
          ;
          shellHook = ''
            SHAKEPATH=`cabal list-bin clash-crypto:shake`
            export PATH="$(dirname $SHAKEPATH):$PATH:$(dirname $SHAKEPATH)"
          '';
        };
        packages.default = dontCheck myHsPkgs.clash-crypto;
      });
}
