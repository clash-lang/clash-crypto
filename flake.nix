{
  description = "A flake enabling tooling for clash-crypto";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    clash-compiler.url = "github:clash-lang/clash-compiler/dd/nix-update";
    ecpprog.url = "github:diegodiv/ecpprog";
  };
  outputs = { self, nixpkgs, flake-utils, clash-compiler, ecpprog, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = clash-compiler.inputs.nixpkgs.legacyPackages.${system};
          serialportSrc = pkgs.fetchFromGitHub {
            owner = "standardsemiconductor";
            repo = "serialport";
            rev = "ce42a5afebb55d2e2e84be7f5386d69c343e3942";
            sha256 = "sha256-oBG8DylFwzUu212AiNOg2x+D1jmI2hAvMJQT0F8wWlE=";
          };
          inherit (pkgs.haskell.lib) dontCheck doJailbreak markUnbroken;
          overlay = final: prev: {
            clash-cores = clash-compiler.packages.${system}.clash-cores;
            clash-prelude = clash-compiler.packages.${system}.clash-prelude;
            clash-prelude-hedgehog = clash-compiler.packages.${system}.clash-prelude-hedgehog;
            clash-lib = clash-compiler.packages.${system}.clash-lib;
            clash-ghc = clash-compiler.packages.${system}.clash-ghc;
            cabal-install = nixpkgs.legacyPackages.${system}.cabal-install;
            serialport = dontCheck (doJailbreak (prev.callCabal2nix "serialport" serialportSrc { }));
            # Otherwise fails on `template-haskell < 2.22`.
            string-interpolate = doJailbreak (prev.string-interpolate);
            typelits-witnesses = markUnbroken prev.typelits-witnesses;
          };
          # TODO: refer dynamically to the right ghc version (using clash-compiler's default).
          # Might require some changes on clash-compiler's flake.
          myHsPkgs = (pkgs.haskell.packages.ghc910.extend overlay).extend
            (pkgs.haskell.lib.compose.packageSourceOverrides {
              clash-crypto = ./.;
            });
      in
      {
        devShells.default = myHsPkgs.shellFor {
          name = "ghc910";
          packages = p: [ p.clash-crypto ];
          inputsFrom = [
            clash-compiler.packages.${system}.clash-lib.env
            clash-compiler.packages.${system}.clash-ghc.env
          ];
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
        default = myHsPkgs.clash-crypto;
      });
}
