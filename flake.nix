{
  description = "A flake enabling tooling for clash-crypto";
  nixConfig = {
    extra-substituters = [ "https://clash-lang.cachix.org" ];
    extra-trusted-substituters = [ "https://clash-lang.cachix.org" ];
    extra-trusted-public-keys = [ "clash-lang.cachix.org-1:/2N1uka38B/heaOAC+Ztd/EWLmF0RLfizWgC5tamCBg=" ];
  };
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    ecpprog.url = "github:diegodiv/ecpprog";
    ghc-typelits-proof-assist.url = "git+ssh://git@github.com/QBayLogic/ghc-typelits-proof-assist";
  };
  outputs = { nixpkgs, flake-utils, ecpprog, ghc-typelits-proof-assist, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system}.extend (_: prev: {
             yosys = prev.callPackage ./nix/yosys.nix {};
          });

          serialportSrc = pkgs.fetchFromGitHub {
            owner = "standardsemiconductor";
            repo = "serialport";
            rev = "ce42a5afebb55d2e2e84be7f5386d69c343e3942";
            sha256 = "sha256-oBG8DylFwzUu212AiNOg2x+D1jmI2hAvMJQT0F8wWlE=";
          };
          clashCompilerSrc = pkgs.fetchFromGitHub {
            owner = "clash-lang";
            repo = "clash-compiler";
            rev = "d0f65c47fe946699cb7818d24ae16dd8e7aff286";
            sha256 = "sha256-Dt8EkrmRCpLAbrTwdyAqpmM7NaU1Suh9WFAhg5vZx/c=";
          };
          ghcTcpluginApiSrc = pkgs.fetchFromGitHub {
            owner = "sheaf";
            repo = "ghc-tcplugin-api";
            rev = "c583750b5899846cb455f3fe2d58b3ba9bc910d0";
            sha256 = "sha256-3RriTela4iwbvHhF3UigmBOfxJv0+YQGAlXQbnXsX74=";
          };
          ghcTypelitsNatnormaliseSrc = pkgs.fetchFromGitHub {
            owner = "clash-lang";
            repo = "ghc-typelits-natnormalise";
            rev = "a4fdc5bf17f678e74a47bf3b8924c6a35e214fb2";
            sha256 = "sha256-igR4OILxX+WmQapDSTMnEJ/8qVLA9Npf3PmZlcnSIdM=";
          };
          ghcTypelitsKnownnatSrc = pkgs.fetchFromGitHub {
            owner = "clash-lang";
            repo = "ghc-typelits-knownnat";
            rev = "47ed62f90218ecf74246caabbbeaeb22e8be8246";
            sha256 = "sha256-l1rQk8hQ7ywYGkfT9TtRuP4E1SH4n1LioxquHgzf+rY=";
          };
          ghcTypelitsExtraSrc = pkgs.fetchFromGitHub {
            owner = "clash-lang";
            repo = "ghc-typelits-extra";
            rev = "db8cfbd17a8c8984d28c8af254cc81860d8430a9";
            sha256 = "sha256-ynlFGRhTcXwG/fgpIk/GAy+mpvo8eBCptTuRWGl/YC4=";
          };

          inherit (pkgs.haskell.lib) dontCheck doJailbreak;
          overlay = final: prev: {
            clash-prelude = dontCheck (prev.callCabal2nix "clash-prelude"
              (clashCompilerSrc + "/clash-prelude") { });
            clash-prelude-hedgehog = dontCheck (prev.callCabal2nix "clash-prelude-hedgehog"
              (clashCompilerSrc + "/clash-prelude-hedgehog") { });
            clash-lib = dontCheck (prev.callCabal2nix "clash-lib"
              (clashCompilerSrc + "/clash-lib") { });
            clash-ghc = dontCheck (prev.callCabal2nix "clash-ghc"
              (clashCompilerSrc + "/clash-ghc") { });
            serialport = dontCheck (prev.callCabal2nix "serialport" serialportSrc { });
            ghc-tcplugin-api = dontCheck (prev.callCabal2nix "ghc-tcplugin-api" ghcTcpluginApiSrc { });
            ghc-typelits-natnormalise = dontCheck (prev.callCabal2nix "ghc-typelits-natnormalise" ghcTypelitsNatnormaliseSrc { });
            ghc-typelits-knownnat = dontCheck (prev.callCabal2nix "ghc-typelits-knownnat" ghcTypelitsKnownnatSrc { });
            ghc-typelits-extra = dontCheck (prev.callCabal2nix "ghc-typelits-extra" ghcTypelitsExtraSrc { });
            network = dontCheck (prev.callHackage "network" "3.2.7.0" {});
            clash-crypto = final.callCabal2nix "clash-crypto" ./. { };
            ghc-typelits-proof-assist = doJailbreak (dontCheck (prev.callCabal2nix "ghc-typelits-proof-assist" ghc-typelits-proof-assist.outPath { }));
          };
          myHsPkgs = pkgs.haskell.packages.ghc9103.extend overlay;
          defaultDevShell = myHsPkgs.shellFor {
            name = "GHC 9.10.3";
            packages = p: [ p.clash-crypto ];
            shellHook = ''
              SHAKEPATH=`cabal list-bin clash-crypto:shake`
              export PATH="$(dirname $SHAKEPATH):$PATH:$(dirname $SHAKEPATH)"
            '';
            nativeBuildInputs =
              with pkgs; [ gnumake yosys nextpnr trellis ] ++
              (with myHsPkgs; [ cabal-install ]) ++
              [ecpprog.defaultPackage.${system}]
              ;
            };
          opamOverlay = _: prevA: {
            name = prevA.name + " with opam";
            shellHook = prevA.shellHook + ''
              export OCAML_VERSION=${pkgs.ocaml-ng.ocamlPackages_4_09.ocaml.version}
              export OPAMROOT=$(pwd)/.opam-local
              mkdir -p $OPAMROOT

              if [ ! -d "$OPAMROOT/default" ]; then
                opam init --bare --disable-sandboxing --auto-setup
                # Create a switch for the current OCaml version
                opam switch create default $OCAML_VERSION
              fi

              eval $(opam env)
            '';
            nativeBuildInputs = prevA.nativeBuildInputs ++
                    (with pkgs; [ opam gmp pkg-config ]);
          };
          hlsOverlay = _: prevA : {
            name = prevA.name + " with HLS";
            nativeBuildInputs = prevA.nativeBuildInputs ++
                    (with myHsPkgs; [ haskell-language-server ]);
          };
      in
      {
        devShells.default = defaultDevShell;
        devShells.withOpam = defaultDevShell.overrideAttrs opamOverlay;
        devShells.withHLS = defaultDevShell.overrideAttrs hlsOverlay;
        devShells.allFeatures =
          (defaultDevShell.overrideAttrs hlsOverlay).overrideAttrs opamOverlay;
        packages.default = dontCheck myHsPkgs.clash-crypto;
      });
}
