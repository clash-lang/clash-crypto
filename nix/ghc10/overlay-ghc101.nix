{ pkgs }:
final: prev:
let
  inherit (pkgs.haskell.lib) doJailbreak dontCheck markUnbroken overrideCabal;
in
{
  # These build tools do not load target code. Bootstrap them with the stable
  # package set, avoiding a cycle through the alpha's global jailbreak below.
  inherit (pkgs.haskellPackages) jailbreak-cabal hscolour;

  # Hackage bounds generally do not include unreleased GHC boot libraries.
  mkDerivation = args: prev.mkDerivation (args // { jailbreak = true; });

  foldl = dontCheck prev.foldl;
  HTTP = dontCheck prev.HTTP;
  infinite-list = dontCheck prev.infinite-list;
  network = dontCheck prev.network;
  time-compat = dontCheck prev.time-compat;
  th-compat = dontCheck prev.th-compat;
  vector = dontCheck prev.vector;

  constraints-extras = doJailbreak prev.constraints-extras;
  integer-logarithms = doJailbreak prev.integer-logarithms;
  ordered-containers = doJailbreak prev.ordered-containers;
  string-interpolate = doJailbreak prev.string-interpolate;

  # Adapt ghc-paths' custom Setup to the alpha's Cabal verbosity API.
  ghc-paths = overrideCabal prev.ghc-paths (old: {
    postPatch = (old.postPatch or "") + ''
      sed -i '/^import Distribution.Simple.Setup$/a import Distribution.Verbosity (mkVerbosity, defaultVerbosityHandles)' Setup.hs
      substituteInPlace Setup.hs \
        --replace-fail '(fromFlag (configVerbosity flags))' \
          '(mkVerbosity defaultVerbosityHandles (fromFlag (configVerbosity flags)))'
    '';
  });

  # jailbreak-cabal leaves this conditional dependency bound unchanged.
  tagged = overrideCabal prev.tagged (old: {
    postPatch = (old.postPatch or "") + ''
      substituteInPlace tagged.cabal --replace-fail "template-haskell >=2.11 && <2.25" "template-haskell >=2.11 && <2.26"
    '';
  });

  unordered-containers = overrideCabal prev.unordered-containers (old: {
    postPatch = (old.postPatch or "") + ''
      substituteInPlace unordered-containers.cabal --replace-fail "template-haskell >=2.16 && <2.25" "template-haskell >=2.16 && <2.26"
    '';
  });

  # Cabal v3.18.1.0
  Cabal = prev.callCabal2nix "Cabal"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/Cabal") {};


  # cabal-syntax v3.18.1.0
  Cabal-syntax = prev.callCabal2nix "Cabal-syntax"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/Cabal-syntax") {};

  # cabal-install-solver v3.18.1.0
  cabal-install-solver = prev.callCabal2nix "cabal-install-solver"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/cabal-install-solver") {};

  # cabal-install-solver v3.18.1.0
  hooks-exe = prev.callCabal2nix "hooks-exe"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/hooks-exe") {};

  # cabal-install v3.18.1.0
  cabal-install = dontCheck (prev.callCabal2nix "cabal-install"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/cabal-install")
    { Cabal-described = null;
      Cabal-QuickCheck = null;
      Cabal-tests = null;
      Cabal-tree-diff = null;
    });

  # hackage-security v0.6.4.0
  hackage-security = prev.callCabal2nix "hackage-security"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "hackage-security";
      rev = "c7c6fdab06f152a54005843e2e91968d1f34962c";
      hash = "sha256-RH6RkJsGKFvp9EcB+Lw0qT0Mv+iIa6LoxWUksoaNQcg=";
    } + "/hackage-security") {};

  # Waiting for upstream: https://github.com/Lysxia/first-class-families/pull/70
  first-class-families = prev.callCabal2nix "first-class-families"
    (pkgs.fetchFromGitHub {
      owner = "Lysxia";
      repo = "first-class-families";
      rev = "423173d74b5bb7a1fa706f25a1da386ecaeb5acb";
      hash = "sha256-pFKhRfsU8Mcp/834Cid2iH3reqk+W0HNA25uQqNIE/c=";
    }) {};

  # Upstream ghc-10.0 branch.
  hashable = prev.callCabal2nix "hashable"
    (pkgs.fetchFromGitHub {
      owner = "haskell-unordered-containers";
      repo = "hashable";
      rev = "c7202c5a061a46753f2cd0b6bd82a40ee22ee401";
      hash = "sha256-h3HWovVuEVJ9bZ1eRSZs3vH2oRkkReLzjQKQ04ZuSLE=";
    }) {};

  hint =
    let package = prev.callCabal2nix "hint" ( pkgs.fetchFromGitHub {
          owner = "haskell-hint";
          repo = "hint";
          rev = "cfcf1a5fd1663399f77f73a5866ead21536fc406";
          hash = "sha256-nYo72iEEdaUJw+rRQl463m5ixyVUHdfXiIHvgvvV1H4=";
        }) {};
     in dontCheck (package.overrideAttrs (_: _: {
          patches = [ ./patches/hint.patch ];
        }));

  # Waiting for upstream: https://github.com/snoyberg/mono-traversable/pull/262
  mono-traversable = prev.callCabal2nix "mono-traversable"
    (pkgs.fetchFromGitHub {
      owner = "snoyberg";
      repo = "mono-traversable";
      rev = "1b7777a104cd326840e945480bcc954b69ad03c8";
      hash = "sha256-3LAIghFufdku8l2GS8TXd+WkC7Y888At13d5DcidHIA=";
    } + "/mono-traversable") {};

  # Waiting for upstream: https://github.com/recursion-schemes/recursion-schemes/pull/176
  recursion-schemes = prev.callCabal2nix "recursion-schemes"
    (pkgs.fetchFromGitHub {
      owner = "recursion-schemes";
      repo = "recursion-schemes";
      rev = "9f1384f718f07178d65f71786d47ebae4ec66f80";
      hash = "sha256-2EyhWQVYWYwnUiUSESM8J+3mwcVmwkSpY+NSTALHzMo=";
    }) {};

  # Waiting for upstream: https://github.com/mgsloan/th-orphans/pull/43
  th-orphans = prev.callCabal2nix "th-orphans"
    (pkgs.fetchFromGitHub {
      owner = "mgsloan";
      repo = "th-orphans";
      rev = "e2e088696de8b13e758a70c173dc5ff0beff2aeb";
      hash = "sha256-/IuI4PN5Rb8rZ39oHHUFcIbWkzmY8c2mGsY2Th95R8A=";
    }) {};

  # Fix legacy gnu99 restriction
  crypton = overrideCabal prev.crypton {
    postPatch = (prev.crypton.postPatch or "") + ''
      sed -i 's/-std=gnu99/-std=gnu11/g' crypton.cabal
    '';
  };

  # Works around a potential cabal bug (yet to be analyzed)
  checked-literals =
    let
      package = prev.callCabal2nix "checked-literals"
        (pkgs.fetchFromGitHub {
           owner = "clash-lang";
           repo = "checked-literals";
           rev = "20364170430bf06e4ebc9090a43c0322261406d0";
           hash = "sha256-V4WBdC9C9XgPYP4TOlwudGmz12eW3AYUCYJ1TDn8wFQ=";
        }) {};
    in dontCheck (package.overrideAttrs (_: _: {
           patches = [ ./patches/checked-literals.patch ];
        }));
}
