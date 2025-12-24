# This file takes inspiration from nixpkgs' derivation.
# https://github.com/NixOS/nixpkgs/blob/master/pkgs/by-name/yo/yosys/package.nix

{
  lib,
  stdenv,
  fetchFromGitHub,

  # nativeBuildInputs
  bison,
  flex,
  pkg-config,
  uv,

  # propagatedBuildInputs
  libffi,
  python3,
  readline,
  tcl,
  zlib,

  # tests
  gtkwave,
  iverilog,

  # passthru
  # plugins
  nix-update-script,
  enablePython ? true, # enable python binding
}:

# NOTE: as of late 2020, yosys has switched to an automation robot that
# automatically tags their repository Makefile with a new build number every
# day when changes are committed. please MAKE SURE that the version number in
# the 'version' field exactly matches the YOSYS_VER field in the Yosys
# makefile!
#
# if a change in yosys isn't yet available under a build number like this (i.e.
# it was very recently merged, within an hour), wait a few hours for the
# automation robot to tag the new version, like so:
#
#     https://github.com/YosysHQ/yosys/commit/71ca9a825309635511b64b3ec40e5e5e9b6ad49b
#
# note that while most nix packages for "unstable versions" use a date-based
# version scheme, synchronizing the nix package version here with the unstable
# yosys version number helps users report better bugs upstream, and is
# ultimately less confusing than using dates.

let
  yosysSrc = fetchFromGitHub {
    owner = "YosysHQ";
    repo = "yosys";
    tag = "v0.60";
    hash = "sha256-BVrSq9nWbdu/PIXfwLW7ZkHTz6SrmsqJMSkVa6CsBm8=";
    fetchSubmodules = true;
    leaveDotGit = true;
    postFetch = ''
      # set up git hashes as if we used the tarball

      pushd $out
      git rev-parse HEAD > .gitcommit
      cd $out/abc
      git rev-parse HEAD > .gitcommit
      popd

      # remove .git now that we are through with it
      find "$out" -name .git -print0 | xargs -0 rm -rf
    '';
  };
  in
stdenv.mkDerivation {
  pname = "yosys";
  version = "0.60";


  enableParallelBuilding = true;
  nativeBuildInputs = [
    bison
    flex
    pkg-config
  ];

  propagatedBuildInputs = [
    libffi
    readline
    tcl
    zlib
    (python3.withPackages (
      pp: with pp; [
        click
        pybind11
        cxxheaderparser
      ]
    ))
  ]
  ++ lib.optionals enablePython [
    python3.pkgs.boost
  ];

  src = yosysSrc;

  makeFlags = [ "PREFIX=${placeholder "out"}" ];

  preBuild = ''
    chmod -R u+w .
    make config-${if stdenv.cc.isClang or false then "clang" else "gcc"}

    if ! grep -q "YOSYS_VER := $version" Makefile; then
      echo "ERROR: yosys version in Makefile isn't equivalent to version of the nix package (allegedly xxx), failing."
      exit 1
    fi
  ''
  + lib.optionalString enablePython ''
    echo "ENABLE_PYOSYS := 1" >> Makefile.conf
    echo "PYOSYS_USE_UV := 0" >> Makefile.conf
    echo "PYTHON_DESTDIR := $out/${python3.sitePackages}" >> Makefile.conf
    echo "BOOST_PYTHON_LIB := -lboost_python${lib.versions.major python3.version}${lib.versions.minor python3.version}" >> Makefile.conf
  '';

  doCheck = false;

  passthru = {
    updateScript = nix-update-script { };
  };

  meta = {
    description = "Open RTL synthesis framework and tools";
    homepage = "https://yosyshq.net/yosys/";
    license = lib.licenses.isc;
    platforms = lib.platforms.all;
  };
}
