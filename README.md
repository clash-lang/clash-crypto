# clash-crypto

## Rocq Proofs

Some proofs are available in the RocqProofs folder.

The Nix environment currently provides opam in the `withOpam` devShell,
providing a dependency management tool for Rocq libraries.

You can activate this devShell by using `nix develop .#withOpam`.

First execute `opam repo add rocq-released https://rocq-prover.org/opam/released`
and `opam repo add coq-released https://coq.inria.fr/opam/released`
to add the required repositories.

Then, you'll need to install these libraries:
- [coq-bits](https://github.com/rocq-community/bits), which provides a
representation for `BitVector`s on which we can reason easily.
- [coq-equations](https://github.com/mattam82/Coq-Equations), a nice framework
that enables us to define functions using equational reasoning.
- [mathcomp](https://github.com/math-comp/math-comp), a full-fledged library
for mathematical representations.
- [coq-mathcomp-zify](https://github.com/math-comp/mczify), that enables us to
use automated reasoning tactics such as `lia` on mathcomp-based propositions.

with `opam install <package>`. It'll also install a suitable verison of Coq with
them, such as 8.16.1.

## Nix & Synthesis

This repository is a [flake](https://wiki.nixos.org/wiki/Flakes), which
primarily defines a development shell to hack on `clash-crypto`, as well as
packages that build bitstreams used for hardware-in-the-loop tests.

### Development Tooling

The development shell can be entered using `nix develop`. This makes typical
haskell tools available (`cabal`, `ghc`), as well as FPGA tooling (yosys,
nextpnr). The project uses `shellFor`, which means that all the dependencies of
`clash-crypto` are first built through nix, and then made available to cabal.

A few alternative development shells are available, which are listed in the
flake, but can also be found by tab completion:

```
$ nix develop .#devShells.x86_64-linux.
.#devShells.x86_64-linux.allFeatures  .#devShells.x86_64-linux.withHLS
.#devShells.x86_64-linux.default      .#devShells.x86_64-linux.withOpam

$ nix develop .#devShells.x86_64-linux.withHLS
```

Development shells can also be loaded automatically on entering the directory
using
[direnv](https://direnv.net/man/direnv-stdlib.1.html#codeuse-flake-ltinstallablegtcode).

### Hardware-in-the-loop tests

The HITL tests can be run using `cabal run hitlt`, which will query the
appropriate package defined in the flake for uploading to the FPGA. The packages
can be found under the prefix `hitlt`:

```
$ nix build .#packages.x86_64-linux.hitlt.
.#hitlt.BEA            .#hitlt.HMACSHA512     .#hitlt.SHA256
.#hitlt.FastGCD        .#hitlt.HMACSHA512224  .#hitlt.SHA384
(...)
```

Each of these is a derivation that will build a packed bitstream for uploading.
By default, a symlink `result` is placed in the current directory pointing to
the build output:

```
$ ls result/
bin  top.bit
```

There is also a corresponding entry in `apps` for each of these, which will
simply call `ecpprog` with any following arguments, as well as the path to the
corresponding bitstream:

```
$ nix run .#apps.x86_64-linux.hitlt.SHA1.upload -- --help
Simple programming tool for Lattice ECP5/NX using FTDI-based JTAG programmers.
```

### Inspecting synthesis targets

Each synthesis target consists of three main steps, each of which is a separate
derivation:

* `.#packages.x86_64-linux.hitltHsPkgs.clash-crypto`: the build output of the
  `clash-crypto` without running any tests;
* `.#packages.x86_64-linux.hitlt.SHA1.src`: the verilog result of running clash
  on an environment with `clash-crypto`;
* `.#packages.x86_64-linux.hitlt.SHA1`: the result of running the appropriate
  synthesis tools to build a bitstream from verilog input.

Each of these can be built separately with `nix build`. Some tricks useful for
inspecting the build:

* You can pass `nix build -L` to output the build log as it is generated on
  stderr. This might especially be helpful for long place-and-route processes
  and such.
* You can look up the log of a build with `nix log ...`.

Another reasonable question is what each of these derivations actually do? You
can ask nix what the plan to build a derivation is as follows:

```
$ nix derivation show .#packages.x86_64-linux.hitlt.SHA1.src
{
  "/nix/store/(...)-clash-crypto-hitlt-instances-SHA-topEntitySHA1-hdl.drv": {
    "args": [
      "-e",
      "/nix/store/(...)-source-stdenv.sh",
      "/nix/store/(...)-default-builder.sh"
    ],
    "builder": "/nix/store/(...)-bash-5.3p3/bin/bash",
    "env": {
      "__structuredAttrs": "",
      "binding": "topEntitySHA1",
      "buildInputs": "",
      "buildPhase": "export PATH=/nix/store/(...)-ghc-9.10.3-with-packages/bin:$PATH\nclash \\\n  -package-db /nix/store/(...)-ghc-9.10.3-with-packages/lib/ghc-*/lib/package.conf.d \\\n  -outputdir . \\\n  --verilog -fclash-clear '-fclash-spec-limit=200' '-fclash-inline-limit=200' '-fconstraint-solver-iterations=20' \\\n  SHA -main-is topEntitySHA1\n",
      (...)
      "stdenv": "/nix/store/(...)-stdenv-linux",
      "strictDeps": "",
      "system": "x86_64-linux"
    },
    "inputDrvs": {
      "/nix/store/(...)-ghc-9.10.3-with-packages.drv": (...),
      "/nix/store/(...)-bash-5.3p3.drv": (...),
      "/nix/store/(...)-stdenv-linux.drv": (...)
    },
    "inputSrcs": [
      "/nix/store/(...)-source-stdenv.sh",
      "/nix/store/(...)-default-builder.sh"
    ],
    "name": "clash-crypto-hitlt-instances-SHA-topEntitySHA1-hdl",
    "outputs": (...)
    "system": "x86_64-linux"
  }
}
```

Nix will execute `builder` with `args` as arguments and `env` as environment
variables. This derivation uses a `stdenv`-based build plan: `source-stdenv.sh`
will call `$stdenv/setup` i.e. a file `setup` in the directory specified in the
`env` under `stdenv`. It's worth a read at some point! The summary, though, is
as follows:

* Does `env` define `buildCommandPath`? If so, source `buildCommandPath`.
* Otherwise, does `env` define `buildCommand`? If so, evaluate `buildCommand`.
* Otherwise, does `env` define `phases`? If so, run each phase in sequence:
  * Set the phase label in nix
  * Evaluate the environment variable whose name is the phase label
* Otherwise, run the default phases. Not all of them are listed here, but a few
  of the important ones are, in sequence:
  * `unpackPhase` (default: extract or copy $src)
  * `configurePhase`
  * `buildPhase`
  * `checkPhase`
  * `installPhase`

So, what does the derivation actually do? You can quickly scan if the derivation
uses `stdenv`; then look for the phases or `buildCommand(Path)`. The above
example only uses `buildPhase` and `installPhase`, running the following
commands:

```
$ nix eval --raw .#packages.x86_64-linux.hitlt.SHA1.src.buildPhase
export PATH=/nix/store/(...)-ghc-9.10.3-with-packages/bin:$PATH
clash \
  -package-db /nix/store/(...)-ghc-9.10.3-with-packages/lib/ghc-*/lib/package.conf.d \
  -outputdir . \
  --verilog -fclash-clear '-fclash-spec-limit=200' '-fclash-inline-limit=200' '-fconstraint-solver-iterations=20' \
  SHA -main-is topEntitySHA1

$ nix eval --raw .#packages.x86_64-linux.hitlt.SHA1.src.installPhase
mkdir -p $out
mv SHA.topEntitySHA1/* $out
rm $out/clash-manifest.json
```

This should give you enough information to run the command interactively if
needed.

### Changing synthesis targets

The source of truth is in `flake.nix`, but here are some hints on altering the
build:

* Any settings affecting both compilation and test running go in
  `build-config.nix` and `build-config-local.nix`. In particular the baud rate
  is set there.
* The HITLT configuration is in `nix/hitl.nix`. The steps in the synthesis chain
  can all accept extra flags. See also `onlyClash` and `ecp5.synthesize` in
  `nix/clash.nix` for options accepted by `ecp5.clash`.
* Each entry in `hitltTopEntities` overrides from `hitltBaseArgs`, so any
  target-specific options can be put there.
* Some particular flags that may be useful:
  * `synthFlags` is passed to `synth_ecp5` in the yosys script
