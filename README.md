# clash-crypto

## Rocq Proofs

Some proofs are available in the RocqProofs folder.

The Nix environment currently provides opam, providing a dependency management
tool for Rocq libraries.

First execute `opam repo add rocq-released https://rocq-prover.org/opam/released`
and `opam repo add coq-released https://coq.inria.fr/opam/released`
to add the required repositories.

Then, you'll need to install these libraries:
- coq-bits
- coq-equations
- mathcomp-boot
- coq-mathcomp-zify

with `opam install <package>`. It'll also install a suitable verison of Coq with
them.
