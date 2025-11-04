# clash-crypto

## Rocq Proofs

Some proofs are available in the RocqProofs folder.

The Nix environment currently provides opam in the `fullFledged` devShell,
providing a dependency management tool for Rocq libraries.

You can activate this devShell to use it with direnv, modifying `.envrc` in this
way:

```use flake .#fullFledged```.

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
