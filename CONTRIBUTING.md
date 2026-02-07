# Contribution Guidelines

We are always happy to receive contributions of any kind via GitHub
pull request. Nevertheless, to keep this a maintained and reusable
library, we request contributors to respect our coding guidelines
summarized below. Maintainers are free to reject, modify or request
changes for a PR whenever these guidelines are violated. If any of the
below mentioned regulations are unclear, or deviation from the
guidelines is strictly necessary for some technical reasons, then please
indicate this clearly as part of your PR or in a subsequent
comment. We will do our best to help you finding a suitable solution
wherever possible.

## Module Structure

The module structure of the main library follows the structure of the
[crypton](https://hackage.haskell.org/package/crypton) library, while
additionally adding a `Clash` module prefix. Simulation and HITL tests
always shall use the same module names as the main library, while
adding a `Simulate` or `Hitl` module prefix, respectively. Modules
that need to be shared between different test systems shall be placed
in the `test` library and are prefixed with `Test`.

## Test Coverage and Documentation

We request all new Clash designs to be at least sufficiently tested
via simulation tests, while we aim to also offer HITL tests for all of
the libraries components.

We consider it essential to share documented code. In that regard,
please take care that all of the contributed hardware primitives have
some sufficient amount of documentation at least for the top level
bindings, as required by Haddock for documentation generation.

## Coding Style

Have a look at [STYLE.md](./STYLE.md).
