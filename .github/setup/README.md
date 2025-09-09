# Setting up Github Action Runners

The following steps are needed to enable the Github Actions CI
workflow of this repository.

## Setting up the docker image

Build and push the image via

```
cd .github/setup
docker build -t ghcr.io/qbaylogic/nix-attic:latest -t ghcr.io/qbaylogic/nix-attic:<today>-<commit>
docker login ghcr.io/qbaylogic
docker push ghcr.io/qbaylogic/nix-attic:latest
docker push ghcr.io/qbaylogic/nix-attic:<today>-<commit>
```

where `<today>` must be replaced by the docker build date (`YYYYMMDD`
format) and `<commit>` by the commit of the attic version that is
running on the cache server. The commit hash should match with one
being declared in the Dockerfile.

## Setup a runner with access to the OrangeCrab board

On the runner (as user `root`):

* copy `90-orangecrab.rules` to `/etc/udev/rules.d/90-orangecrab.rules`
* copy `unique-device-num` to `/etc/udev/scripts/unique-device-num`
* make sure `/etc/udev/scripts/unique-device-num` is executable

The runner must be tagged with `self-hosted`, `hardware-access`, and
`orangecrab`.