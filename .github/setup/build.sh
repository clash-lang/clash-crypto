#!/bin/bash
HERE=$(dirname $(realpath "$0"))
ROOT=$(dirname $(dirname "$HERE"))

DOCKERS="docker podman err"

if [ -z "$DOCKER" ]; then
  for DOCKER in $DOCKERS; do
    $DOCKER --help >/dev/null 2>/dev/null
    if [ 0 -eq $? ]; then break; fi
  done
  if [ "$DOCKER" == "err" ]; then
    echo "Docker is required to build the CI image."
    exit 1
  fi
fi

if [ -z "$ATTIC_VERSION" ]; then
  ATTIC_VERSION=$(sed -rn "s/^ARG ATTIC_VERSION=\"(.*)\"$/\\1/p" $HERE/Dockerfile)
fi

if [ -z "$ATTIC_VERSION_TAG" ]; then
  ATTIC_VERSION_TAG=${ATTIC_VERSION:0:7}
fi

DATE=$(date +%Y%m%d)

(
  cd $ROOT
  $DOCKER build . -f $HERE/Dockerfile \
    --build-arg ATTIC_VERSION="$ATTIC_VERSION" \
    -t ghcr.io/qbaylogic/clash-crypto-ci:latest \
    -t ghcr.io/qbaylogic/clash-crypto-ci:$DATE-$ATTIC_VERSION_TAG \
    $DOCKER_ARGS
)
