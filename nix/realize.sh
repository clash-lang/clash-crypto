#!/bin/bash
nix build --no-link .#hitlt.$1.src^* .#hitlt.$1^*
nix build .#hitlt.$1^out -o _build_nix/$1/05-bitstream
nix build .#hitlt.$1^log -o _build_nix/$1/05-bitstream
nix build .#hitlt.$1.src^out -o _build_nix/$1/02-hdl
nix build .#hitlt.$1.src^log -o _build_nix/$1/02-hdl
