#!/bin/bash
nix build --no-link .#hitlt.$1.src^* .#hitlt.$1^*
nix build .#hitlt.$1^out -o result/$1/out
nix build .#hitlt.$1^log -o result/$1/log
nix build .#hitlt.$1.src^out -o result/$1/hdl
nix build .#hitlt.$1.src^log -o result/$1/hdl-log
