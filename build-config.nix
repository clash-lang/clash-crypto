# To alter build configuration settings, please edit build-config-local.nix, but
# be careful not to commit changes. The better solution is to have local
# settings in a file that is ignored via .gitignore, but there currently is no
# good solution to address a flake that depends on files that are not in the git
# index.
{
  serial-speed = "115200";
  hitlt-serial-dev = "/dev/ttyUSB0";
} // import ./build-config-local.nix
