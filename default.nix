# Pin a specific version of the Nixpkgs repository; following
# https://nixos.wiki/wiki/FAQ/Pinning_Nixpkgs
{ nixpkgs ? import (builtins.fetchTarball https://github.com/nixos/nixpkgs/archive/7919518f0235106d050c77837df5e338fb94de5d.tar.gz) {} }:

# Longer-form version
#{ nixpkgs ? import (builtins.fetchTarball {
#  # Descriptive name to make the store path easier to identify
#  name = "nixpkgs-unstable-2021-04-20";
#  # Commit hash for nixos-unstable as of 2021-04-20
#  url = "https://github.com/nixos/nixpkgs/archive/7919518f0235106d050c77837df5e338fb94de5d.tar.gz";
#  # Hash obtained using `nix-prefetch-url --unpack <url>`
#  sha256 = "06vy0qc4y3gsgm7s4d37aw4xfklmqvgp3mkpwvn9h2kbw19jh4pp";
#}) {} }:

let
  pkgs = [
    nixpkgs.clang_10
    nixpkgs.llvm_10
    nixpkgs.cmake
  ];

in
  nixpkgs.stdenv.mkDerivation {
    name = "env";
    buildInputs = pkgs;
    shellHook=''
      export LLVM_DIR=${nixpkgs.llvm_10.outPath}
      export CLANG_DIR=${nixpkgs.llvmPackages_10.clang-unwrapped.outPath}
      '';
  }
