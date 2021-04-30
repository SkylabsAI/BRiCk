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
  # All dependencies information are here
  llvm = nixpkgs.llvm_10;
  llvmPackages = nixpkgs.llvmPackages_10;
  # aliases
  # * clang-unwrapped is a multi-platform cross-compiler, but cannot produce
  #   host binaries (because it is not integrated with Nix's magic).
  clang-unwrapped = llvmPackages.clang-unwrapped;
  # * clang is a host compiler that is integrated with Nix
  #   (and is implemented by clang-wrapper, a wrapper to clang that forces
  #   `-target x86_64-apple-darwin` among many other options).
  clang = llvmPackages.clang;
  lld = llvmPackages.lld;
  pkgs = [
    llvm
    clang
    lld
    nixpkgs.cmake
    clang-unwrapped.lib
  ];
  llvm_dir = llvm.outPath;
  clang_dir = clang-unwrapped.outPath;

  llvm_bin_dir = llvm_dir + "/bin";
  clang_bin_dir = clang_dir + "/bin";
  lld_bin_dir = lld.outPath + "/bin";

in
  nixpkgs.stdenv.mkDerivation {
    name = "env";
    buildInputs = pkgs;
    # cpp2v-core depends on ${LLVM,CLANG}_DIR
    # zeta depends on ${LLVM,CLANG}_BASE_DIR
    # NOVA depends on $PREFIX_{aarch64,x86_64}
    # Beware that ${foo} is expanded by Nix while ''${foo} is expanded by the shell.
    #
    # Nova might need clang-unwrapped on the PATH
    # cpp2v-core needs a wrapped compiler (clang or nothing) to build on the host.
    shellHook=''
      export LLVM_DIR=${llvm_dir}
      export CLANG_DIR=${clang_dir}
      export CLANG_PREFIX_aarch64=${clang_bin_dir}/
      export CLANG_PREFIX_x86_64=${clang_bin_dir}/
      export LLVM_BASE_DIR=${llvm_bin_dir}/
      export CLANG_BASE_DIR=${clang_bin_dir}/
      export LLD_BASE_DIR=${lld_bin_dir}/
      export CLANG_LIB_DIR=${clang-unwrapped.lib.outPath}/lib
      '';
      # export WRAPPED_CLANG_DIR=${clang.outPath}
      # export PATH=${clang-unwrapped.outPath}/bin:''$PATH
      # export PATH=${clang.outPath}/bin:''$PATH
  }
