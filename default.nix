{ nixpkgs ? import <nixpkgs> {  } }:
 
let
  pkgs = [
    nixpkgs.clang_11
    nixpkgs.llvm_11
    nixpkgs.cmake
  ];
 
in
  nixpkgs.stdenv.mkDerivation {
    name = "env";
    buildInputs = pkgs;
    shellHook=''
      export LLVM_DIR=${nixpkgs.llvm_11.outPath}
      export CLANG_DIR=${nixpkgs.llvmPackages_11.clang-unwrapped.outPath}
      '';
  }
