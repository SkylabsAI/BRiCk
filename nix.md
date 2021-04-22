# Building under Nix

We support installing a standard configuration of LLVM and Clang using Nix, and
building against those. In short:

1. Install Nix on your system (see #installing-nix).
2. Run `nix-shell path/to/cpp2v-core/default.nix`.
   This will install clang 10 (and dependencies) to a special location, and open
   a shell with those tools on the PATH.
   The output will be similar to
   https://asciinema.org/a/b8QRpIknyacgKZFAvMVrlCzzw (but we currently do not
   install Coq via Nix.)
   Those tools will be cached.
3. Inside the Nix shell, compile cpp2v-core as usual.

## What is Nix

For us, the Nix package manager enables installing a reproducible software
configuration on arbitrary Linux/Mac computers, without using virtualization or
containers.

Nix mostly does not modify your existing configuration, outside of the `/nix`
folder.

## Installing Nix

Nix will be installed under the `/nix` folder; on Macs, this is complicated by
System Integrity Protection, but is still possible by creating and mounting a
separate volume.

### Limiting installation impact

Before the installation, you _might_ want to limit the impact of Nix installation (and make it less convenient) by setting:

```
export NIX_INSTALLER_NO_MODIFY_PROFILE=y
```

otherwise, Nix will modify your bash configuration to perform
```
. ~/.nix-profile/etc/profile.d/nix.sh
```
and make Nix commands available by defaults. With this setting, you will have to load that file by hand.

### Installation
For Linux/macOS <= 10.14 (details on https://nixos.org/guides/install-nix.html):

```
sh <(curl -L https://nixos.org/nix/install)
```

For macOS >= 10.15 (Catalina): (details on https://nixos.org/manual/nix/stable/#sect-macos-installation)

```
sh <(curl -L https://nixos.org/nix/install) --darwin-use-unencrypted-nix-store-volume
```

### Verifying installation

See https://nixos.org/download.html#nix-verify-installation.
