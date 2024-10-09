BlueRock C++ Program Verification Setup
=======================================

Getting Started
---------------

Assuming that all necessary packages are installed, a C++ verification project
(for now only containing generated code files) can be set up using the command
`br init` at the root of the project's directory (where you'd typically have a
`.git` folder).

Consider, for example, a project with the following structure.
```
example
├── include
│   └── util.hpp
├── Makefile
└── src
    ├── client
    │   ├── client.cpp
    │   └── include
    │       └── client.hpp
    └── server
        ├── include
        │   └── server.hpp
        └── server.cpp
```
In that case, the setup can be done by running a command like the following (a
description of available options can be obtained with `br init --help`).
```bash
br init -I include -I src/client/include -I src/server/include \
  --flags=-Werror,-Wall,-Wextra
```
Note that the tool will detect that the current directory is called `example`,
and will use that name to derive a Coq directory path for the project, as well
as an opam package name.

The main effect of running `br init` is to add a `br-project.toml` file to the
current working directory. This file can then be directly edited to change the
configuration of the project.

To update generated files, you need to run `br gen`, and also `dune build` for
generated `*.opam` files. All of these generated files should be added to your
repository.

Project Configuration file
--------------------------

A project configuration file `br-project.toml` must exist at the root of the
project, and is typically generated using `br init` (see above). It can look
like the following, for example.
```toml
[coq]
dirpath = "my.project"
package = "my_package"
theories = ["Equations"]

[clang]
includes = ["include", "src/include"]
flags = ["-Werror", "-Wall"]

[project]
ignored = ["attic", "some/file.cpp"]
```

Note that only the `coq.dirpath` and `coq.package` options are mandatory, the
other options default to empty lists.

Local Configuration file
------------------------

When configuration needs to be extended or modified in some directories, one
can create a `br-config.toml` file. The configuration for any given C++ source
file is obtained by combining the contents of the project configuration file,
as well as all local configuration files in directories on the path to the
source file.

An example of local configuration file is given below.
```toml
[coq]
extra_theories = ["ExtLib"]

[clang]
extra_includes = ["include"]
extra_flags = ["-Wextra"]

[project]
ignored = ["another/file.cpp"]
```
Note that all paths are relative to the configuration file.

Setting the option `clang.includes` instead of `clang.extra_includes` will
override the configurations inherited from more general configuration files.
Similarly, one can set `clang.flags` instead of `clang.extra_flags`, or also
`coq.theories` instead of `coq.extra_theories`. The Coq directory path can
also be modified. If it is not, a directory path is derived according to the
directory hierarchy, and the directory path that is in effect at that point
in the file system. The Coq package can also be overriden.

The `project.ignored` configuration always extends previous configurations.

Generating
----------

Running the following command will generate the necessary dune files so that
dune is able to generate code files for all C++ source files in the source
tree.
```bash
br gen
```

Use `br --help` to learn about all available options.
