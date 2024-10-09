  $ . ../setup.sh
  $ find | sort
  .
  ./example
  ./example/Makefile
  ./example/include
  ./example/include/util.hpp
  ./example/src
  ./example/src/client
  ./example/src/client/client.cpp
  ./example/src/client/include
  ./example/src/client/include/client.hpp
  ./example/src/server
  ./example/src/server/include
  ./example/src/server/include/server.hpp
  ./example/src/server/server.cpp
  $ cd example
  $ br init -I include -I src/client/include -I src/server/include --flags=-Werror,-Wall,-Wextra
  $ cat br-project.toml
  # Project configuration file (at the root of the workspace).
  
  [coq]
  dirpath = "br.project.example"
  package = "example"
  theories = []
  
  [clang]
  includes = ["include", "src/client/include", "src/server/include"]
  flags = ["-Werror", "-Wall", "-Wextra"]
  
  [project]
  ignored = []
  $ br gen
  $ find | sort
  .
  ./Makefile
  ./br-project.toml
  ./dune-project
  ./include
  ./include/proof
  ./include/proof/util_hpp
  ./include/proof/util_hpp/dune
  ./include/util.hpp
  ./src
  ./src/client
  ./src/client/client.cpp
  ./src/client/include
  ./src/client/include/client.hpp
  ./src/client/include/proof
  ./src/client/include/proof/client_hpp
  ./src/client/include/proof/client_hpp/dune
  ./src/client/proof
  ./src/client/proof/client_cpp
  ./src/client/proof/client_cpp/dune
  ./src/server
  ./src/server/include
  ./src/server/include/proof
  ./src/server/include/proof/server_hpp
  ./src/server/include/proof/server_hpp/dune
  ./src/server/include/server.hpp
  ./src/server/proof
  ./src/server/proof/server_cpp
  ./src/server/proof/server_cpp/dune
  ./src/server/server.cpp
