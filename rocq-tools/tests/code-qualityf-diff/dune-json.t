  $ cat > dune-log.json <<EOF
  > [
  >   {
  >     "command": "_build/default/fmdeps/vendored/rocq/topbin/coqc_bin.exe --config > /tmp/dune_6f9dd0_output",
  >     "output": [],
  >     "status": 1
  >   },
  >   {
  >     "command": "(cd _build/default && fmdeps/BRiCk/ltac2-extra/.bin/coqc -q -w <.. a spurious appearance of extra.v ..> fmdeps/BRiCk/ltac2-extra/theories/extra.v)",
  >     "output": [
  >       "what",
  >       "File \"./fmdeps/BRiCk/ltac2-extra/theories/extra.v\", line 43, characters 8-17:",
  >       "Warning: Unused variable: x. [ltac2-unused-variable,ltac2,default]",
  >       "File \"./fmdeps/BRiCk/ltac2-extra/theories/extra.v\", line 44, characters 19-20:",
  >       "Error: Syntax error: '.' expected after [command] (in [vernac_aux]).",
  >       ""
  >     ],
  >     "status": 1
  >   }
  > ]
  > EOF
  $ coqc-perf.code-quality-diff --after-dune dune-log.json
  # :x: New Errors (1)
  
  ```
  File "./fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 44, characters 19-20:
  Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  ```
  
  # :warning: New Warnings (2)
  
  ```
  File "fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 0, characters 0-0:
  Warning: Dangling output when building using coqc:
  what
  [dangling-output-stdout,dummy]
  ```
  ```
  File "./fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 43, characters 8-17:
  Warning: Unused variable: x. [ltac2-unused-variable,ltac2,default]
  ```
  

  $ coqc-perf.code-quality-diff --before-dune dune-log.json
  # :negative_squared_cross_mark: Fixed Errors (1)
  
  ```
  File "./fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 44, characters 19-20:
  Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  ```
  
  # :green_heart: Fixed Warnings (2)
  
  ```
  File "fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 0, characters 0-0:
  Warning: Dangling output when building using coqc:
  what
  [dangling-output-stdout,dummy]
  ```
  ```
  File "./fmdeps/BRiCk/ltac2-extra/theories/extra.v", line 43, characters 8-17:
  Warning: Unused variable: x. [ltac2-unused-variable,ltac2,default]
  ```
  
