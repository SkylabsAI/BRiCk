  $ mkdir globs
  $ cat > globs/test.glob.stderr <<EOF
  > File "test.v", line 44, characters 19-20:
  > Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  > EOF
  $ cat > globs/test.glob.stdout <<EOF
  > dangling text!
  > EOF
  $ cat > globs/files <<EOF
  > globs/test.glob.stderr
  > globs/test.glob.stdout
  > EOF
  $ coqc-perf.code-quality-diff --after-globs-from-file globs/files
  # :x: New Errors (1)
  
  ```
  File "test.v", line 44, characters 19-20:
  Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  ```
  
  # :warning: New Warnings (1)
  
  ```
  File "test.v", line 0, characters 0-0:
  Warning: Non-empty stdout when building using coqc:
  dangling text!
  [non-empty-stdout,dummy]
  ```
  

  $ coqc-perf.code-quality-diff --before-globs-from-file globs/files
  # :negative_squared_cross_mark: Fixed Errors (1)
  
  ```
  File "test.v", line 44, characters 19-20:
  Error: Syntax error: '.' expected after [command] (in [vernac_aux]).
  ```
  
  # :green_heart: Fixed Warnings (1)
  
  ```
  File "test.v", line 0, characters 0-0:
  Warning: Non-empty stdout when building using coqc:
  dangling text!
  [non-empty-stdout,dummy]
  ```
  
