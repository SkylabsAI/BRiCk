  $ cat > before <<EOF
  > File "./fmdeps/auto/coq-bluerock-auto-cpp/tests/arch_indep/simple_if_style_hpp_spec.v", line 100, characters 8-25:
  > Warning: Timeout (2.50s) exceeded: tactic ran for 3.98s [br-work-timeout,br]
  > EOF

  $ cat > after <<EOF
  > File "./fmdeps/auto/coq-bluerock-auto-cpp/tests/arch_indep/simple_if_style_hpp_spec.v", line 100, characters 8-25:
  > Warning: Timeout (2.50s) exceeded: tactic ran for 3.71s [br-work-timeout,br]
  > EOF

  $ coqc-perf.code-quality-diff before after
  # No Changes in Warnings or Errors
