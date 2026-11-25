import CertifiedConsensus

open CertifiedConsensus

/-! Print the axiom dependencies of every headline theorem.
`scripts/verify.sh` fails the build if anything other than the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) shows up. -/

#print axioms ransac_iterations_le_exact
#print axioms choose_ratio_lt_pow
#print axioms pow_le_one_sub_of_ge_log_div_log
#print axioms epipolar_constraint
#print axioms checkEpipolar_sound_real
#print axioms expected_false_alarms_le
