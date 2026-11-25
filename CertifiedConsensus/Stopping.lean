import CertifiedConsensus.Exact

/-!
# The corrected stopping rule

`Stopping.lean` turns the exact consensus probability into the number of RANSAC
iterations needed to reach a target confidence `η`.

If a single minimal sample succeeds with probability `P`, then `N` independent
samples all fail with probability `(1 - P) ^ N`. Requiring `(1 - P) ^ N ≤ 1 - η`
gives the stopping rule

  `N = ⌈log (1 - η) / log (1 - P)⌉`.

The classical rule replaces `P` by `p ^ k`. Since `P ≤ p ^ k`, the classical `N` is
never large enough — the deficit is quantified in `Exact.lean`.
-/

namespace CertifiedConsensus

/-- **Corrected stopping rule.** With per-trial success probability `P`, taking
`⌈log (1 - η) / log (1 - P)⌉` independent samples fails with probability at most
`1 - η`. -/
theorem pow_le_one_sub_of_ge_log_div_log {P η : ℝ} (hP0 : 0 < P) (hP1 : P < 1)
    (hη0 : 0 < η) (hη1 : η < 1) :
    (1 - P) ^ (Nat.ceil (Real.log (1 - η) / Real.log (1 - P))) ≤ 1 - η := by
  have hq0 : 0 < 1 - P := by linarith
  have hq1 : 1 - P < 1 := by linarith
  have hqlog : Real.log (1 - P) < 0 := Real.log_neg hq0 hq1
  have hηpos : 0 < 1 - η := by linarith
  have hN : Real.log (1 - η) / Real.log (1 - P) ≤
      (Nat.ceil (Real.log (1 - η) / Real.log (1 - P)) : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonpos_right hN (le_of_lt hqlog)
  have hcancel : Real.log (1 - η) / Real.log (1 - P) * Real.log (1 - P) = Real.log (1 - η) :=
    div_mul_cancel₀ _ (ne_of_lt hqlog)
  have hkey : (Nat.ceil (Real.log (1 - η) / Real.log (1 - P)) : ℝ) * Real.log (1 - P) ≤
      Real.log (1 - η) := by
    linarith
  rw [← Real.log_le_log_iff (pow_pos hq0 _) hηpos, Real.log_pow]
  exact hkey

/-- Powers with base in `[0, 1]` are antitone in the exponent. -/
theorem pow_le_pow_of_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  calc a ^ m * a ^ d ≤ a ^ m * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ ha0 ha1) (pow_nonneg ha0 m)
    _ = a ^ m := mul_one _

/-- **Monotonicity.** Any number of iterations above the computed bound also suffices,
because the per-trial failure probability is below one. -/
theorem pow_le_one_sub_of_le {P η : ℝ} (hP0 : 0 < P) (hP1 : P < 1) (hη0 : 0 < η) (hη1 : η < 1)
    {N : ℕ} (hN : Nat.ceil (Real.log (1 - η) / Real.log (1 - P)) ≤ N) :
    (1 - P) ^ N ≤ 1 - η := by
  have hbase : 1 - P ≤ 1 := by linarith
  have hnonneg : 0 ≤ 1 - P := by linarith
  exact le_trans (pow_le_pow_of_le_one hnonneg hbase hN)
    (pow_le_one_sub_of_ge_log_div_log hP0 hP1 hη0 hη1)

/-- **The classical rule is not conservative.** With `P` the exact success probability
and `p ^ k` the folklore estimate, `P ≤ p ^ k` implies `1 - p ^ k ≤ 1 - P`, hence the
folklore iteration count always stops early. -/
theorem folklore_failure_probability_le {P p : ℝ} {k : ℕ} (hP : P ≤ p ^ k) (_hp : p ^ k < 1) :
    1 - p ^ k ≤ 1 - P := by
  linarith

end CertifiedConsensus
