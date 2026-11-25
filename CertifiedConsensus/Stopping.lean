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
    (_hη0 : 0 < η) (hη1 : η < 1) :
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

/-- Monotonicity of `Nat.ceil` on `ℝ`. -/
theorem ceil_le_ceil_of_le {a b : ℝ} (h : a ≤ b) : Nat.ceil a ≤ Nat.ceil b := by
  rw [Nat.ceil_le]
  exact le_trans h (Nat.le_ceil b)

/-- **The folklore iteration count never exceeds the exact one.**

If `P` is the exact per-trial success probability and `p ^ k` the textbook estimate, then
`P ≤ p ^ k` yields at least as many required iterations under the exact rule. This is the
formal content of "the classical rule stops too early": not merely a smaller success
probability, but a smaller iteration budget. -/
theorem folklore_iterations_le_exact {P p : ℝ} {k : ℕ} (hP : P ≤ p ^ k) (hP0 : 0 < P)
    (_hp0 : 0 < p ^ k) (hp1 : p ^ k < 1) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    Nat.ceil (Real.log (1 - η) / Real.log (1 - p ^ k)) ≤
      Nat.ceil (Real.log (1 - η) / Real.log (1 - P)) := by
  have hq1 : 0 < 1 - P := by linarith
  have hq2 : 0 < 1 - p ^ k := by linarith
  have hlog : Real.log (1 - p ^ k) ≤ Real.log (1 - P) :=
    Real.log_le_log hq2 (by linarith)
  have hneg : Real.log (1 - P) < 0 := Real.log_neg hq1 (by linarith)
  have hL : Real.log (1 - η) < 0 := Real.log_neg (by linarith) (by linarith)
  have hinv : 1 / Real.log (1 - P) ≤ 1 / Real.log (1 - p ^ k) :=
    one_div_le_one_div_of_neg_of_le hneg hlog
  have hmul : Real.log (1 - η) / Real.log (1 - p ^ k) ≤
      Real.log (1 - η) / Real.log (1 - P) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonpos_left (by simpa using hinv) (le_of_lt hL)
  exact ceil_le_ceil_of_le hmul

/-- **End-to-end form, with binomials.** Let `m = ⌈p · n⌉`-style inlier count and `k` the
minimal sample size. Then the textbook RANSAC iteration count based on `(m/n)^k` is never
larger than the exact count based on `C(m,k)/C(n,k)`. -/
theorem ransac_iterations_le_exact (m n k : ℕ) (hmn : m < n) (hk : 2 ≤ k) (hkm : k ≤ m)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    Nat.ceil (Real.log (1 - η) / Real.log (1 - ((m : ℝ) / n) ^ k)) ≤
      Nat.ceil (Real.log (1 - η) /
        Real.log (1 - (m.choose k : ℝ) / (n.choose k : ℝ))) := by
  have hn : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hp0 : 0 < (m : ℝ) / n := by positivity
  have hp1 : (m : ℝ) / n < 1 := by
    rw [div_lt_one (by exact_mod_cast hn)]
    exact_mod_cast hmn
  have hpk0 : 0 < ((m : ℝ) / n) ^ k := pow_pos hp0 k
  have hpk1 : ((m : ℝ) / n) ^ k < 1 :=
    pow_lt_one₀ (le_of_lt hp0) hp1 (by omega)
  have hP0 : 0 < (m.choose k : ℝ) / (n.choose k : ℝ) := by
    apply div_pos
    · exact_mod_cast Nat.choose_pos hkm
    · exact_mod_cast Nat.choose_pos (le_trans hkm (le_of_lt hmn))
  exact folklore_iterations_le_exact
    (choose_ratio_le_pow_real m n k (le_of_lt hmn) hkm) hP0 hpk0 hpk1 hη0 hη1

end CertifiedConsensus
