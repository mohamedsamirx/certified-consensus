import CertifiedConsensus.Checker

/-!
# A contrario control of false alarms

A threshold on a residual is arbitrary: it depends on units, noise, and the operator's
taste. The a contrario principle replaces it with a *count*. Fix a family of `m` tests,
each of which fires on a set `A i` of configurations. Under the uniform model on the
finite configuration space `Ω`, the expected number of tests that fire is

  `(∑ i, #(A i)) / #Ω`.

Calibrating every test so that its own expected count is at most `ε / m` makes the total
expected number of false alarms at most `ε` — no threshold on the data, only a budget on
the number of tests. This is the finite form of the NFA (Number of False Alarms) bound of
Desolneux–Moisan–Morel, and the principle behind AC-RANSAC / ORSA.
-/

namespace CertifiedConsensus

open Finset

/-- **A contrario bound, finite form.** If each test fires on at most an `ε / m` fraction
of the configuration space, the expected number of firing tests is at most `ε`. -/
theorem expected_false_alarms_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (A : ι → Finset Ω) {ε : ℚ} (hε : 0 ≤ ε)
    (h : ∀ i, (A i).card * (Fintype.card ι : ℚ) ≤ ε * Fintype.card Ω)
    (hΩ : 0 < Fintype.card Ω) (hι : 0 < Fintype.card ι) :
    (∑ i, ((A i).card : ℚ)) / (Fintype.card Ω : ℚ) ≤ ε := by
  have hm : (0 : ℚ) < Fintype.card ι := by exact_mod_cast hι
  have hN : (0 : ℚ) < Fintype.card Ω := by exact_mod_cast hΩ
  have hsum : (∑ i, ((A i).card : ℚ)) * (Fintype.card ι : ℚ) ≤
      (Fintype.card ι : ℚ) * (ε * Fintype.card Ω) := by
    calc (∑ i, ((A i).card : ℚ)) * (Fintype.card ι : ℚ)
        = ∑ i, ((A i).card : ℚ) * (Fintype.card ι : ℚ) := by rw [Finset.sum_mul]
      _ ≤ ∑ _i ∈ Finset.univ, ε * (Fintype.card Ω : ℚ) := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact h i
      _ = (Fintype.card ι : ℚ) * (ε * Fintype.card Ω) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [div_le_iff₀ hN]
  nlinarith [hsum, hm, hN, hε]

/-- The union of the firing sets is contained in their sum, which is the counting form of
the union bound. -/
theorem card_biUnion_le_sum {Ω ι : Type*} [DecidableEq Ω] (A : ι → Finset Ω) (s : Finset ι) :
    (s.biUnion A).card ≤ ∑ i ∈ s, (A i).card :=
  Finset.card_biUnion_le

/-- A single test calibrated at `ε / m` satisfies the hypothesis of the a contrario
bound, up to the integrality of cardinalities. -/
theorem calibrated_hypothesis {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (A : ι → Finset Ω) {ε : ℚ} (hι : 0 < Fintype.card ι)
    (h : ∀ i, ((A i).card : ℚ) ≤ ε / Fintype.card ι * Fintype.card Ω) :
    ∀ i, (A i).card * (Fintype.card ι : ℚ) ≤ ε * Fintype.card Ω := by
  intro i
  have hm : (0 : ℚ) < Fintype.card ι := by exact_mod_cast hι
  have := h i
  rw [div_mul_eq_mul_div, le_div_iff₀ hm] at this
  linarith

end CertifiedConsensus
