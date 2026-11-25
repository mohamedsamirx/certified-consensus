import CertifiedConsensus.Basic

/-!
# Exact consensus probability

The classical RANSAC stopping rule assumes that, with inlier ratio `p`, a sample of `k`
correspondences is all-inlier with probability `p ^ k`. That model samples *with*
replacement. In reality a minimal sample is a `k`-subset of the data, drawn without
replacement, and the correct probability is the hypergeometric one

  `P(all inliers) = C(m, k) / C(n, k)`,

where `n` is the number of correspondences and `m` the number of inliers.

This file proves:

* `consensus_ratio` — the exact probability is `C(m,k)/C(n,k)`;
* `choose_ratio_le_pow` — it is at most `(m/n)^k`, so the folklore rule is never
  conservative;
* `choose_ratio_lt_pow` — the inequality is strict as soon as `k ≥ 2` and `m < n`,
  so the folklore rule always promises more confidence than it delivers.
-/

namespace CertifiedConsensus

open Finset
open scoped BigOperators

/-! ## Counting all-inlier samples -/

section Counting

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The `k`-subsets of the full type that lie inside a set `I` are exactly the
`k`-subsets of `I`. -/
theorem filter_powersetCard_subset (I : Finset α) (k : ℕ) :
    ((univ : Finset α).powersetCard k).filter (fun s => s ⊆ I) = I.powersetCard k := by
  ext s
  simp [Finset.mem_powersetCard, and_comm]

/-- Number of all-inlier samples: `C(|I|, k)`. -/
theorem card_filter_powersetCard_subset (I : Finset α) (k : ℕ) :
    (((univ : Finset α).powersetCard k).filter (fun s => s ⊆ I)).card = I.card.choose k := by
  rw [filter_powersetCard_subset, card_powersetCard]

/-- **Exact consensus probability.** Drawing a `k`-subset uniformly from `n`
correspondences of which `m` are inliers, the probability that every drawn
correspondence is an inlier is `C(m,k)/C(n,k)`. -/
theorem consensus_ratio (I : Finset α) (k : ℕ) :
    ((((univ : Finset α).powersetCard k).filter (fun s => s ⊆ I)).card : ℚ) /
        (((univ : Finset α).powersetCard k).card : ℚ) =
      (I.card.choose k : ℚ) / (Fintype.card α).choose k := by
  rw [card_filter_powersetCard_subset, card_powersetCard, card_univ]

end Counting

/-! ## The product formula for the hypergeometric ratio

`C(m,k)/C(n,k) = ∏_{i<k} (m-i)/(n-i)`. The right-hand side makes the comparison
with `(m/n)^k` a termwise one. -/

section Product

theorem choose_mul_factorial_eq_descFactorial (n k : ℕ) :
    n.choose k * k.factorial = n.descFactorial k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]

theorem cast_choose_mul_factorial (n k : ℕ) :
    (n.choose k : ℚ) * (k.factorial : ℚ) = (n.descFactorial k : ℚ) := by
  rw [← Nat.cast_mul, choose_mul_factorial_eq_descFactorial]

/-- The binomial ratio is a ratio of descending factorials; the common factor `k!`
cancels. -/
theorem choose_ratio_eq_descFactorial_ratio (m n k : ℕ) :
    (m.choose k : ℚ) / (n.choose k : ℚ) =
      (m.descFactorial k : ℚ) / (n.descFactorial k : ℚ) := by
  have hk : ((k.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [← cast_choose_mul_factorial m k, ← cast_choose_mul_factorial n k, mul_div_mul_right _ _ hk]

/-- Casting a descending factorial to `ℚ` turns it into a product of differences. -/
theorem cast_descFactorial_eq_prod (n k : ℕ) (hk : k ≤ n) :
    (n.descFactorial k : ℚ) = ∏ i ∈ range k, ((n : ℚ) - i) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl ?_
  intro i hi
  rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le (mem_range.mp hi) hk))]

/-- Termwise comparison with the with-replacement model. -/
theorem div_sub_le_div (m n i : ℕ) (hmn : m ≤ n) (him : i ≤ m) (hin : i < n) :
    ((m : ℚ) - i) / ((n : ℚ) - i) ≤ (m : ℚ) / n := by
  have hn : (0 : ℚ) < n := by
    have h : (0 : ℕ) < n := lt_of_le_of_lt (Nat.zero_le i) hin
    exact_mod_cast h
  have hden : (0 : ℚ) < (n : ℚ) - i := by
    have h : (i : ℚ) < n := by exact_mod_cast hin
    linarith
  rw [div_le_div_iff₀ hden hn]
  have hm : (m : ℚ) ≤ n := by exact_mod_cast hmn
  have hi : (i : ℚ) ≤ m := by exact_mod_cast him
  nlinarith

/-- The termwise comparison is strict when there is a genuine shortage of inliers. -/
theorem div_sub_lt_div (m n i : ℕ) (hmn : m < n) (him : i ≤ m) (hi : 1 ≤ i) :
    ((m : ℚ) - i) / ((n : ℚ) - i) < (m : ℚ) / n := by
  have hin : i < n := lt_of_le_of_lt him hmn
  have hn : (0 : ℚ) < n := by
    have h : (0 : ℕ) < n := lt_of_le_of_lt (Nat.zero_le i) hin
    exact_mod_cast h
  have hden : (0 : ℚ) < (n : ℚ) - i := by
    have h : (i : ℚ) < n := by exact_mod_cast hin
    linarith
  rw [div_lt_div_iff₀ hden hn]
  have hm : (m : ℚ) < n := by exact_mod_cast hmn
  have hi' : (1 : ℚ) ≤ i := by exact_mod_cast hi
  nlinarith

/-- A product of nonnegative factors is monotone. Stated for `ℚ`, where
`Finset.prod_le_prod` is unavailable because multiplication by a negative number
reverses the order. -/
theorem prod_le_prod_of_nonneg {s : Finset ℕ} {f g : ℕ → ℚ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hle : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact mul_le_mul (hle a (mem_insert_self a s))
        (ih (fun i hi => hf i (mem_insert_of_mem hi))
            (fun i hi => hle i (mem_insert_of_mem hi)))
        (Finset.prod_nonneg fun i hi => hf i (mem_insert_of_mem hi))
        (le_trans (hf a (mem_insert_self a s)) (hle a (mem_insert_self a s)))

/-- A product of positive factors, one of them strict, is strict. -/
theorem prod_lt_prod_of_nonneg {s : Finset ℕ} {f g : ℕ → ℚ}
    (hpos : ∀ i ∈ s, 0 < f i) (hle : ∀ i ∈ s, f i ≤ g i)
    {i₀ : ℕ} (hi₀ : i₀ ∈ s) (hlt : f i₀ < g i₀) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  have hle' : ∏ i ∈ s \ {i₀}, f i ≤ ∏ i ∈ s \ {i₀}, g i :=
    prod_le_prod_of_nonneg (fun i hi => le_of_lt (hpos i (mem_sdiff.mp hi).1))
      fun i hi => hle i (mem_sdiff.mp hi).1
  have hpos' : 0 < ∏ i ∈ s \ {i₀}, f i :=
    Finset.prod_pos fun i hi => hpos i (mem_sdiff.mp hi).1
  have hg : 0 ≤ g i₀ := le_trans (le_of_lt (hpos i₀ hi₀)) (hle i₀ hi₀)
  calc ∏ i ∈ s, f i = (∏ i ∈ s \ {i₀}, f i) * f i₀ :=
        Finset.prod_eq_prod_sdiff_singleton_mul hi₀ f
    _ = f i₀ * ∏ i ∈ s \ {i₀}, f i := by rw [mul_comm]
    _ < g i₀ * ∏ i ∈ s \ {i₀}, g i := mul_lt_mul hlt hle' hpos' hg
    _ = (∏ i ∈ s \ {i₀}, g i) * g i₀ := by rw [mul_comm]
    _ = ∏ i ∈ s, g i := (Finset.prod_eq_prod_sdiff_singleton_mul hi₀ g).symm

end Product

/-! ## The folklore bound -/

section Bound

/-- **The folklore bound.** The exact all-inlier probability never exceeds `p^k`. -/
theorem descFactorial_ratio_le_pow (m n k : ℕ) (hmn : m ≤ n) (hkm : k ≤ m) :
    (m.descFactorial k : ℚ) / (n.descFactorial k : ℚ) ≤ ((m : ℚ) / n) ^ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm0 : m = 0 := le_antisymm hmn (Nat.zero_le m)
    have hk0 : k = 0 := le_antisymm (hm0 ▸ hkm) (Nat.zero_le k)
    subst hm0 hk0
    norm_num
  have hkn : k ≤ n := le_trans hkm hmn
  rw [cast_descFactorial_eq_prod m k hkm, cast_descFactorial_eq_prod n k hkn, ← Finset.prod_div_distrib]
  rw [show ((m : ℚ) / n) ^ k = ∏ _ ∈ range k, ((m : ℚ) / n) by
    rw [Finset.prod_const, Finset.card_range]]
  have hnonneg : ∀ i ∈ range k, 0 ≤ ((m : ℚ) - i) / ((n : ℚ) - i) := by
    intro i hi
    have him : (i : ℚ) ≤ m := by
      exact_mod_cast le_of_lt (lt_of_lt_of_le (mem_range.mp hi) hkm)
    have hin : (i : ℚ) < n := by
      exact_mod_cast lt_of_lt_of_le (mem_range.mp hi) hkn
    exact div_nonneg (by linarith) (by linarith)
  exact prod_le_prod_of_nonneg hnonneg fun i hi =>
    div_sub_le_div m n i hmn (le_of_lt (lt_of_lt_of_le (mem_range.mp hi) hkm))
      (lt_of_lt_of_le (mem_range.mp hi) hkn)

/-- **The folklore bound is strict.** With at least one inlier missing and `k ≥ 2`, the
exact probability is strictly smaller than `p^k`. -/
theorem descFactorial_ratio_lt_pow (m n k : ℕ) (hmn : m < n) (hk : 2 ≤ k) (hkm : k ≤ m) :
    (m.descFactorial k : ℚ) / (n.descFactorial k : ℚ) < ((m : ℚ) / n) ^ k := by
  have hkn : k ≤ n := le_trans hkm (le_of_lt hmn)
  rw [cast_descFactorial_eq_prod m k hkm, cast_descFactorial_eq_prod n k hkn, ← Finset.prod_div_distrib]
  rw [show ((m : ℚ) / n) ^ k = ∏ _ ∈ range k, ((m : ℚ) / n) by
    rw [Finset.prod_const, Finset.card_range]]
  refine prod_lt_prod_of_nonneg ?_ ?_ (mem_range.mpr hk) ?_
  · intro i hi
    have him : (i : ℚ) < m := by
      exact_mod_cast lt_of_lt_of_le (mem_range.mp hi) hkm
    have hin : (i : ℚ) < n := by
      exact_mod_cast lt_of_lt_of_le (mem_range.mp hi) hkn
    exact div_pos (by linarith) (by linarith)
  · intro i hi
    exact div_sub_le_div m n i (le_of_lt hmn)
      (le_of_lt (lt_of_lt_of_le (mem_range.mp hi) hkm))
      (lt_of_lt_of_le (mem_range.mp hi) hkn)
  · exact div_sub_lt_div m n 1 hmn (by omega) le_rfl

/-- **Corrected stopping rule, combinatorial form.** The exact probability is
`C(m,k)/C(n,k)`, and it is dominated by `p^k`. -/
theorem choose_ratio_le_pow (m n k : ℕ) (hmn : m ≤ n) (hkm : k ≤ m) :
    (m.choose k : ℚ) / (n.choose k : ℚ) ≤ ((m : ℚ) / n) ^ k := by
  rw [choose_ratio_eq_descFactorial_ratio]
  exact descFactorial_ratio_le_pow m n k hmn hkm

/-- **The classical rule over-promises.** For `k ≥ 2` and `m < n` the inequality with
`p^k` is strict, so every textbook iteration count under-delivers its stated confidence. -/
theorem choose_ratio_lt_pow (m n k : ℕ) (hmn : m < n) (hk : 2 ≤ k) (hkm : k ≤ m) :
    (m.choose k : ℚ) / (n.choose k : ℚ) < ((m : ℚ) / n) ^ k := by
  rw [choose_ratio_eq_descFactorial_ratio]
  exact descFactorial_ratio_lt_pow m n k hmn hk hkm

/-- The same bound, transported to `ℝ` for use in the stopping rule. -/
theorem choose_ratio_le_pow_real (m n k : ℕ) (hmn : m ≤ n) (hkm : k ≤ m) :
    (m.choose k : ℝ) / (n.choose k : ℝ) ≤ ((m : ℝ) / n) ^ k := by
  have h := choose_ratio_le_pow m n k hmn hkm
  have h' : ((m.choose k : ℚ) / (n.choose k : ℚ) : ℝ) ≤ (((m : ℚ) / n) ^ k : ℝ) := by
    exact_mod_cast h
  simpa using h'

end Bound

end CertifiedConsensus
