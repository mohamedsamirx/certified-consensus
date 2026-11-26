variable {m n k : ℕ}

/-- The descending-factorial inequality underlying
`Nat.choose_div_choose_le_pow_div_pow`. -/
theorem descFactorial_mul_pow_le (hmn : m ≤ n) (hkm : k ≤ m) :
    m.descFactorial k * n ^ k ≤ n.descFactorial k * m ^ k := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  rw [show n ^ k = ∏ _ ∈ Finset.range k, n by simp]
  rw [show m ^ k = ∏ _ ∈ Finset.range k, m by simp]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i hi => ?_)
  have hik : i < k := Finset.mem_range.mp hi
  have him : i ≤ m := le_trans (Nat.le_of_lt hik) hkm
  rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm n m]
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hmn) (m * n)

/-- **Ratio bound for binomial coefficients.** If `m ≤ n` and `k ≤ m`, then
`C(m,k) / C(n,k) ≤ (m/n)^k`.

The left-hand side is the probability that a uniformly random `k`-element subset of an
`n`-element set is contained in a fixed `m`-element subset; the right-hand side is the
corresponding probability for `k` independent draws with replacement. -/
theorem choose_div_choose_le_pow_div_pow (hmn : m ≤ n) (hkm : k ≤ m) :
    (m.choose k : α) / (n.choose k : α) ≤ ((m : α) / n) ^ k := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · have hm0 : m = 0 := by omega
    have hk0 : k = 0 := by omega
    simp [hn0, hm0, hk0]
  have hnα : (0 : α) < n := by exact_mod_cast hn
  have hkn : k ≤ n := le_trans hkm hmn
  have hCn : (0 : α) < (n.choose k : α) := by exact_mod_cast Nat.choose_pos hkn
  have hpow : (0 : α) < (n : α) ^ k := pow_pos hnα k
  rw [div_pow, div_le_div_iff₀ hCn hpow]
  have hmain : (m.descFactorial k : α) * (n : α) ^ k ≤
      (n.descFactorial k : α) * (m : α) ^ k := by
    exact_mod_cast descFactorial_mul_pow_le hmn hkm
  have hfac : (0 : α) < (k.factorial : α) := by exact_mod_cast k.factorial_pos
  have hmul : ((m.choose k : α) * (n : α) ^ k) * (k.factorial : α) ≤
      ((m : α) ^ k * (n.choose k : α)) * (k.factorial : α) := by
    calc ((m.choose k : α) * (n : α) ^ k) * (k.factorial : α)
        = (m.descFactorial k : α) * (n : α) ^ k := by
          rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_cast; ac_rfl
      _ ≤ (n.descFactorial k : α) * (m : α) ^ k := hmain
      _ = ((m : α) ^ k * (n.choose k : α)) * (k.factorial : α) := by
          rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_cast; ac_rfl
  exact le_of_mul_le_mul_right hmul hfac
