/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Inequalities for binomial coefficients

This file proves exponential bounds on binomial coefficients. We might want to add here the
bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.

## Main declarations

* `Nat.choose_le_pow_div`: `n.choose r ≤ n^r / r!`
* `Nat.pow_le_choose`: `(n + 1 - r)^r / r! ≤ n.choose r`. Beware of the fishy ℕ-subtraction.
-/

public section


open Nat

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {n k : ℕ}

namespace Nat

theorem choose_le_pow_div (r n : ℕ) : (n.choose r : α) ≤ (n ^ r : α) / r ! := by
  rw [le_div_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow r
  exact mod_cast r.factorial_pos

lemma choose_lt_pow_div (hn : n ≠ 0) (hk : 2 ≤ k) : (n.choose k : α) < (n ^ k : α) / k ! := by
  rw [lt_div_iff₀' (mod_cast k.factorial_pos)]
  norm_cast
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_lt_pow hn hk

lemma choose_le_descFactorial (n k : ℕ) : n.choose k ≤ n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]
  exact Nat.div_le_self _ _

lemma choose_lt_descFactorial (hk : 2 ≤ k) (hkn : k ≤ n) : n.choose k < n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]; exact Nat.div_lt_self (by simpa) (by simpa)

lemma choose_le_pow (n k : ℕ) : n.choose k ≤ n ^ k :=
  (choose_le_descFactorial n k).trans (descFactorial_le_pow n k)

lemma choose_lt_pow (hn : n ≠ 0) (hk : 2 ≤ k) : n.choose k < n ^ k :=
  (choose_le_descFactorial n k).trans_lt (descFactorial_lt_pow hn hk)

theorem choose_add_le_add_one_pow (n k : ℕ) : (n + k).choose k ≤ (n + 1) ^ k := by
  rw [choose_eq_asc_factorial_div_factorial]
  exact Nat.div_le_of_le_mul (ascFactorial_le_factorial_mul_pow _ _)

theorem choose_le_sub_pow (n k : ℕ) : n.choose k ≤ (n + 1 - k) ^ k := by
  rcases le_or_gt k n with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm k m, Nat.add_right_comm, Nat.add_sub_cancel]
    exact choose_add_le_add_one_pow m k
  · simp [choose_eq_zero_of_lt h]

-- horrific casting is due to ℕ-subtraction
theorem pow_le_choose (r n : ℕ) : ((n + 1 - r : ℕ) ^ r : α) / r ! ≤ n.choose r := by
  rw [div_le_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_descFactorial r
  exact mod_cast r.factorial_pos

theorem choose_succ_le_two_pow (n k : ℕ) : (n + 1).choose k ≤ 2 ^ n := by
  by_cases lt : n + 1 < k
  · simp [choose_eq_zero_of_lt lt]
  · cases n with
    | zero => cases k <;> simp_all
    | succ n =>
      rcases k with - | k
      · rw [choose_zero_right]
        exact Nat.one_le_two_pow
      · rw [choose_succ_succ', two_pow_succ]
        exact Nat.add_le_add (choose_succ_le_two_pow n k) (choose_succ_le_two_pow n (k + 1))

theorem choose_lt_two_pow (n k : ℕ) (p : 0 < n) : n.choose k < 2 ^ n := by
  refine lt_of_le_of_lt ?_ (Nat.two_pow_pred_lt_two_pow p)
  rw [← Nat.sub_add_cancel p]
  exact choose_succ_le_two_pow (n - 1) k

theorem choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  obtain (rfl | hn) := eq_zero_or_pos n
  · cases k <;> simp
  · exact (Nat.choose_lt_two_pow _ _ hn).le

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

end Nat
