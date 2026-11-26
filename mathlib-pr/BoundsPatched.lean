/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Choose.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Inequalities for binomial coefficients

This file proves exponential and ratio bounds on binomial coefficients. We might want to add
here the bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.

## Main declarations

* `Nat.choose_le_pow_div`: `n.choose r ≤ n^r / r!`
* `Nat.pow_le_choose`: `(n + 1 - r)^r / r! ≤ n.choose r`. Beware of the fishy ℕ-subtraction.
* `Nat.choose_div_choose_le_pow_div_pow`: `m.choose k / n.choose k ≤ (m / n) ^ k` for `m ≤ n`
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

/-- For `m ≤ n`, `m.descFactorial k * n ^ k ≤ n.descFactorial k * m ^ k`. This is the
descending-factorial form of the ratio bound. -/
private lemma descFactorial_mul_pow_le {m : ℕ} (hmn : m ≤ n) :
    m.descFactorial k * n ^ k ≤ n.descFactorial k * m ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have h1 : (m - k) * n ≤ (n - k) * m := by
      rcases le_or_gt k m with hk | hk
      · rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm n m]
        exact Nat.sub_le_sub_left (Nat.mul_le_mul_left k hmn) (m * n)
      · rw [Nat.sub_eq_zero_of_le hk.le, Nat.zero_mul]
        exact Nat.zero_le _
    calc (m - k) * m.descFactorial k * (n ^ k * n)
        = ((m - k) * n) * (m.descFactorial k * n ^ k) := by ac_rfl
      _ ≤ ((n - k) * m) * (n.descFactorial k * m ^ k) := Nat.mul_le_mul h1 ih
      _ = (n - k) * n.descFactorial k * (m ^ k * m) := by ac_rfl

/-- For `m ≤ n`, `m.choose k * n ^ k ≤ n.choose k * m ^ k`. -/
private lemma choose_mul_pow_le {m : ℕ} (hmn : m ≤ n) :
    m.choose k * n ^ k ≤ n.choose k * m ^ k := by
  have h' : k.factorial * (m.choose k * n ^ k) ≤ k.factorial * (n.choose k * m ^ k) := by
    calc k.factorial * (m.choose k * n ^ k)
        = (k.factorial * m.choose k) * n ^ k := by ac_rfl
      _ = m.descFactorial k * n ^ k := by rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ ≤ n.descFactorial k * m ^ k := descFactorial_mul_pow_le hmn
      _ = (k.factorial * n.choose k) * m ^ k := by rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ = k.factorial * (n.choose k * m ^ k) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left h' k.factorial_pos

/-- **Ratio bound for binomial coefficients.** For `m ≤ n`, the ratio of binomial
coefficients `m.choose k / n.choose k` is at most `(m / n) ^ k`.

This is the probability that `k` items drawn without replacement from `n` items, of which
`m` are marked, are all marked: it is at most the corresponding probability `(m / n) ^ k`
for drawing with replacement. The bound is an equality when `m = n` and when `k ≤ 1`, and
is sharper than the estimate obtained from `Nat.choose_le_pow_div` and `Nat.pow_le_choose`
for `2 ≤ k`. -/
theorem choose_div_choose_le_pow_div_pow {m : ℕ} (hmn : m ≤ n) :
    (m.choose k : α) / (n.choose k : α) ≤ ((m : α) / n) ^ k := by
  rcases le_or_gt k m with hkm | hkm
  · obtain rfl | hn := eq_zero_or_pos n
    · have hm0 : m = 0 := Nat.le_zero.mp hmn
      have hk0 : k = 0 := Nat.le_zero.mp (hm0 ▸ hkm)
      simp [hm0, hk0]
    have hnα : (0 : α) < n := by exact_mod_cast hn
    have hkn : k ≤ n := le_trans hkm hmn
    have hCn : (0 : α) < (n.choose k : α) := by exact_mod_cast Nat.choose_pos hkn
    have hpow : (0 : α) < (n : α) ^ k := pow_pos hnα k
    rw [div_pow, div_le_div_iff₀ hCn hpow]
    have hnat : m.choose k * n ^ k ≤ n.choose k * m ^ k := choose_mul_pow_le hmn
    have hcast : (m.choose k : α) * (n : α) ^ k ≤ (n.choose k : α) * (m : α) ^ k := by
      exact_mod_cast hnat
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hcast
  · rw [Nat.choose_eq_zero_of_lt hkm, Nat.cast_zero, zero_div]
    exact pow_nonneg (div_nonneg (by exact_mod_cast Nat.zero_le m)
      (by exact_mod_cast Nat.zero_le n)) k

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

end Nat
