import CertifiedConsensus.Epipolar

/-!
# Exact certificate checking

A fundamental matrix is only as trustworthy as the arithmetic used to verify it.
Floating-point residuals are never exactly zero, so every checker in practice relies on a
threshold — and a threshold is exactly what a certificate is supposed to remove.

This file checks the epipolar constraint over `ℚ`. Image coordinates arrive as decimal
literals, which are rationals, so the conversion is exact: a certificate that passes is
kernel-checked with no numerical trust at all.

Rank two is certified by `det F = 0` together with a nonzero `2 × 2` minor, which is a
witness that can be checked entry by entry.
-/

namespace CertifiedConsensus

open scoped Matrix BigOperators

/-- A homogeneous image point with rational coordinates. -/
abbrev Point := Fin 3 → ℚ

/-- Lift image coordinates to homogeneous coordinates. -/
def homog (u v : ℚ) : Point := ![u, v, 1]

/-- The `2 × 2` minor on rows `i, j` and columns `k, l`. -/
def minor2 (F : Matrix (Fin 3) (Fin 3) ℚ) (i j k l : Fin 3) : ℚ :=
  F i k * F j l - F i l * F j k

/-- The nine maximal minors of a `3 × 3` matrix. -/
def minors2 (F : Matrix (Fin 3) (Fin 3) ℚ) : List ℚ :=
  [minor2 F 0 1 0 1, minor2 F 0 1 0 2, minor2 F 0 1 1 2,
   minor2 F 0 2 0 1, minor2 F 0 2 0 2, minor2 F 0 2 1 2,
   minor2 F 1 2 0 1, minor2 F 1 2 0 2, minor2 F 1 2 1 2]

/-- `F` has rank two: it is singular and some `2 × 2` minor does not vanish. -/
def IsRankTwo (F : Matrix (Fin 3) (Fin 3) ℚ) : Bool :=
  (F.det == 0) && (minors2 F).any (fun m => m != 0)

variable {R : Type*} [Field R]

/-- The epipolar residual `yᵀ F x`. -/
def epipolarResidual (F : Matrix (Fin 3) (Fin 3) R) (x y : Fin 3 → R) : R :=
  y ⬝ᵥ (F *ᵥ x)

/-- Check every correspondence against the epipolar constraint. -/
def checkCorrespondences (F : Matrix (Fin 3) (Fin 3) ℚ) (pts : List (Point × Point)) : Bool :=
  pts.all (fun p => epipolarResidual F p.1 p.2 == 0)

/-- The full certificate: rank two and a vanishing residual on every correspondence. -/
def checkEpipolar (F : Matrix (Fin 3) (Fin 3) ℚ) (pts : List (Point × Point)) : Bool :=
  IsRankTwo F && checkCorrespondences F pts

theorem isRankTwo_sound {F : Matrix (Fin 3) (Fin 3) ℚ} (h : IsRankTwo F = true) :
    F.det = 0 ∧ ∃ m ∈ minors2 F, m ≠ 0 := by
  simp only [IsRankTwo, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hdet, hany⟩ := h
  refine ⟨hdet, ?_⟩
  simpa using List.any_eq_true.mp hany

theorem checkCorrespondences_sound {F : Matrix (Fin 3) (Fin 3) ℚ} {pts : List (Point × Point)}
    (h : checkCorrespondences F pts = true) :
    ∀ p ∈ pts, epipolarResidual F p.1 p.2 = 0 := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simpa using this

/-- **Soundness of the certificate checker.** A certificate that passes establishes that
`F` is singular, has a nonvanishing maximal minor, and satisfies the epipolar constraint
exactly on every correspondence. -/
theorem checkEpipolar_sound {F : Matrix (Fin 3) (Fin 3) ℚ} {pts : List (Point × Point)}
    (h : checkEpipolar F pts = true) :
    F.det = 0 ∧ (∃ m ∈ minors2 F, m ≠ 0) ∧
      ∀ p ∈ pts, epipolarResidual F p.1 p.2 = 0 := by
  simp only [checkEpipolar, Bool.and_eq_true] at h
  exact ⟨(isRankTwo_sound h.1).1, (isRankTwo_sound h.1).2, checkCorrespondences_sound h.2⟩

/-- Casting a residual to `ℝ` commutes with casting the data. -/
theorem residual_cast (F : Matrix (Fin 3) (Fin 3) ℚ) (x y : Point) :
    ((epipolarResidual F x y : ℚ) : ℝ) =
      epipolarResidual (F.map (Rat.cast : ℚ → ℝ))
        (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) := by
  simp [epipolarResidual, dotProduct, Matrix.mulVec, Matrix.map_apply, Fin.sum_univ_three]

/-- A rational certificate yields a real-valued vanishing residual. -/
theorem checkEpipolar_sound_real {F : Matrix (Fin 3) (Fin 3) ℚ} {pts : List (Point × Point)}
    (h : checkEpipolar F pts = true) :
    ∀ p ∈ pts,
      epipolarResidual (F.map (Rat.cast : ℚ → ℝ))
        (fun i => (p.1 i : ℝ)) (fun i => (p.2 i : ℝ)) = 0 := by
  intro p hp
  have hc : checkCorrespondences F pts = true := by
    simp only [checkEpipolar, Bool.and_eq_true] at h
    exact h.2
  have hres := checkCorrespondences_sound hc p hp
  rw [← residual_cast, hres]
  simp

/-! ## Certified tolerance

Real correspondences never satisfy the epipolar constraint exactly. The tolerance
checker replaces `residual = 0` by `|residual| ≤ δ`, where `δ` is an explicit rational
supplied by the caller. The result is still a machine-checked statement: not "the
residual is small", but "the residual is at most this number". -/

/-- The residual lies in `[-δ, δ]`. -/
def residualWithin (F : Matrix (Fin 3) (Fin 3) ℚ) (p : Point × Point) (δ : ℚ) : Bool :=
  let r := epipolarResidual F p.1 p.2
  (r ≤ δ) && (-δ ≤ r)

/-- Tolerance certificate: rank two, and every residual bounded by `δ`. -/
def checkEpipolarTol (δ : ℚ) (pts : List (Point × Point))
    (F : Matrix (Fin 3) (Fin 3) ℚ) : Bool :=
  IsRankTwo F && pts.all (fun p => residualWithin F p δ)

/-- **Soundness of the tolerance checker.** A passing certificate establishes rank two
and the explicit bound `|x'ᵀ F x| ≤ δ` on every correspondence. -/
theorem checkEpipolarTol_sound {δ : ℚ} {pts : List (Point × Point)}
    {F : Matrix (Fin 3) (Fin 3) ℚ} (h : checkEpipolarTol δ pts F = true) :
    F.det = 0 ∧ (∃ m ∈ minors2 F, m ≠ 0) ∧
      ∀ p ∈ pts, |epipolarResidual F p.1 p.2| ≤ δ := by
  simp only [checkEpipolarTol, Bool.and_eq_true] at h
  obtain ⟨hrank, hall⟩ := h
  refine ⟨(isRankTwo_sound hrank).1, (isRankTwo_sound hrank).2, ?_⟩
  intro p hp
  have hp' := List.all_eq_true.mp hall p hp
  simp only [residualWithin, Bool.and_eq_true, decide_eq_true_eq] at hp'
  exact abs_le.mpr ⟨hp'.2, hp'.1⟩

end CertifiedConsensus
