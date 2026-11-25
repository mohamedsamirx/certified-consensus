import CertifiedConsensus

/-!
# Worked example: a quarter turn and a baseline

The camera pair

  `P₁ = [I | 0]`,  `P₂ = [A | b]`

with `A` a quarter turn about the optical axis and `b = (1/2, 1/10, 0)`.

Every statement below is proved symbolically by the kernel; nothing is evaluated by
compiled code. The data-driven counterpart is `lake exe certify`.
-/

open CertifiedConsensus
open scoped Matrix

/-- Quarter turn about the optical axis. -/
def demoA : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, -1, 0; 1, 0, 0; 0, 0, 1]

/-- Baseline of the second camera. -/
def demoB : Fin 3 → ℚ := ![1/2, 1/10, 0]

/-- The fundamental matrix `F = [b]ₓ A`. -/
def demoF : Matrix (Fin 3) (Fin 3) ℚ := crossMatrix demoB * demoA

/-- **Every** world point satisfies the epipolar constraint, for every depth. -/
example (x : Fin 3 → ℚ) (lam : ℚ) :
    epipolarResidual demoF x (demoA *ᵥ x + lam • demoB) = 0 :=
  epipolar_constraint demoA demoB x lam

/-- The baseline is the second epipole: it kills `F` from the left. -/
example : demoFᵀ *ᵥ demoB = 0 :=
  transpose_mulVec_epipolar demoA demoB

/-- The fundamental matrix is singular. -/
example : demoF.det = 0 :=
  det_epipolar demoA demoB

/-- Correspondences `x ↦ A x + b` for three world points at depth one. -/
def demoPts : List (Point × Point) :=
  [(homog 0 0, homog (1/2) (1/10)),
   (homog (1/2) (1/2), homog 0 (3/5)),
   (homog (1/4) (3/4), homog (-1/4) (7/20))]

/-- The three correspondences lie on the epipolar geometry of the pair. -/
example : ∀ p ∈ demoPts, epipolarResidual demoF p.1 p.2 = 0 := by
  intro p hp
  fin_cases hp <;>
    simp [epipolarResidual, demoF, demoA, demoB, homog, crossMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
