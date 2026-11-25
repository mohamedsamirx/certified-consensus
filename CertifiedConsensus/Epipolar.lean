import CertifiedConsensus.Basic

/-!
# Epipolar geometry

With the first camera normalized to `P₁ = [I | 0]`, a world point `X = (x, 1)` projects to
`x` in the first image and to `x' = A x + b` in the second. The **fundamental matrix**

  `F = [b]ₓ A`

satisfies the epipolar constraint `x'ᵀ F x = 0` for every world point, has rank two, and
carries the two epipoles in its kernels:

* `b` spans the left kernel (`Fᵀ b = 0`), the epipole in the second image;
* `A⁻¹ b` spans the right kernel (`F e = 0`), the epipole in the first image.

This is the `F = [e']ₓ H` factorization of Hartley–Zisserman, Chapter 9.
-/

namespace CertifiedConsensus

open scoped Matrix BigOperators

variable {K : Type*} [Field K]

/-- The scalar triple product with a repeated vector vanishes: `v ⬝ (b × v) = 0`. -/
theorem dot_crossMatrix_self (v b : Fin 3 → K) : v ⬝ᵥ (crossMatrix b *ᵥ v) = 0 := by
  rw [crossMatrix_mulVec]
  simp [dotProduct, Fin.sum_univ_three]
  ring

/-- **Epipolar constraint.** Every point `x'` corresponding to `x` under the camera pair
`(I, 0), (A, b)` lies on the epipolar line `F x`, where `F = [b]ₓ A`. -/
theorem epipolar_constraint (A : Matrix (Fin 3) (Fin 3) K) (b x : Fin 3 → K) (lam : K) :
    (A *ᵥ x + lam • b) ⬝ᵥ ((crossMatrix b * A) *ᵥ x) = 0 := by
  rw [← Matrix.mulVec_mulVec, add_dotProduct, smul_dotProduct,
    dot_crossMatrix_self, dot_crossMatrix_mulVec]
  simp

/-- The second epipole `b` spans the left kernel of `F = [b]ₓ A`. -/
theorem transpose_mulVec_epipolar (A : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → K) :
    (crossMatrix b * A)ᵀ *ᵥ b = 0 := by
  rw [Matrix.transpose_mul, transpose_crossMatrix, Matrix.mul_neg, Matrix.neg_mulVec,
    ← Matrix.mulVec_mulVec, crossMatrix_mulVec_self, Matrix.mulVec_zero, neg_zero]

/-- The first epipole `e` with `A e = b` spans the right kernel of `F = [b]ₓ A`. -/
theorem mulVec_epipolar_of_eq (A : Matrix (Fin 3) (Fin 3) K) (b e : Fin 3 → K)
    (he : A *ᵥ e = b) : (crossMatrix b * A) *ᵥ e = 0 := by
  rw [← Matrix.mulVec_mulVec, he, crossMatrix_mulVec_self]

/-- The fundamental matrix is singular. -/
theorem det_epipolar (A : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → K) :
    (crossMatrix b * A).det = 0 := by
  rw [Matrix.det_mul, det_crossMatrix, zero_mul]

/-- The fundamental matrix is nonzero whenever the baseline and the second camera are
nondegenerate. -/
theorem epipolar_ne_zero (A : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → K)
    (hA : A.det ≠ 0) (hb : b ≠ 0) : crossMatrix b * A ≠ 0 := by
  intro h
  have h' : crossMatrix b = 0 := by
    calc crossMatrix b = crossMatrix b * (A * A⁻¹) := by
          rw [Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), Matrix.mul_one]
      _ = (crossMatrix b * A) * A⁻¹ := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.zero_mul]
  exact crossMatrix_ne_zero hb h'

end CertifiedConsensus
