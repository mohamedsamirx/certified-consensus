import Mathlib

/-!
# Basic primitives for two-view geometry

This file introduces the skew-symmetric cross-product matrix `[b]ₓ` and proves the
elementary identities that the epipolar construction rests on.

Everything here is over an arbitrary field, so the same statements serve the
certificate checker over `ℚ` and the geometric theorems over `ℝ`.
-/

namespace CertifiedConsensus

open scoped Matrix

variable {K : Type*} [Field K]

/-- The cross-product matrix of a vector `b = (b₀, b₁, b₂)`:

```
[b]ₓ = ⎡ 0   -b₂   b₁ ⎤
       ⎢ b₂   0   -b₀ ⎥
       ⎣-b₁   b₀   0  ⎦
```

It is the matrix of the linear map `v ↦ b × v`. -/
def crossMatrix (b : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of
    ![![0, -b 2, b 1],
      ![b 2, 0, -b 0],
      ![-b 1, b 0, 0]]

@[simp]
lemma crossMatrix_apply (b : Fin 3 → K) (i j : Fin 3) :
    crossMatrix b i j =
      ![![0, -b 2, b 1], ![b 2, 0, -b 0], ![-b 1, b 0, 0]] i j := rfl

-- The matrix literals `![…]` are nested `vecCons`, so `mulVec` on them reduces to
-- `vecHead`/`vecTail` projections of the argument. These three `rfl` lemmas put such
-- projections back into ordinary indexing form.
@[simp] lemma vecHead_eq {n : ℕ} {K : Type*} (v : Fin (n + 1) → K) :
    Matrix.vecHead v = v 0 := rfl

@[simp] lemma vecHead_vecTail {K : Type*} (v : Fin 3 → K) :
    Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl

@[simp] lemma vecHead_vecTail_tail {K : Type*} (v : Fin 3 → K) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail v)) = v 2 := rfl

@[simp] lemma vecTail_apply_zero {K : Type*} (v : Fin 3 → K) :
    Matrix.vecTail v 0 = v 1 := rfl

@[simp] lemma vecTail_tail_apply_zero {K : Type*} (v : Fin 3 → K) :
    Matrix.vecTail (Matrix.vecTail v) 0 = v 2 := rfl

/-- `[b]ₓ v` is the cross product `b × v`. -/
lemma crossMatrix_mulVec (b v : Fin 3 → K) :
    crossMatrix b *ᵥ v =
      ![b 1 * v 2 - b 2 * v 1, b 2 * v 0 - b 0 * v 2, b 0 * v 1 - b 1 * v 0] := by
  ext i
  fin_cases i <;>
    simp [crossMatrix, Matrix.mulVec] <;> ring

/-- The defining property: `b` is orthogonal to every vector of the form `[b]ₓ v`. -/
theorem dot_crossMatrix_mulVec (b v : Fin 3 → K) :
    b ⬝ᵥ (crossMatrix b *ᵥ v) = 0 := by
  rw [crossMatrix_mulVec]
  simp [dotProduct, Fin.sum_univ_three]
  ring

/-- `b` spans the kernel of `[b]ₓ`. -/
@[simp]
theorem crossMatrix_mulVec_self (b : Fin 3 → K) : crossMatrix b *ᵥ b = 0 := by
  rw [crossMatrix_mulVec]
  ext i
  fin_cases i <;> simp <;> ring

/-- The cross-product matrix is skew-symmetric. -/
theorem transpose_crossMatrix (b : Fin 3 → K) :
    (crossMatrix b)ᵀ = -crossMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMatrix]

/-- A skew-symmetric matrix has vanishing determinant in odd dimension. -/
theorem det_crossMatrix (b : Fin 3 → K) : (crossMatrix b).det = 0 := by
  rw [Matrix.det_fin_three]
  simp [crossMatrix]
  ring

/-- If `b ≠ 0` then `[b]ₓ` is not the zero matrix. -/
theorem crossMatrix_ne_zero {b : Fin 3 → K} (hb : b ≠ 0) : crossMatrix b ≠ 0 := by
  intro h
  apply hb
  funext i
  fin_cases i
  · have h21 := congrFun (congrFun h 2) 1
    simpa [crossMatrix] using h21
  · have h02 := congrFun (congrFun h 0) 2
    simpa [crossMatrix] using h02
  · have h10 := congrFun (congrFun h 1) 0
    simpa [crossMatrix] using h10

end CertifiedConsensus
