# Design decisions

A record of what was chosen, what was rejected, and why. Written so a reviewer can
reconstruct the reasoning without reading the whole proof development.

---

## 1. Formalize the guarantee, not the algorithm

**Decision.** The library proves *what the iteration count promises*, rather than
implementing RANSAC and proving it terminates.

**Alternative.** A verified sampler + scorer + model fitter in Lean, extracted to C.

**Why.** The sampled model is uniformly drawn by assumption in every RANSAC paper; the
only non-trivial formal content in the loop is the probability that a minimal sample is
all-inlier. A verified sampler would add thousands of lines of data-structure proofs and
zero insight, and would be unusable from Python/C++ anyway.

**Cost.** The library does not certify that a particular implementation samples
uniformly. That assumption is stated in the README and is the honest boundary.

---

## 2. Exact hypergeometric probability, and honest numbers

**Decision.** Prove `P(all inliers) = C(pn,k)/C(n,k)` and `C(pn,k)/C(n,k) ≤ p^k`.

**Alternative.** Formalize the 2025 empirical critique only, without a closed form.

**Why.** A closed form makes the correction a one-line change in any implementation.
The inequality gives the direction of the error: the textbook rule is always optimistic,
never conservative.

**Cost, stated plainly.** The correction is **1.04×–5.47×**, not orders of magnitude.
It is largest when `n` is small and `k` is close to `pn` — exactly the hard cases. The
README prints these numbers rather than implying a bigger effect.

---

## 3. Rational arithmetic in the checker

**Decision.** `Point := Fin 3 → ℚ`, and every check is exact.

**Alternative.** `Float`, matching what OpenCV/COLMAP actually produce.

**Why.** Floats are rationals. Parsing a decimal string or a binary float as an exact
rational loses nothing, and the resulting certificate is kernel-checked rather than
"checked to 6 decimal places". It also removes the entire question of tolerances from
the trusted base.

**Cost.** Real correspondences never satisfy `x'ᵀFx = 0` exactly, so the exact checker
rejects real data. This is a genuine limitation — see item 9.

---

## 4. Rank two by minors, not by `Matrix.rank`

**Decision.** Certify rank two as `det F = 0` plus at least one non-zero 2×2 minor.

**Alternative.** `Matrix.rank F = 2`.

**Why.** `Matrix.rank` is defined through linear maps and `Module.rank`; transporting it
along `ℚ → ℝ` needs a scalar-extension argument that is fiddly and adds nothing to the
certificate. The minors are nine rational numbers, each checkable by `decide`-free
computation, and the soundness proof is `det = 0` + "some minor non-zero ⇒ rank ≥ 2".

**Cost.** The certificate must list a minor witness. That is a feature: the witness is
checkable by hand.

---

## 5. Explicit `crossMatrix`, not `Projectivization.cross`

**Decision.** Define the 3×3 skew matrix directly on `Fin 3 → K`.

**Alternative.** Mathlib's `Projectivization.cross` on `ℙ K (Fin 3 → K)`.

**Why.** The theorem is about a specific matrix identity, `F = [b]ₓ A`, that must hold
entrywise. Working in projective space would require constantly transporting across
`mk`/`rep` and proving non-zero side conditions, for no gain in the statement.

**Cost.** We do not connect to Mathlib's projective geometry API. Upstreaming the
skew-matrix lemmas is therefore easier than upstreaming the projective ones.

---

## 6. The affine camera pair `[I | 0]`, `[A | b]`

**Decision.** State the epipolar construction for cameras `P₁ = [I | 0]`, `P₂ = [A | b]`.

**Alternative.** Two arbitrary `3×4` matrices of rank 3.

**Why.** Every camera pair reduces to this form by a projective change of coordinates,
so no generality is lost for the construction, and the algebra stays entrywise. The
general case would require a proof that such a reduction exists — real work, no new
insight.

**Cost.** The statement is not literally "for all camera pairs"; the README says
"without loss of generality, after a projective change of coordinates".

---

## 7. The a-contrario principle in abstract form

**Decision.** Prove the finite expectation bound: if `m` tests each fire on at most an
`ε/m` fraction of the null model, the expected number of false alarms is at most `ε`.

**Alternative.** Instantiate the null model for epipolar geometry — random points in an
image rectangle, distance-to-line statistics.

**Why.** The geometric instantiation needs a measure on image points and a
distance-to-line distribution; that is a paper on its own, and the *principle* is the
transferable result. Stating it finitely keeps it exact and reusable.

**Cost.** No numerical NFA value for a specific dataset. The theorem is a schema, not a
calibrated test — stated as such.

---

## 8. No eight-point algorithm

**Decision.** Omit the correctness proof of the eight-point solver.

**Alternative.** Prove that the null space of the design matrix is one-dimensional and
equals the true `F` under rank-8 genericity.

**Why.** It needs rank–nullity over a stacked design matrix plus a genericity argument,
and it certifies a solver nobody in this library runs. The epipolar *construction* is
what the checker validates.

**Cost.** The library does not claim "the eight-point algorithm is correct". It claims
`F = [b]ₓA` is the fundamental matrix of the pair, and that a given `F` can be checked.

---

## 9. Synthetic exact data for the demo

**Decision.** The demo certificate uses 24 correspondences generated as `x' = A x + λb`
in exact rationals.

**Alternative.** Real SIFT correspondences from an image pair.

**Why.** With exact data the certificate is genuinely exact, so the demo exercises the
soundness theorem rather than an error bound. Mixing in real noise would require the
tolerance layer (not built) to avoid a misleading "rejected" verdict.

**Cost.** A reviewer can object that the demo proves the checker works on data
constructed to satisfy it. That objection is correct. The honest next step is a
certified-tolerance mode, `|x'ᵀFx| ≤ δ`, with `δ` explicit in the certificate.

**Implemented.** `checkEpipolarTol` and `checkEpipolarTol_sound`; `certify` accepts
`tol <rat>` after the mode token. `data/noisy_certificate.txt` sets `δ` to the smallest
`1/1000` multiple above the observed maximum residual, and the CLI prints that tightening
`δ` to half the maximum is rejected — evidence the certificate is tight, not generous.

---

## 10. No `#certify_epipolar` elaborator (yet)

**Decision.** Ship the checker as a compiled executable, not an elaborator command.

**Why.** Kernel reduction of `Rat` arithmetic is unreliable in this toolchain — `decide`
gets stuck on `Rat.num` / `Nat.gcd` — so an elaborator that produced `by decide` proofs
would not work. A compiled executable gives the same verdict without pretending the
computation is kernel-checked.

**Cost.** The demo is one shell command rather than one Lean line. The soundness theorem
still connects the executable's answer to the mathematical statement, because the
executable is a direct transcription of `checkEpipolar`.

---

## 11. Upstreaming candidates

`choose_ratio_lt_pow` (and its `descFactorial` machinery) and `expected_false_alarms_le`
are stated with no project-specific definitions and would fit Mathlib. They were not
submitted. A reviewer should treat "Mathlib-ready" as a claim about shape, not about
acceptance.
