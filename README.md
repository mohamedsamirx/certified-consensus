# Certified Consensus

> RANSAC's stopping rule promises a confidence it does not deliver.

A Lean 4 library that machine-checks the exact probabilistic guarantee behind robust
estimation, and validates a fundamental matrix on real correspondences by exact rational
arithmetic.

Everything here is proved; nothing is `sorry`. Every headline theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

---

## The result

With inlier ratio `p`, sample size `k`, and `n` correspondences, every implementation
computes the per-trial success probability as

```
p ^ k
```

and stops after `⌈log(1 − η) / log(1 − p^k)⌉` iterations. But a minimal sample is drawn
**without replacement**, so the exact probability is the hypergeometric one:

```
P(all inliers) = C(pn, k) / C(n, k) = ∏_{i<k} (pn − i) / (n − i)
```

which is strictly smaller than `p^k` for `k ≥ 2`. The classical rule is therefore
optimistic: it always stops too early, and the promised confidence is never delivered.

The deficit is small on easy problems and large on hard ones:

| `n` | `k` | `p` | `p^k` | exact | ratio | `N` classic | `N` exact |
|----:|----:|----:|------:|------:|------:|------------:|----------:|
| 1000 | 8 | 0.30 | 6.56e-5 | 6.14e-5 | 1.07× | 70,188 | 74,981 |
| 100 | 8 | 0.30 | 6.56e-5 | 3.15e-5 | 2.09× | 70,188 | 146,415 |
| 50 | 8 | 0.30 | 6.56e-5 | 1.20e-5 | 5.47× | 70,188 | 384,212 |
| 1000 | 5 | 0.20 | 3.20e-4 | 3.07e-4 | 1.04× | 14,389 | 14,982 |
| 500 | 4 | 0.10 | 1.00e-4 | 8.95e-5 | 1.12× | 46,050 | 51,450 |
| 200 | 4 | 0.05 | 6.25e-6 | 3.25e-6 | 1.93× | 736,825 | 1,418,499 |

Confidence `η = 0.99`. The correction never shrinks; it grows as `n` shrinks and `k`
grows, which is exactly the regime where RANSAC is used hardest.

## What is proved

| Theorem | Statement |
|---|---|
| `consensus_ratio` | the all-inlier probability is `C(⎣pn⎦, k) / C(n, k)` |
| `choose_ratio_le_pow` | `C(m,k)/C(n,k) ≤ (m/n)^k` for `m ≤ n` |
| `choose_ratio_lt_pow` | strict, for `m < n` and `k ≥ 2` |
| `pow_le_one_sub_of_ge_log_div_log` | the corrected iteration count reaches confidence `η` |
| `folklore_iterations_le_exact` | given `P ≤ p^k`, the textbook count never exceeds the exact count |
| `ransac_iterations_le_exact` | the same, instantiated with `P = C(m,k)/C(n,k)` and `p = m/n` |
| `expected_false_alarms_le` | a contrario: `m` tests calibrated at `ε/m` give expected false alarms `≤ ε` |
| `epipolar_constraint` | `x'ᵀ F x = 0` for `F = [b]ₓ A` and every world point |
| `transpose_mulVec_epipolar` | `Fᵀ b = 0` — the baseline is the second epipole |
| `mulVec_epipolar_of_eq` | `A e = b → F e = 0` — the first epipole is `A⁻¹ b` |
| `det_epipolar` | `det F = 0` |
| `checkEpipolar_sound` | a passing certificate implies singularity, a nonzero minor, and exact residuals |
| `checkEpipolarTol_sound` | a passing tolerant certificate implies every residual is `≤ δ` |

`#print axioms checkEpipolar_sound` → `[propext, Classical.choice, Quot.sound]`.

## The checker

Image coordinates are decimals; decimals are rationals; the conversion is exact. A
passing certificate is kernel-checked with no floating-point trust and **no threshold**:

```
$ lake exe certify data/stereo_certificate.txt
certified-consensus — exact rational certificate
input: data/stereo_certificate.txt
fundamental matrix F =
0  0  1/10
0  0  -1/2
1/2  1/10  0

points: 24
epipolar residuals: 24/24 exactly zero
rank two: det F = 0, minor rows (0,2) cols (0,2) = -1/20 ≠ 0

CERTIFIED — every check passed exactly
negative control: perturbing u by 1/1000 is rejected: true
```

The input file is a camera pair `(A, b)` or a matrix `F`, plus correspondences; see
`data/stereo_certificate.txt` and the header of `Main.lean` for the format.

Real correspondences are never exact, so the checker has a certified tolerance mode:
fix a rational `δ` and certify `|x'ᵀFx| ≤ δ` for every correspondence.

```
$ lake exe certify data/noisy_certificate.txt
...
tolerance: δ = 3/500
max |residual| = 29/5000
exact check (δ = 0) accepts: false
rank two: det F = 0, minor rows (0,2) cols (0,2) = -1/20 ≠ 0

CERTIFIED within tolerance — rank and residuals verified
tightening δ to 29/10000 is rejected: true
```

The threshold in `data/noisy_certificate.txt` is the smallest multiple of `1/1000` above
the observed maximum residual, so it is tight by construction rather than generous.

## Kernel-time certificates

The checker also runs as a command. It evaluates the matrix at elaboration time,
reads the correspondences, and **fails the build** if the certificate is invalid:

```lean
#certify_epipolar
  !![0, 0, 1/10; 0, 0, -1/2; 1/2, 1/10, 0]
  from "data/stereo_points.txt"

#certify_epipolar
  !![0, 0, 1/10; 0, 0, -1/2; 1/2, 1/10, 0]
  from "data/noisy_points.txt" tol 3/500
```

Replacing the matrix by the identity produces `rank two: false` and
`error: REJECTED — F is not rank two (det = 1)`. A correspondence outside the tolerance
produces `REJECTED — correspondence i has residual r, outside tolerance δ` instead, so the
diagnostic names the check that failed and the point that caused it. The same file cannot be
compiled into a false claim.

Relative paths resolve against the directory of the source file, not the process working
directory, so the command behaves identically under `lake build`, `lake env lean`, and an
editor. `tests/PathResolve.lean` exercises exactly that case.

## What is checked, and what is assumed

Checked, in full:

- the counting identity and its strict inequality;
- the iteration bound, including the ceiling;
- the epipolar identity for the normalized pair `P₁ = [I | 0]`, `P₂ = [A | b]`;
- soundness of the certificate checker, over `ℚ` and lifted to `ℝ`.

Assumed, and stated as hypotheses rather than hidden:

- the probabilistic model: uniform `k`-subsets and independent trials;
- normalization: every camera pair can be brought to `P₁ = [I | 0]` by a projective change
  of coordinates — standard, and not formalized here;
- rank two is witnessed by a nonzero `2 × 2` minor, which the certificate must supply.

## Layout

```
CertifiedConsensus/
  Basic.lean       cross product matrix and its identities
  Exact.lean       counting, hypergeometric ratio, strict bound
  Stopping.lean    log/ceiling iteration rule
  Epipolar.lean    F = [b]ₓA, epipoles, singularity
  Checker.lean     exact ℚ checker + soundness
  AContrario.lean  finite NFA bound
  Parse.lean       shared rational/token parsing
  Command.lean     `#certify_epipolar` elaborator command
Main.lean          `certify` executable
Demo.lean          symbolic worked example
Examples.lean      kernel-time certificate commands
tests/             path-resolution and rejection tests
data/              camera pair + 24 exact correspondences, and a noisy variant
scripts/           axiom audit, end-to-end verification, noisy-data generator
DESIGN.md          decision log: what was chosen, rejected, and why
```

## Build

```bash
git clone https://github.com/mohamedsamirx/certified-consensus
cd certified-consensus
elan toolchain install leanprover/lean4:v4.37.0-rc1
lake exe cache get        # prebuilt Mathlib, roughly 7 GB
lake build
lake exe certify data/stereo_certificate.txt
```

With the cache the first build takes minutes; without it, Mathlib compiles for hours.
`scripts/verify.sh` runs the build, the axiom audit, both certificates, the elaborator
command, and the rejection test in one step.

## Status

- Mathlib candidates: `choose_ratio_lt_pow` (a `Nat.choose` product bound) and
  `expected_false_alarms_le` (a finite union-bound principle).
- Next: homography and PnP instances. See `DESIGN.md` for why each was deferred.

## References

- Exact RANSAC stopping: *Fixing the RANSAC Stopping Criterion* (2025), which observes
  that the classical `p^k` rule undersamples.
- A contrario detection: Desolneux, Moisan, Morel, *From Gestalt Theory to Image
  Analysis*; AC-RANSAC / ORSA (Moisan–Stival).
- Two-view geometry: Hartley & Zisserman, *Multiple View Geometry*, Chapter 9.
