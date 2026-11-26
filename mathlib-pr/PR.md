# Mathlib PR

**Title**

```
feat(Data/Nat/Choose/Bounds): add ratio bound for binomial coefficients
```

**Body**

```markdown
## Summary

Add `Nat.choose_div_choose_le_pow_div_pow`: for `m ≤ n` and any `k`,

  `m.choose k / n.choose k ≤ (m / n) ^ k`

over a `Semifield α` with `[LinearOrder α]` and `[IsStrictOrderedRing α]`.

## Motivation

`m.choose k / n.choose k` is the probability that a uniformly chosen `k`-subset
of an `n`-element set lies inside a fixed `m`-element subset — sampling `k`
elements without replacement. The bound `(m/n)^k` is the corresponding
with-replacement estimate, so this lemma makes the comparison available inside
Mathlib.

Equality holds when `k ≤ 1`, when `m = 0`, and when `m = n` with `k ≤ n`; the
inequality is strict when `0 < m < n` and `2 ≤ k`.

## Relationship to existing bounds

`Nat.choose_le_pow_div` and `Nat.pow_le_choose` combine to give

  `m.choose k / n.choose k ≤ (m / (n + 1 - k)) ^ k`

for `k ≤ n`. Since `n + 1 - k ≤ n`, this estimate is at least `(m / n) ^ k`, and
strictly larger when `0 < m < n` and `2 ≤ k ≤ n`; the new bound is therefore
sharper in that range.

## Proof

The private lemma `descFactorial_mul_pow_le` is proved by induction on `k` using
`Nat.descFactorial_succ`, splitting `k ≤ m` from `m < k`. Multiplying by `k!`
and cancelling (`Nat.descFactorial_eq_factorial_mul_choose`) gives the integer
form, `choose_mul_pow_le`, and `div_le_div_iff₀` transfers it to the field. The
case `m < k` uses `Nat.choose_eq_zero_of_lt`.

No new imports; no changes outside this file.

## Testing

- `lake build Mathlib.Data.Nat.Choose.Bounds` succeeds.
- `#print axioms Nat.choose_div_choose_le_pow_div_pow` reports only
  `propext`, `Classical.choice`, `Quot.sound`.
- Checked against brute force for `0 ≤ m ≤ n ≤ 50`, `0 ≤ k ≤ 120` in `ℚ`.
- The pinned `Bounds.lean` is byte-identical to `mathlib4` master at the time
  of writing, so the patch applies without rebasing.
```

## Files

| File | Purpose |
|---|---|
| `addition.lean` | the exact text inserted into `Bounds.lean` |
| `make_patch.py` | regenerates the patched file and diff from the pinned Mathlib |
| `BoundsPatched.lean` | full patched file, type-checked |
| `bounds.patch` | submission diff (docstring bullet + three declarations) |

## Submission

```bash
git clone https://github.com/leanprover-community/mathlib4
cd mathlib4
git switch -c choose-ratio-bound
git apply /path/to/bounds.patch
lake exe cache get
lake build Mathlib.Data.Nat.Choose.Bounds
lake exe lint Mathlib.Data.Nat.Choose.Bounds
git add -A && git commit -m "feat(Data/Nat/Choose/Bounds): add ratio bound for binomial coefficients"
git push -u origin choose-ratio-bound
```

## Review risks

| Risk | Mitigation |
|---|---|
| Duplicate | No `choose_div_choose` ratio lemma found by grep; the pinned file is byte-identical to master |
| Generality | Stated for all `k`, not just `k ≤ m`; contexts match the file |
| Import weight | Zero new imports; the helper avoids `Finset`/`BigOperators` |
| Placement | Fits the module's stated purpose ("exponential and ratio bounds") |
| Latency | 2600+ open PRs; expect weeks |
