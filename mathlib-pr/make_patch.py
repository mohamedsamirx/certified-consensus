#!/usr/bin/env python3
"""Regenerate the Mathlib patch for `Nat.choose_div_choose_le_pow_div_pow`.

Reads the pinned Mathlib copy under `.lake/packages/mathlib`, inserts the two
private lemmas and the public ratio bound after `Nat.pow_le_choose`, updates the
module docstring, and writes:

* `mathlib-pr/BoundsPatched.lean` — the patched file, for type-checking;
* `mathlib-pr/bounds.patch` — the unified diff, for submission.

The script asserts every anchor it relies on, so an upstream change to
`Bounds.lean` fails loudly instead of producing a silently wrong patch.
"""
from pathlib import Path
import difflib
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
src = root / ".lake/packages/mathlib/Mathlib/Data/Nat/Choose/Bounds.lean"
addition = (root / "mathlib-pr/addition.lean").read_text()

original = src.read_text()
text = original

summary_old = (
    "This file proves exponential bounds on binomial coefficients. We might want to add here the\n"
    "bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.\n"
)
summary_new = (
    "This file proves exponential and ratio bounds on binomial coefficients. We might want to add\n"
    "here the bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.\n"
)
assert summary_old in text, "module docstring summary changed upstream"
text = text.replace(summary_old, summary_new, 1)

pow_le_choose_bullet = (
    "* `Nat.pow_le_choose`: `(n + 1 - r)^r / r! ≤ n.choose r`. "
    "Beware of the fishy ℕ-subtraction.\n"
)
assert pow_le_choose_bullet in text, "`pow_le_choose` docstring bullet changed upstream"
ratio_bullet = (
    "* `Nat.choose_div_choose_le_pow_div_pow`: "
    "`m.choose k / n.choose k ≤ (m / n) ^ k` for `m ≤ n`\n"
)
text = text.replace(pow_le_choose_bullet, pow_le_choose_bullet + ratio_bullet, 1)

anchor = "    exact n.pow_sub_le_descFactorial r\n  exact mod_cast r.factorial_pos\n"
assert anchor in text, "end of `pow_le_choose` changed upstream"
text = text.replace(anchor, anchor + "\n" + addition.rstrip() + "\n", 1)

assert text.rstrip().endswith("end Nat"), "unexpected end of file"

patched = root / "mathlib-pr/BoundsPatched.lean"
patched.write_text(text)

diff = difflib.unified_diff(
    original.splitlines(keepends=True),
    text.splitlines(keepends=True),
    fromfile="a/Mathlib/Data/Nat/Choose/Bounds.lean",
    tofile="b/Mathlib/Data/Nat/Choose/Bounds.lean",
)
(root / "mathlib-pr/bounds.patch").write_text("".join(diff))
print(f"wrote {patched.relative_to(root)} and mathlib-pr/bounds.patch")

# Type-check the patched file against the pinned Mathlib.
proc = subprocess.run(
    ["lake", "env", "lean", str(patched.relative_to(root))],
    cwd=root,
    capture_output=True,
    text=True,
)
if proc.returncode != 0:
    sys.stderr.write(proc.stdout + proc.stderr)
    sys.exit("patched file failed to type-check")
print("patched file type-checks cleanly")
