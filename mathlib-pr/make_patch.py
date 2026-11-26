#!/usr/bin/env python3
"""Regenerate the Mathlib patch for `Nat.choose_div_choose_le_pow_div_pow`.

Reads the pinned Mathlib copy under `.lake/packages/mathlib`, inserts the
additional imports and the two lemmas, writes the result to
`mathlib-pr/BoundsPatched.lean` (for type-checking) and the unified diff to
`mathlib-pr/bounds.patch` (for submission).
"""
from pathlib import Path
import difflib

root = Path(__file__).resolve().parent.parent
src = root / ".lake/packages/mathlib/Mathlib/Data/Nat/Choose/Bounds.lean"
addition = (root / "mathlib-pr/addition.lean").read_text()

text = src.read_text()
lines = text.splitlines(keepends=True)

# Replace the public-import block with a sorted one that also covers the lemmas.
imports = [
    "public import Mathlib.Algebra.BigOperators.Group.Finset.Basic\n",
    "public import Mathlib.Algebra.Field.Defs\n",
    "public import Mathlib.Algebra.Order.BigOperators.Group.Finset\n",
    "public import Mathlib.Algebra.Order.Ring.Defs\n",
    "public import Mathlib.Data.Nat.Cast.Order.Basic\n",
    "public import Mathlib.Data.Nat.Choose.Basic\n",
    "public import Mathlib.Data.Nat.Factorial.BigOperators\n",
]
start = next(i for i, l in enumerate(lines) if l.startswith("public import"))
end = max(i for i, l in enumerate(lines) if l.startswith("public import"))
lines[start:end + 1] = imports
text = "".join(lines)

assert text.rstrip().endswith("end Nat")
text = text.rstrip()[: -len("end Nat")] + addition + "\nend Nat\n"

(root / "mathlib-pr/BoundsPatched.lean").write_text(text)
diff = difflib.unified_diff(
    src.read_text().splitlines(keepends=True),
    text.splitlines(keepends=True),
    fromfile="a/Mathlib/Data/Nat/Choose/Bounds.lean",
    tofile="b/Mathlib/Data/Nat/Choose/Bounds.lean",
)
(root / "mathlib-pr/bounds.patch").write_text("".join(diff))
print("wrote mathlib-pr/BoundsPatched.lean and mathlib-pr/bounds.patch")
