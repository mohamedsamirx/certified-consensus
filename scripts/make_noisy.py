#!/usr/bin/env python3
"""Generate a noisy stereo certificate for the tolerance-mode demo.

Camera pair: P1 = [I | 0], P2 = [A | b] with A a 90-degree rotation and
b = (1/2, 1/10, 0).  Exact correspondences satisfy x' = A x + b, hence
x'^T F x = 0 with F = [b]_x A.  We then perturb every observed coordinate by a
small rational and record the largest residual exactly, so the certificate
threshold is not guessed.
"""
from fractions import Fraction as F
from pathlib import Path
import math

A = [[0, -1, 0], [1, 0, 0], [0, 0, 1]]
b = [F(1, 2), F(1, 10), F(0)]


def cross(b):
    return [
        [0, -b[2], b[1]],
        [b[2], 0, -b[0]],
        [-b[1], b[0], 0],
    ]


def matmul(M, N):
    return [[sum(M[i][k] * N[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def matvec(M, v):
    return [sum(M[i][k] * v[k] for k in range(3)) for i in range(3)]


def dot(u, v):
    return sum(a * c for a, c in zip(u, v))


def fmt(q):
    return f"{q.numerator}/{q.denominator}" if q.denominator != 1 else str(q.numerator)


Fm = matmul(cross(b), A)

# Deterministic perturbations, in units of 1/1000.
deltas = [3, -5, 7, -2, 4, -6, 1, -3, 5, -4, 2, -7,
          6, -1, 8, -2, 3, -5, 4, -6, 2, -8, 5, -3]

base = [(F(1, 10), F(2, 10)), (F(3, 10), F(1, 10)), (F(5, 10), F(4, 10)),
        (F(7, 10), F(3, 10)), (F(2, 10), F(7, 10)), (F(6, 10), F(8, 10)),
        (F(9, 10), F(1, 10)), (F(4, 10), F(5, 10)), (F(8, 10), F(2, 10)),
        (F(1, 10), F(9, 10)), (F(3, 10), F(6, 10)), (F(7, 10), F(5, 10)),
        (F(2, 10), F(3, 10)), (F(6, 10), F(1, 10)), (F(9, 10), F(7, 10)),
        (F(4, 10), F(9, 10)), (F(8, 10), F(6, 10)), (F(1, 10), F(5, 10)),
        (F(3, 10), F(9, 10)), (F(7, 10), F(2, 10)), (F(2, 10), F(8, 10)),
        (F(6, 10), F(4, 10)), (F(9, 10), F(3, 10)), (F(4, 10), F(1, 10))]

rows = []
max_res = F(0)
for t, (u, v) in enumerate(base):
    x = [u, v, F(1)]
    xp = matvec(A, x)
    xp = [xp[0] + b[0], xp[1] + b[1], xp[2] + b[2]]
    du, dv, dup, dvp = (F(deltas[(4 * t + k) % len(deltas)], 1000) for k in range(4))
    u2, v2, up2, vp2 = u + du, v + dv, xp[0] / xp[2] + dup, xp[1] / xp[2] + dvp
    r = dot([up2, vp2, F(1)], matvec(Fm, [u2, v2, F(1)]))
    max_res = max(max_res, abs(r))
    rows.append((u2, v2, up2, vp2))

# Round the threshold up to a readable multiple of 1/1000.
nice = F(math.ceil(max_res * 1000), 1000)

lines = ["# Noisy stereo certificate: F = [b]_x A, observations perturbed by up to 8/1000.",
         "# Exact F is known; the threshold below is the smallest 1/1000 multiple above",
         "# the largest observed residual, so it is not generous by construction.",
         "A", f"tol {fmt(nice)}"]
for row in A:
    lines.append(" ".join(fmt(F(x)) for x in row))
lines.append("b")
lines.append(" ".join(fmt(x) for x in b))
lines.append(str(len(rows)))
for r in rows:
    lines.append(" ".join(fmt(x) for x in r))

out = Path(__file__).resolve().parent.parent / "data" / "noisy_certificate.txt"
out.write_text("\n".join(lines) + "\n")
print(f"max |residual| = {fmt(max_res)} ≈ {float(max_res):.6f}")
print(f"threshold      = {fmt(nice)} ≈ {float(nice):.6f}")
print(f"wrote {out}")
