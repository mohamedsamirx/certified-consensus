#!/usr/bin/env python3
"""Extract a points-only certificate from a CLI certificate.

The `#certify_epipolar` command takes the fundamental matrix inline, so it only
needs the correspondences. This script strips the camera/matrix header and writes
`<count> <4*count rationals>`.
"""
import sys
from fractions import Fraction


def tokens(path):
    out = []
    for line in open(path):
        line = line.split("#", 1)[0]
        out.extend(line.split())
    return out


def main(src, dst):
    toks = tokens(src)
    mode = toks[0]
    if mode == "A":
        header = 12  # 9 matrix entries + 3 baseline entries
    elif mode == "F":
        header = 9
    else:
        raise SystemExit(f"unknown mode {mode!r}")
    rest = toks[1:]
    if rest and rest[0] == "tol":
        rest = rest[2:]
    if mode == "A":
        # 9 matrix entries, then the literal `b`, then 3 baseline entries
        assert rest[9] == "b", rest[9]
        header = 13
    else:
        header = 9
    n = int(rest[header])
    coords = rest[header + 1: header + 1 + 4 * n]
    if len(coords) != 4 * n:
        raise SystemExit("truncated certificate")
    with open(dst, "w") as f:
        f.write(f"# Points-only certificate extracted from {src}\n")
        f.write(f"{n}\n")
        for i in range(0, len(coords), 4):
            f.write(" ".join(coords[i:i + 4]) + "\n")
    print(f"{dst}: {n} correspondences")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
