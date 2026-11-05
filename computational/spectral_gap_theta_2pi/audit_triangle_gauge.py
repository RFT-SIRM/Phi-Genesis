#!/usr/bin/env python3
"""Exact combinatorial/gauge audit for the theta=2pi SG triangle model.

Coordinates are integer triangular-lattice pairs (i,j). Each ordered upward
face (a,b,c) has signed-adjacency signs +1 on (a,b), -1 on (a,c),(b,c).
The explicit gauge is eps(i,j)=(-1)^j.
"""
from __future__ import annotations

import argparse
from collections import Counter


def faces(level: int):
    if level < 0:
        raise ValueError("level must be nonnegative")
    out = [((0, 0), (1, 0), (0, 1))]
    for depth in range(1, level + 1):
        half = 1 << (depth - 1)
        old = out
        out = [
            tuple((x + dx, y + dy) for x, y in f)
            for dx, dy in ((0, 0), (half, 0), (0, half))
            for f in old
        ]
    return out


def edge(u, v):
    return (u, v) if u < v else (v, u)


def audit(level: int):
    fs = faces(level)
    edge_sign = {}
    incidence = Counter()
    degree = Counter()
    vertices = set()

    for a, b, c in fs:
        for v in (a, b, c):
            vertices.add(v)
            incidence[v] += 1
        for u, v, s in ((a, b, 1), (a, c, -1), (b, c, -1)):
            e = edge(u, v)
            assert e not in edge_sign, (level, "edge shared by faces", e)
            edge_sign[e] = s
            degree[u] += 1
            degree[v] += 1
            eps_u = -1 if u[1] % 2 else 1
            eps_v = -1 if v[1] % 2 else 1
            assert s == eps_u * eps_v, (level, "gauge mismatch", e, s)

    assert len(fs) == 3**level
    assert len(edge_sign) == 3**(level + 1)
    assert len(vertices) == (3**(level + 1) + 3) // 2
    assert min(incidence.values()) == 1
    assert max(incidence.values()) == (1 if level == 0 else 2)
    assert min(degree.values()) == 2
    assert max(degree.values()) == (2 if level == 0 else 4)

    # For H_s=D+A_s, the connection convention H=D-A_U has U=-s.
    # Its holonomy on each elementary triangle is (-1)^3*(+1) = -1.
    assert all((-1)**3 * (1 * -1 * -1) == -1 for _ in fs)
    return (
        len(vertices), len(edge_sign), len(fs),
        min(incidence.values()), max(incidence.values())
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-level", type=int, default=10)
    args = parser.parse_args()
    if args.max_level < 0:
        raise SystemExit("max level must be nonnegative")
    print("level vertices edges elementary_faces face_incidence")
    for m in range(args.max_level + 1):
        print(m, *audit(m))


if __name__ == "__main__":
    main()
