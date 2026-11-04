#!/usr/bin/env python3
"""Exact finite audit of the GF(2) address-tree formula.

Run inside a Phi-Genesis checkout:
  python computational/higher_moments_z2/audit_gf2_pivot_tree.py --max-level 10
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from phi_genesis.higher_moments_z2 import build_generation_flux_problem


def words_at_level(level: int) -> list[str]:
    out: list[str] = []
    def visit(word: str) -> None:
        if len(word) < level - 1:
            for digit in "012":
                visit(word + digit)
        out.append(word)
    visit("")
    return out


def parent(word: str, level: int) -> str:
    if len(word) < level - 1:
        return word + "0" + "1" * (level - len(word) - 2)
    pos = word.rfind("2")
    return word[:pos] if pos >= 0 else "R"


def terminal_parent(word: str) -> str | None:
    pos = word.rfind("0")
    if pos >= 0 and all(ch == "1" for ch in word[pos + 1 :]):
        return word[:pos]
    return None


def audit(level: int) -> dict[str, int]:
    problem = build_generation_flux_problem(level)
    words = words_at_level(level)
    assert len(words) == len(problem.holes)
    assert all(problem.holes[i][3] == level - len(w) for i, w in enumerate(words))

    edge_index = {edge: i for i, edge in enumerate(problem.edges)}
    original: dict[str, int] = {}
    for word, boundary in zip(words, problem.boundaries):
        bits = 0
        for edge in boundary:
            bits ^= 1 << edge_index[tuple(sorted(edge))]
        original[word] = bits

    transformed: dict[str, int] = {}
    for word in words:
        bits = original[word]
        if len(word) < level - 1:
            for digit in "012":
                bits ^= original[word + digit]
        transformed[word] = bits

    columns = [0] * len(problem.edges)
    for row, word in enumerate(words):
        bits = transformed[word]
        while bits:
            low = bits & -bits
            columns[low.bit_length() - 1] |= 1 << row
            bits ^= low

    dual: list[tuple[int, str, str]] = []
    parallel: dict[tuple[str, str], list[int]] = defaultdict(list)
    for edge_id, signature in enumerate(columns):
        degree = signature.bit_count()
        if degree == 0:
            continue
        if degree > 2:
            raise AssertionError(("dual degree exceeds two", level, edge_id, degree))
        endpoints: list[str] = []
        bits = signature
        while bits:
            low = bits & -bits
            endpoints.append(words[low.bit_length() - 1])
            bits ^= low
        if degree == 1:
            endpoints.append("R")
        a, b = sorted(endpoints)
        dual.append((edge_id, a, b))
        parallel[(a, b)].append(edge_id)

    candidate: dict[str, int] = {}
    for word in words:
        pair = tuple(sorted((word, parent(word, level))))
        if pair not in parallel:
            raise AssertionError(("missing address-parent dual edge", level, word, pair))
        candidate[word] = min(parallel[pair])
    chosen = set(candidate.values())
    if len(chosen) != len(words):
        raise AssertionError("candidate edges are not distinct")

    nodes = words + ["R"]
    index = {word: i for i, word in enumerate(nodes)}
    dsu = list(range(len(nodes)))
    def find(x: int) -> int:
        while dsu[x] != x:
            dsu[x] = dsu[dsu[x]]
            x = dsu[x]
        return x
    def union(a: str, b: str) -> bool:
        x, y = find(index[a]), find(index[b])
        if x == y:
            return False
        dsu[x] = y
        return True

    pair_by_id = {k: (a, b) for k, a, b in dual if k in chosen}
    for edge_id in sorted(chosen):
        if not union(*pair_by_id[edge_id]):
            raise AssertionError(("candidate contains a cycle", level, edge_id))
    if len({find(i) for i in range(len(nodes))}) != 1:
        raise AssertionError("candidate tree is disconnected")

    greedy_dsu = list(range(len(nodes)))
    def gfind(x: int) -> int:
        while greedy_dsu[x] != x:
            greedy_dsu[x] = greedy_dsu[greedy_dsu[x]]
            x = greedy_dsu[x]
        return x
    greedy: set[int] = set()
    for edge_id, a, b in sorted(dual):
        x, y = gfind(index[a]), gfind(index[b])
        if x != y:
            greedy_dsu[x] = y
            greedy.add(edge_id)
    assert greedy == chosen
    assert chosen == set(problem.system._basis)

    for word in words:
        if len(word) < level - 1:
            cut = original[word] ^ original[word + "0"] ^ original[word + "1"]
        else:
            v = terminal_parent(word)
            cut = original[word] if v is None else (
                original[word] ^ original[v] ^ original[v + "0"] ^ original[v + "1"]
            )
        least = (cut & -cut).bit_length() - 1
        if cut == 0 or least != candidate[word]:
            raise AssertionError(("cut minimum mismatch", level, word, least, candidate[word]))

    for generation in range(1, level + 1):
        solution = 0
        for word, edge_id in candidate.items():
            if len(word) < level - 1:
                bit = generation == level - len(word)
            else:
                bit = generation == 1
                v = terminal_parent(word)
                if v is not None:
                    bit = bool(bit) ^ (generation == level - len(v))
            if bit:
                solution |= 1 << edge_id
        for word in words:
            lhs = (original[word] & solution).bit_count() & 1
            rhs = int(level - len(word) == generation)
            if lhs != rhs:
                raise AssertionError(("closed-form solution mismatch", level, generation, word))

    return {
        "level": level,
        "vertices": len(problem.vertices),
        "edges": len(problem.edges),
        "holes": len(problem.holes),
        "dual_edges": len(dual),
        "tree_edges": len(chosen),
        "pivot_match": 1,
        "cut_minimum_match": 1,
        "generation_basis_rhs_checked": level,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-level", type=int, default=8)
    args = parser.parse_args()
    if args.max_level < 1:
        parser.error("--max-level must be positive")
    for level in range(1, args.max_level + 1):
        print(audit(level), flush=True)


if __name__ == "__main__":
    main()
