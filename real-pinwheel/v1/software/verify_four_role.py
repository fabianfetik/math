#!/usr/bin/env python3
"""Check the four-role real-simplex cover using only mathematical data.

Periodic caps are recomputed from cyclic occurrence spans. Construction
regions are rederived before the exact split tree and its rational
contradiction witnesses are checked. No assignment document is an input.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from functools import reduce
from math import gcd, lcm
from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1] / "data/four-role"
D = F(5, 6)


def need(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def load(path: Path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            need(key not in result, f"duplicate JSON key: {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique)


def word_bounds(word: str, roles: int):
    need(isinstance(word, str) and set(word) == {str(i) for i in range(1, roles + 1)},
         "word has missing or invalid role labels")
    period = len(word)
    caps = []
    for label in range(1, roles + 1):
        positions = [t for t, c in enumerate(word) if c == str(label)]
        count = len(positions)
        doubled = positions + [t + period for t in positions]
        mean = F(period, count)
        residual = F(0)
        for rank in range(1, count):
            span = max(doubled[j + rank] - doubled[j] for j in range(count))
            residual = max(residual, F(span - 1, rank))
        caps.append((1 / max(mean, residual), residual >= mean))
    return caps  # The Boolean is True exactly for an open rate cap.


def normalize(coefficients, rhs, strict):
    need(type(strict) is bool, "invalid inequality strictness flag")
    values = [F(x) for x in coefficients] + [F(rhs)]
    denominator = lcm(*(x.denominator for x in values))
    integers = [int(x * denominator) for x in values]
    divisor = reduce(gcd, (abs(x) for x in integers)) or 1
    return tuple(x // divisor for x in integers) + (strict,)


def reduce4(coefficients, rhs, strict=False):
    need(len(coefficients) == 4, "wrong load dimension")
    return normalize([F(coefficients[i]) - coefficients[3] for i in range(3)],
                     F(rhs) - D * coefficients[3], strict)


def prefix_caps(caps):
    result = []
    for cap, strict in caps:
        if result:
            previous, previous_strict = result[-1]
            if previous < cap:
                cap, strict = previous, previous_strict
            elif previous == cap:
                strict = strict or previous_strict
        result.append((cap, strict))
    return result


def from_caps(caps):
    need(len(caps) == 4, "wrong cap dimension")
    return [reduce4([int(j == i) for j in range(4)], cap, strict)
            for i, (cap, strict) in enumerate(prefix_caps(caps))]


def expected_region(region, catalogue):
    provenance = region["provenance"]
    kind = provenance["kind"]
    words, sources = catalogue["four_role_words"], catalogue["three_role_words"]
    if kind == "word":
        index = provenance["index"]
        need(type(index) is int and 1 <= index <= len(words), "invalid catalogue word index")
        need(provenance["word"] == words[index - 1], "word provenance mismatch")
        return from_caps(word_bounds(words[index - 1], 4))
    if kind == "direct":
        coefficients = provenance["co"]
        need(coefficients in catalogue["direct_loads"], "unproved direct construction")
        return [reduce4(coefficients, 1)]
    need(kind in ("pair-word", "pair-scalar"), "unproved construction kind")
    pair = provenance["pair"]
    need(isinstance(pair, list) and len(pair) == 2 and
         all(type(i) is int for i in pair), "invalid paired labels")
    i, j = pair
    need(0 <= i < j < 4, "invalid paired labels")
    other = [t for t in range(4) if t not in (i, j)]
    if kind == "pair-word":
        need(provenance["word"] in sources, "missing three-role source")
        bounds = word_bounds(provenance["word"], 3)
        for (u, su), (v, sv) in zip(bounds, bounds[1:]):
            need(u > v or (u == v and (not su or sv)), "source intervals not nested")
        permutation = provenance["assignment"]
        need(isinstance(permutation, list) and all(type(k) is int for k in permutation)
             and sorted(permutation) == [0, 1, 2], "invalid three-role assignment")
        caps = [(F(1), False)] * 4
        for q, t in enumerate(permutation):
            cap, strict = bounds[t]
            if q < 2:
                caps[other[q]] = (cap, strict)
            else:
                caps[i] = caps[j] = (cap / 2, strict)
        return from_caps(caps)
    singleton = provenance["singleton"]
    need(type(singleton) is int and 0 <= singleton < 3, "invalid scalar singleton")
    expressions = [[int(q == t) for q in range(4)] for t in other]
    expressions.append([2 * int(q == i) for q in range(4)])
    return [reduce4([expressions[singleton][q] + 2 * expressions[t][q]
                     for q in range(4)], 1)
            for t in range(3) if t != singleton]


def verify(proof_file: Path | None = None):
    catalogue = load(ROOT / "catalogue.json")
    need(catalogue["schema"] == "four-role-mathematical-catalogue-1"
         and catalogue["density"] == "5/6", "unexpected four-role catalogue")
    words, sources = catalogue["four_role_words"], catalogue["three_role_words"]
    need(len(words) == len(set(words)) == 63 and len(sources) == len(set(sources)) == 6,
         "incomplete or duplicate word catalogue")
    need(catalogue["direct_loads"] == [[1, 3, 0, 0], [3, 0, 0, 1], [2, 0, 2, 0]],
         "unexpected direct load constructions")
    proof = load(proof_file or ROOT / "coverage-proof.json")
    need(proof["variables"] == ["x", "y", "z"]
         and proof["elimination"] == "w=5/6-x-y-z", "wrong normalized domain")
    initial = [normalize([-1, 1, 0], 0, False), normalize([0, -1, 1], 0, False),
               normalize([-1, -1, -2], -D, False), normalize([1, 1, 1], D, True)]
    need([tuple(h) for h in proof["root_atoms"]] == initial, "wrong closed/strict root faces")
    regions = []
    for region in proof["regions"]:
        expected = expected_region(region, catalogue)
        need([tuple(h) for h in region["atoms"]] == expected, "construction region mismatch")
        regions.append(expected)
    need(len(regions) == 93, "incomplete construction regions")
    nodes = proof["nodes"]
    need(len(nodes) == 735, "incomplete four-role cover tree")
    seen, counts, used = set(), Counter(), Counter()
    strict_zero = negative_rhs = uses_positive_fourth = 0
    stack = [(proof["root_node"], initial)]
    while stack:
        index, path = stack.pop()
        need(type(index) is int and 0 <= index < len(nodes) and index not in seen,
             "invalid, reused or cyclic tree node")
        seen.add(index)
        node = nodes[index]
        kind = node["kind"]
        counts[kind] += 1
        if kind == "split":
            atom = tuple(node["atom"])
            need(len(atom) == 5 and all(type(v) is int for v in atom[:4])
                 and type(atom[4]) is bool, "malformed rational split")
            complement = tuple(-v for v in atom[:4]) + (not atom[4],)
            stack.append((node["inside"], path + [atom]))
            stack.append((node["outside"], path + [complement]))
        elif kind == "covered":
            region = node["region"]
            need(type(region) is int and 0 <= region < len(regions), "missing construction region")
            need(all(atom in path for atom in regions[region]), "path does not imply source region")
            used[region] += 1
        else:
            need(kind == "empty", "unknown proof leaf")
            total, strict, indices, root_strict = [F(0)] * 4, False, set(), False
            need(bool(node["weights"]), "missing contradiction weights")
            for premise, weight in node["weights"]:
                need(type(premise) is int and 0 <= premise < len(path) and premise not in indices,
                     "invalid contradiction premise")
                indices.add(premise)
                value = F(weight)
                need(value > 0, "nonpositive contradiction multiplier")
                atom = path[premise]
                for coordinate in range(4):
                    total[coordinate] += value * atom[coordinate]
                strict = strict or atom[4]
                root_strict = root_strict or premise == 3
            need(total[:3] == [0, 0, 0]
                 and (total[3] < 0 or (total[3] == 0 and strict)),
                 "invalid rational contradiction")
            if total[3] < 0:
                negative_rhs += 1
            else:
                strict_zero += 1
                uses_positive_fourth += int(root_strict)
    need(len(seen) == len(nodes), "unreachable cover-tree node")
    word_data = load(ROOT / "word-certificates.json")
    need([c["word"] for c in word_data["source"]] == sources
         and [c["word"] for c in word_data["catalogue"]] == words, "word inventory mismatch")
    for row, roles in ([(row, 3) for row in word_data["source"]]
                       + [(row, 4) for row in word_data["catalogue"]]):
        tasks = row["tasks"]
        need(all(type(task["strict"]) is bool for task in tasks), "invalid periodic cap flag")
        need([(F(task["rate_cap"]), task["strict"]) for task in tasks]
             == word_bounds(row["word"], roles), "false periodic cap or closed endpoint")
    need(dict(counts) == {"split": 367, "covered": 96, "empty": 272},
         "cover-tree census changed")
    return {"result": "VERIFIED: Delta4 is contained in K_star", "regions": len(regions),
            "nodes": len(seen), "word_regions_checked": 69, "node_kinds": dict(counts),
            "empty_negative_rhs": negative_rhs, "empty_strict_zero_rhs": strict_zero,
            "strict_zero_using_w_positive": uses_positive_fourth}


if __name__ == "__main__":
    try:
        print(json.dumps(verify(Path(sys.argv[1]) if len(sys.argv) > 1 else None), sort_keys=True))
    except (ValueError, OSError, KeyError, IndexError, TypeError, ZeroDivisionError) as exc:
        raise SystemExit(f"Four-role verification failed: {exc}") from exc
