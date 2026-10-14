#!/usr/bin/env python3
"""Independent exact checker of the two complete eleventh-band covers.

This file does not import the returned verifier. It reads only the two saved
certificate JSON members of the immutable eleventh-band ZIP. Discovery metadata and
the seven unrelated partial trees are not used as proof inputs.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time
from zipfile import ZipFile

Q = Fraction
D = Q(5, 6)
ZERO = (Q(0),) * 7
ARCHIVE = Path(__file__).resolve().parents[1] / "data/eleventh-band.zip"
MEMBERS = {
    0: ("band_1_11_m0.json",
        "ecebf1db672e87096528b93abab9fd2296be472e4c0e1d57f2b343206fd2a5cc"),
    1: ("band_1_11_m1.json",
        "f68cdd210e7086849f3a306bcf2b2eeb827d2464cc71d64f69b7668b60f8098e"),
}


class InvalidCertificate(Exception):
    pass


def need(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidCertificate(message)


def row(entries) -> tuple[Q, ...]:
    result = tuple(Q(t) for t in entries)
    need(len(result) == 7, "a row must have seven coordinates")
    return result


def role(index: int, mark: int) -> tuple[Q, ...]:
    """Sorted physical role index to six head / one half-mark coordinates."""
    need(type(index) is int and 0 <= index < 7, "invalid role index")
    out = [Q(0)] * 7
    if index == mark:
        out[6] = Q(2)
    else:
        out[index if index < mark else index - 1] = Q(1)
    return tuple(out)


def root_region(data: dict, mark: int):
    """An exact, closed strip with only the four *strict* price failures."""
    need(data.get("format") == "R190-exact-first-failure-cover-v1", "format")
    need(data.get("mark") == mark, "wrong marked position")
    need(Q(data.get("cut")) == Q(1, 11), "lower endpoint changed")
    need(Q(data.get("upper")) == Q(1, 10), "upper endpoint changed")
    need(data.get("restricted") is False, "unexpected restricted root")
    need(data.get("filtered", False) is False, "unexpected filtered root")
    need(data.get("strong_filtered", False) is False, "unexpected strong filter")
    need(data.get("status") == "COMPLETE" and data.get("todo") == [],
         "cover still has a frontier")

    rows = []  # (seven coefficients, right hand side, strict?)
    for i in range(5):
        a = [0] * 7
        a[i], a[i + 1] = -1, 1
        rows.append((row(a), Q(0), False))
    rows.extend([
        (row([0, 0, 0, 0, 0, -1, 1]), Q(0), False),
        (row([0, 0, 0, 0, 0, 0, -1]), -Q(1, 11), False),
        (row([0, 0, 0, 0, 0, 0, 1]), Q(1, 10), False),
    ])
    for a in ([ -8, 0, 0, 0, 0, 0, 0],
              [ -2, 0, -6, 0, 0, 0, 0],
              [ -4, 0, 0, 0, -4, 0, 0],
              [ -6, 0, 0, 0, 0, 0, -2]):
        rows.append((row(a), Q(-1), True))
    if mark == 0:
        rows.append((row([1, 0, 0, 0, 0, 0, -2]), Q(0), False))
    else:
        rows.extend([
            (row([-1, 0, 0, 0, 0, 0, 2]), Q(0), False),
            (row([0, 1, 0, 0, 0, 0, -2]), Q(0), False),
        ])
    return tuple(rows)


def forest_leaves(tree, multiplier=1):
    if type(tree) is int:
        need(0 <= tree < 7, "invalid forest leaf")
        return [(tree, multiplier)]
    need(type(tree) is list and len(tree) >= 2, "forest internal arity < 2")
    out = []
    for child in tree:
        out.extend(forest_leaves(child, multiplier * len(tree)))
    return out


def source_tests(box: dict, mark: int):
    """Return all ordered closed inequalities required by this actual source."""
    kind = box.get("kind", "word")
    if kind == "word":
        caps = tuple(Q(c) for c in box["caps"])
        need(len(caps) == 7 and all(c >= 0 for c in caps), "word caps")
        need(all(caps[i] >= caps[i + 1] for i in range(6)), "caps unsorted")
        # Under the root's sorted physical rates, an equal later cap is
        # implied by the earlier role's cap; retain exactly the first one.
        return [(role(i, mark), cap) for i, cap in enumerate(caps)
                if i == 0 or cap != caps[i - 1]]
    need(kind == "forest", f"unsupported source kind {kind!r}")
    trees = box["trees"]
    need(type(trees) is list and 1 <= len(trees) <= 2, "forest root count")
    raw = [forest_leaves(tree) for tree in trees]
    need(sorted(i for root in raw for i, _ in root) == list(range(7)),
         "forest roots do not partition seven labels")
    maxima = []
    for group in raw:
        active = []
        greatest_earlier_arity = 0
        for i, arity in sorted(group):
            if arity > greatest_earlier_arity:
                active.append((i, arity))
                greatest_earlier_arity = arity
        maxima.append(active)
    if len(maxima) == 1:
        return [(tuple(arity * x for x in role(i, mark)), Q(1))
                for i, arity in maxima[0]]
    return [
        (tuple(a * x + b * y for x, y in zip(role(i, mark), role(j, mark))), Q(1))
        for i, a in maxima[0] for j, b in maxima[1]
    ]


def check_literal_word(box: dict) -> tuple[int, int]:
    """Independent rank-span check, not the returned sliding-prefix test."""
    symbols = box["word"]
    need(type(symbols) is list and symbols, "empty word")
    need(all(type(v) is int and 0 <= v < 7 for v in symbols), "word alphabet")
    caps = tuple(Q(c) for c in box["caps"])
    need(len(caps) == 7, "seven word caps required")
    period = len(symbols)
    comparisons = 0
    for label, cap in enumerate(caps):
        positions = [i for i, v in enumerate(symbols) if v == label]
        count = len(positions)
        need(period * cap <= count, f"word frequency fails for role {label}")
        if cap == 0:
            continue
        need(count > 0, f"positive cap but role {label} absent")
        extended = positions + [v + period for v in positions]
        for rank in range(1, count + 1):
            # A longest cyclic window with rank-1 visits has length H-1.
            span = max(extended[j + rank] - extended[j] for j in range(count))
            comparisons += count
            need(cap * (span - 1) <= rank,
                 f"cyclic rank-span cap fails for role {label}, rank {rank}")
    return period, comparisons


def check_dual(cert: dict, constraints, node_id: int) -> None:
    """Reconstruct the claimed Farkas identity including common strict slack."""
    coeff = [Q(x) for x in cert["dual"]]
    need(len(coeff) == len(constraints) + 1, f"dual length at node {node_id}")
    need(all(x <= 0 for x in coeff), f"negative Farkas weight at {node_id}")
    weights = [-x for x in coeff]
    eq_weight = -Q(cert["eq_dual"])
    lhs = [eq_weight] * 7 + [Q(0)]
    rhs = eq_weight * D + weights[-1]  # epsilon <= 1
    lhs[7] += weights[-1]
    for weight, (a, bound, strict) in zip(weights[:-1], constraints):
        if not weight:
            continue
        for i in range(7):
            lhs[i] += weight * a[i]
        lhs[7] += weight if strict else 0
        rhs += weight * bound
    need(lhs == [Q(0)] * 7 + [Q(1)], f"wrong exact dual identity at {node_id}")
    need(rhs == Q(cert["epsilon_upper"]) and rhs <= 0,
         f"noncontradictory exact dual at {node_id}")


def verify_tree(data: dict, mark: int):
    base = root_region(data, mark)
    nodes, boxes = data["nodes"], data["boxes"]
    need(type(nodes) is list and nodes, "empty node list")
    need(type(boxes) is list, "missing source boxes")
    used = set()
    seen = set()
    source_count = leaf_count = max_depth = 0
    # Each child receives every successful earlier condition and the strict
    # failure of its own condition. A child exists at every failure index.
    work = [(0, base, 0)]
    while work:
        nid, constraints, depth = work.pop()
        need(type(nid) is int and 0 <= nid < len(nodes), "bad node ID")
        need(nid not in seen, f"repeated node {nid}")
        seen.add(nid)
        max_depth = max(max_depth, depth)
        node = nodes[nid]
        if "leaf" in node:
            need("source" not in node and "children" not in node,
                 f"node {nid} is both leaf and source")
            check_dual(node["leaf"], constraints, nid)
            leaf_count += 1
            continue
        need("source" in node and "children" in node,
             f"node {nid} has no proof, source, or complete children")
        source_index = node["source"]
        need(type(source_index) is int and 0 <= source_index < len(boxes),
             f"bad source index at {nid}")
        used.add(source_index)
        source_count += 1
        tests = source_tests(boxes[source_index], mark)
        children = node["children"]
        need(type(children) is list and len(children) == len(tests),
             f"missing first-failure branch at {nid}")
        prefix = constraints
        successors = []
        for j, ((a, bound), child) in enumerate(zip(tests, children)):
            need(type(child) is int and nid < child < len(nodes),
                 f"invalid child index at {nid}:{j}")
            child_record = nodes[child]
            need(child_record.get("parent") == nid and
                 child_record.get("failure") == j,
                 f"wrong parent/failure at {nid}:{j}")
            failure = (tuple(-x for x in a), -bound, True)
            successors.append((child, prefix + (failure,), depth + 1))
            prefix += ((a, bound, False),)
        work.extend(reversed(successors))
    need(len(seen) == len(nodes), "unreachable certificate nodes")
    counts = Counter()
    slots = comparisons = maximum_period = 0
    for source_index in sorted(used):
        box = boxes[source_index]
        kind = box.get("kind", "word")
        counts[kind] += 1
        if kind == "word":
            period, local_comparisons = check_literal_word(box)
            slots += period
            comparisons += local_comparisons
            maximum_period = max(maximum_period, period)
        else:
            source_tests(box, mark)
    return {
        "nodes": len(seen), "exact_dual_leaves": leaf_count,
        "source_nodes": source_count, "pending": 0, "max_depth": max_depth,
        "distinct_word_boxes": counts["word"], "distinct_forests": counts["forest"],
        "literal_slots": slots, "max_period": maximum_period,
        "span_comparisons": comparisons,
    }


def negative_controls(data: dict, mark: int) -> list[str]:
    passed = []
    controls = [
        ("lower endpoint", lambda s: s.__setitem__("cut", str(Q(1, 11) + Q(1, 1000000)))),
        ("upper endpoint", lambda s: s.__setitem__("upper", "999999/10000000")),
        ("unexpected filter", lambda s: s.__setitem__("filtered", True)),
    ]
    for name, mutation in controls:
        sample = dict(data)
        mutation(sample)
        try:
            root_region(sample, mark)
        except (InvalidCertificate, ValueError):
            passed.append(name)
        else:
            raise InvalidCertificate(f"negative control accepted: {name}")
    # Corrupt a branch of the actual tree, without changing the raw archive.
    sample = dict(data)
    sample["nodes"] = [dict(data["nodes"][0])] + data["nodes"][1:]
    sample["nodes"][0]["children"] = sample["nodes"][0]["children"][:-1]
    try:
        verify_tree(sample, mark)
    except InvalidCertificate:
        passed.append("missing first-failure child")
    else:
        raise InvalidCertificate("negative control accepted: missing branch")
    first_leaf = next(i for i, node in enumerate(data["nodes"]) if "leaf" in node)
    sample = dict(data)
    sample["nodes"] = data["nodes"].copy()
    sample["nodes"][first_leaf] = dict(sample["nodes"][first_leaf])
    sample["nodes"][first_leaf]["leaf"] = dict(sample["nodes"][first_leaf]["leaf"])
    sample["nodes"][first_leaf]["leaf"]["epsilon_upper"] = "1"
    try:
        verify_tree(sample, mark)
    except InvalidCertificate:
        passed.append("corrupt rational dual")
    else:
        raise InvalidCertificate("negative control accepted: corrupt dual")
    # These source controls exercise literal words and actual tree syntax.
    word = {"word": [0, 1, 2, 3, 4, 5, 6],
            "caps": ["1"] + ["1/7"] * 6}
    try:
        check_literal_word(word)
    except InvalidCertificate:
        passed.append("inflated word cap")
    else:
        raise InvalidCertificate("negative control accepted: inflated cap")
    forest = {"kind": "forest", "trees": [[0, 1, 2, 3, 4, 5], 5]}
    try:
        source_tests(forest, mark)
    except InvalidCertificate:
        passed.append("repeated forest leaf")
    else:
        raise InvalidCertificate("negative control accepted: malformed forest")
    return passed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=ARCHIVE)
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    start = time.monotonic()
    output = {}
    union_words = set()
    with ZipFile(args.archive) as archive:
        for mark, (member, expected_sha) in MEMBERS.items():
            raw = archive.read(member)
            digest = hashlib.sha256(raw).hexdigest()
            need(digest == expected_sha, f"saved certificate digest changed: m{mark}")
            data = json.loads(raw)
            result = verify_tree(data, mark)
            result["sha256"] = digest
            if args.negative_controls:
                result["negative_controls_rejected"] = negative_controls(data, mark)
            output[f"m{mark}"] = result
            used = {node["source"] for node in data["nodes"] if "source" in node}
            union_words.update(
                (tuple(data["boxes"][k]["word"]),
                 tuple(data["boxes"][k]["caps"]))
                for k in used if data["boxes"][k].get("kind", "word") == "word"
            )
    output["total_nodes"] = sum(result["nodes"] for result in output.values())
    output["union_word_cap_pairs"] = len(union_words)
    output["union_literal_slots"] = sum(len(word) for word, _ in union_words)
    output["elapsed_seconds"] = round(time.monotonic() - start, 3)
    output["result"] = "PASS"
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
