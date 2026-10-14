#!/usr/bin/env python3
"""Independent exact replay of the closed middle paired-band cover.

This implementation reads the archived proof object directly from its ZIP.
It does not import the middle paired-band programs. The mathematical acceptance rules are stated in Appendix D.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import cache
from itertools import product
import gzip
import json
from pathlib import Path
import zipfile


HERE = Path(__file__).resolve().parent
DEFAULT_ZIP = HERE.parent / "data/middle-cover.json.gz"
DENSITY = Q(5, 6)
NCOORD = 7


class InvalidCertificate(ValueError):
    pass


def require(test: bool, message: str) -> None:
    if not test:
        raise InvalidCertificate(message)


def rational(s: object) -> Q:
    require(isinstance(s, str), "rational must be a string")
    try:
        return Q(s)
    except (ValueError, ZeroDivisionError) as exc:
        raise InvalidCertificate(f"invalid rational {s!r}") from exc


def read_cover(path: Path) -> dict:
    data = json.loads(gzip.decompress(path.read_bytes()))
    require(isinstance(data, dict), "cover must be an object")
    return data


def check_period(word: object, rates: tuple[Q, ...], source_id: int) -> int:
    """Check all cyclic windows via a monotone queue of prefix deficits.

    For rate p/q, each slot contributes p-q when it carries the label, p
    otherwise. The queue finds the maximum sum of any window of length at most
    one period, at every starting phase. A nonpositive full-period drift then
    extends the check to arbitrary lengths.
    """
    require(isinstance(word, list) and word, f"source {source_id}: empty word")
    require(all(type(label) is int and 0 <= label < 8 for label in word),
            f"source {source_id}: invalid label")
    period = len(word)
    frequency = Counter(word)
    for label, rate in enumerate(rates):
        p, q = rate.numerator, rate.denominator
        require(p > 0 and p <= q, f"source {source_id}: invalid cap for label {label}")
        require(p * period <= q * frequency[label],
                f"source {source_id}: frequency failure for label {label}")
        prefix = 0
        minima: deque[tuple[int, int]] = deque()
        for end in range(1, 2 * period):
            start = end - 1
            if start < period:
                while minima and minima[-1][1] >= prefix:
                    minima.pop()
                minima.append((start, prefix))
            cutoff = end - period
            while minima and minima[0][0] < cutoff:
                minima.popleft()
            prefix += p - q * (word[(end - 1) % period] == label)
            require(prefix - minima[0][1] <= q,
                    f"source {source_id}: cyclic deficit failure for label {label}, "
                    f"end {end}")
    return period


def check_sources(records: object) -> list[tuple[Q, ...]]:
    require(isinstance(records, list) and records, "missing source list")
    caps_list = []
    for source_id, source in enumerate(records):
        require(isinstance(source, dict) and set(source) == {"caps", "word"},
                f"source {source_id}: bad fields")
        raw_caps = source["caps"]
        require(isinstance(raw_caps, list) and len(raw_caps) == NCOORD,
                f"source {source_id}: expected seven caps")
        caps = tuple(map(rational, raw_caps))
        require(all(caps[i] >= caps[i + 1] for i in range(6)),
                f"source {source_id}: unordered caps")
        check_period(source["word"], caps + (caps[6],), source_id)
        caps_list.append(caps)
    return caps_list


@dataclass(frozen=True)
class Region:
    low: tuple[Q, ...]
    high: tuple[Q, ...]
    low_strict: tuple[bool, ...]
    high_strict: tuple[bool, ...]


def region(low: list[Q], high: list[Q],
           low_strict: list[bool], high_strict: list[bool]) -> Region | None:
    """Canonical ordered interval intersection, including open endpoints."""
    for i in range(5, -1, -1):
        if low[i] < low[i + 1]:
            low[i], low_strict[i] = low[i + 1], low_strict[i + 1]
        elif low[i] == low[i + 1]:
            low_strict[i] |= low_strict[i + 1]
    for i in range(1, 7):
        if high[i] > high[i - 1]:
            high[i], high_strict[i] = high[i - 1], high_strict[i - 1]
        elif high[i] == high[i - 1]:
            high_strict[i] |= high_strict[i - 1]
    for i in range(7):
        if low[i] > high[i] or (low[i] == high[i] and
                                (low_strict[i] or high_strict[i])):
            return None
    low_sum, high_sum = sum(low), sum(high)
    if low_sum > DENSITY or high_sum < DENSITY:
        return None
    if low_sum == DENSITY and any(low_strict):
        return None
    if high_sum == DENSITY and any(high_strict):
        return None
    return Region(tuple(low), tuple(high), tuple(low_strict), tuple(high_strict))


def root_region() -> Region:
    result = region([Q(1, 21)] * 7, [DENSITY] * 6 + [Q(1, 11)],
                    [False] * 7, [False] * 7)
    require(result is not None, "empty root domain")
    return result


def bound_box(r: Region, coordinate: int, cap: Q, pass_cap: bool) -> Region | None:
    low, high = list(r.low), list(r.high)
    lower_open, upper_open = list(r.low_strict), list(r.high_strict)
    if pass_cap:
        if cap < high[coordinate]:
            high[coordinate], upper_open[coordinate] = cap, False
    else:
        if cap > low[coordinate]:
            low[coordinate], lower_open[coordinate] = cap, True
        elif cap == low[coordinate]:
            lower_open[coordinate] = True
    return region(low, high, lower_open, upper_open)


def residual_boxes(r: Region, caps: tuple[Q, ...]) -> list[Region]:
    """Return the nonempty first-failure boxes in coordinate order."""
    out = []
    previous = r
    for i, cap in enumerate(caps):
        failure = bound_box(previous, i, cap, False)
        if failure is not None:
            out.append(failure)
        previous = bound_box(previous, i, cap, True)
        if previous is None:
            break
    return out


def coordinate_envelope(r: Region) -> tuple[tuple[Q, ...], tuple[Q, ...]]:
    """Safe closed coordinate extrema from order and the fixed sum.

    For x_i above a candidate value, every coordinate j..i, j<=i, is
    at least x_i. The reversed argument bounds x_i below. Taking all such
    blocks gives the following exact rational outer box.
    """
    lo, hi = r.low, r.high
    lower, upper = [], []
    for i in range(7):
        max_i = hi[i]
        for j in range(i + 1):
            candidate = (DENSITY - sum(lo[:j]) - sum(lo[i + 1:])) / (i - j + 1)
            if candidate < max_i:
                max_i = candidate
        min_i = lo[i]
        for j in range(i, 7):
            candidate = (DENSITY - sum(hi[:i]) - sum(hi[j + 1:])) / (j - i + 1)
            if candidate > min_i:
                min_i = candidate
        require(min_i <= max_i, "internal envelope contradiction")
        lower.append(min_i)
        upper.append(max_i)
    return tuple(lower), tuple(upper)


def linear_ceiling(coeff: tuple[int, ...], lo: tuple[Q, ...], hi: tuple[Q, ...]) -> Q:
    """Box-plus-sum LP by its one-variable rational dual.

    For every lambda, c.x <= lambda*d + sum_i max((c_i-lambda)*lo_i,
    (c_i-lambda)*hi_i). Its minimum occurs at a coefficient c_i. This is
    the exact box/hyperplane optimum, independent of a greedy fill order.
    """
    return min(
        lam * DENSITY + sum((c - lam) * (hi[i] if c > lam else lo[i])
                            for i, c in enumerate(coeff))
        for lam in set(coeff)
    )


@cache
def weight_shapes(n: int) -> tuple[tuple[int, ...], ...]:
    if n == 1:
        return ((1,),)

    def partitions(total: int, smallest: int = 1):
        if total == 0:
            yield ()
        for first in range(smallest, total + 1):
            for rest in partitions(total - first, first):
                yield (first,) + rest

    shapes = set()
    for parts in partitions(n):
        if len(parts) < 2:
            continue
        arity = len(parts)
        for child_shapes in product(*(weight_shapes(size) for size in parts)):
            shapes.add(tuple(sorted(arity * weight for shape in child_shapes
                                    for weight in shape)))
    return tuple(sorted(shapes))


def forest_menu() -> tuple[tuple[tuple[int, ...], ...], ...]:
    """All split-point pairs, sorted lexicographically within each root size."""
    forms = []
    for split in range(1, 8):
        for left in weight_shapes(split):
            for right in weight_shapes(8 - split):
                pair_forms = []
                for i, left_weight in enumerate(left):
                    for j, right_weight in enumerate(right, start=split):
                        coeff = [0] * 7
                        coeff[min(i, 6)] += left_weight
                        coeff[min(j, 6)] += right_weight
                        pair_forms.append(tuple(coeff))
                forms.append(tuple(pair_forms))
    require(len(forms) == 222, "forest menu length differs from specification")
    return tuple(forms)


def check_leaf(leaf: object, incoming: Region, caps: list[tuple[Q, ...]],
               forests: tuple[tuple[tuple[int, ...], ...], ...]) -> str:
    require(isinstance(leaf, list) and len(leaf) == 2 and type(leaf[1]) is int,
            "invalid leaf record")
    kind, arg = leaf
    lo, hi = coordinate_envelope(incoming)
    if kind == "word":
        require(0 <= arg < len(caps), f"unknown leaf word {arg}")
        require(all(hi[i] <= caps[arg][i] for i in range(7)),
                f"word leaf {arg} fails whole-region cap")
    elif kind == "flat":
        require(0 <= arg <= 6, f"unknown flat source {arg}")
        coeff = [0] * 7
        if arg == 0:
            coeff[0] = 8
        else:
            coeff[0], coeff[arg] = arg, 8 - arg
        require(linear_ceiling(tuple(coeff), lo, hi) <= 1,
                f"flat source {arg} exceeds capacity")
    elif kind == "forest":
        require(0 <= arg < len(forests), f"unknown forest source {arg}")
        for form in forests[arg]:
            require(linear_ceiling(form, lo, hi) <= 1,
                    f"forest source {arg} exceeds capacity")
    else:
        raise InvalidCertificate(f"unknown leaf kind {kind!r}")
    return kind


def check_cover(data: dict, caps: list[tuple[Q, ...]]) -> dict:
    require(data.get("format") == "R420-cover-v1", "wrong cover format")
    require(data.get("domain") == {"density": "5/6", "delta_lo": "1/21",
                                   "delta_hi": "1/11"}, "wrong root domain")
    require(data.get("frontier") == [], "certificate has a frontier")
    nodes = data.get("nodes")
    require(isinstance(nodes, list) and nodes, "missing region tree")
    forests = forest_menu()
    reached = set()
    todo = [(0, root_region())]
    counts = Counter()
    while todo:
        index, incoming = todo.pop()
        require(type(index) is int and 0 <= index < len(nodes),
                f"invalid node id {index!r}")
        require(index not in reached, f"region node {index} reached twice")
        reached.add(index)
        node = nodes[index]
        require(isinstance(node, dict) and len(node) == 1,
                f"malformed node {index}")
        if "leaf" in node:
            counts[check_leaf(node["leaf"], incoming, caps, forests)] += 1
        elif "split" in node:
            split = node["split"]
            require(isinstance(split, list) and len(split) == 2 and
                    type(split[0]) is int and 0 <= split[0] < len(caps) and
                    isinstance(split[1], list), f"invalid split {index}")
            source_id, children = split
            boxes = residual_boxes(incoming, caps[source_id])
            require(len(children) == len(boxes),
                    f"split {index}: expected {len(boxes)} nonempty children, "
                    f"found {len(children)}")
            require(all(type(child) is int for child in children),
                    f"split {index}: noninteger child")
            counts["split"] += 1
            for child, box in zip(children, boxes):
                todo.append((child, box))
        else:
            raise InvalidCertificate(f"unknown node type {index}")
    require(len(reached) == len(nodes),
            f"{len(nodes) - len(reached)} unreachable nodes")
    counts["nodes"] = len(reached)
    counts["sources"] = len(caps)
    counts["frontier"] = 0
    return dict(counts)


def negative_controls(data: dict, caps: list[tuple[Q, ...]]) -> dict[str, str]:
    """Deliberately damage accepted mathematical obligations and demand rejection."""
    outcomes = {}

    def expect_reject(name: str, action) -> None:
        try:
            action()
        except InvalidCertificate as exc:
            outcomes[name] = str(exc)
        else:
            raise AssertionError(f"negative control unexpectedly accepted: {name}")

    source = data["sources"][0]
    bad_caps = tuple(caps[0][:-1]) + (Q(1),)
    expect_reject("inflated source cap", lambda: check_period(
        source["word"], bad_caps + (bad_caps[6],), 0))

    damaged = dict(data)
    damaged["nodes"] = list(data["nodes"])
    damaged["nodes"][0] = {"split": [data["nodes"][0]["split"][0],
                                     data["nodes"][0]["split"][1][1:]]}
    expect_reject("omitted first-failure child", lambda: check_cover(damaged, caps))

    damaged = dict(data)
    damaged["frontier"] = [0]
    expect_reject("false completion", lambda: check_cover(damaged, caps))

    root = root_region()
    forests = forest_menu()
    expect_reject("unsupported word leaf",
                  lambda: check_leaf(["word", 0], root, caps, forests))
    expect_reject("overpriced flat leaf",
                  lambda: check_leaf(["flat", 0], root, caps, forests))
    expect_reject("overpriced forest leaf",
                  lambda: check_leaf(["forest", 0], root, caps, forests))

    # Closed equality is covered by the cap; the strict failure side is empty.
    delta = Q(1, 11)
    head = (DENSITY - delta) / 6
    exact = [head] * 6 + [delta]
    point = region(exact.copy(), exact.copy(),
                   [False] * 7, [False] * 7)
    require(point is not None, "equality control point is empty")
    require(bound_box(point, 6, delta, True) is not None,
            "closed cap lost equality point")
    require(bound_box(point, 6, delta, False) is None,
            "strict failure retained equality point")
    outcomes["closed equality face"] = "strict failure empty, closed pass nonempty"

    # In this period, slots 2..8 have no label 0. At L=7, r=1/7,
    # weak quota is zero, while ordinary quota is one.
    endpoint_word = [0, 0, 1, 2, 3, 4, 5, 6, 7]
    endpoint_rates = (Q(1, 7),) + (Q(1, 9),) * 7
    check_period(endpoint_word, endpoint_rates, -1)
    expect_reject("raised weak endpoint", lambda: check_period(
        endpoint_word, (Q(1, 6),) + endpoint_rates[1:], -1))
    outcomes["weak integer endpoint"] = "accepted at 1/7 despite ordinary failure"
    return outcomes


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", nargs="?", type=Path, default=DEFAULT_ZIP)
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    data = read_cover(args.archive)
    caps = check_sources(data.get("sources"))
    result = check_cover(data, caps)
    if args.negative_controls:
        result["negative_controls"] = negative_controls(data, caps)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except InvalidCertificate as exc:
        raise SystemExit(f"REJECTED: {exc}") from exc
