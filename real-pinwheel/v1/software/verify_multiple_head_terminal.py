#!/usr/bin/env python3
"""Independent exact checker for the multiple-head terminal literal-word/region certificate.

The proof algorithms here are separate from multiple-head terminal's released verifier:
head service is checked by occurrence-to-successor spans, omitted branches
by their least possible ordered sum, and two-flat leaves by intersection of
strict one-variable half-lines.  Only Python's standard library is used.

This program reads an immutable ZIP and never writes a repository file.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations_with_replacement, product
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time
import zipfile


HERE = Path(__file__).resolve().parent
DEFAULT_ARCHIVE = HERE.parent / "data/multiple-head-terminal.zip"
MEMBER = "release-certificate.json.gz"
ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"


def need(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


@lru_cache(maxsize=200000)
def rat(value: str | int) -> Fraction:
    return Fraction(value)


def image_upper(tail: tuple[int, ...]) -> Fraction:
    need(bool(tail), "empty tail in multiple-head terminal release")
    need(tuple(sorted(tail)) == tail and all(11 <= c <= 21 for c in tail), "bad tail signature")
    credit = Fraction(1, 22) if tail[-1] == 21 else Fraction(1, 2 * (tail[0] + 1))
    return Fraction(5, 6) + credit - sum((Fraction(1, c + 1) for c in tail), Fraction(0))


class Auditor:
    def __init__(self, data: dict):
        self.data = data
        self.words = data["words"]
        self.word_cache: dict[str, tuple[tuple[tuple[Fraction, bool], ...], tuple[int, ...]]] = {}
        self.used_words: set[str] = set()
        self.count = Counter()

    def word(self, wid: str):
        if wid in self.word_cache:
            return self.word_cache[wid]
        need(wid in self.words, f"missing source word {wid}")
        row = self.words[wid]
        p, q, letters = row["p"], row["q"], row["word"]
        period = len(letters)
        need(isinstance(p, int) and isinstance(q, int) and p >= 1 and q >= 1, f"bad roles: {wid}")
        need(period >= p + q and p + q <= len(ALPHABET), f"bad word length: {wid}")
        need(set(letters) == set(ALPHABET[: p + q]), f"wrong distinct labels: {wid}")
        need(len(row["head_caps"]) == p and len(row["tail_gaps"]) == q, f"wrong word metadata: {wid}")
        locations = [[] for _ in range(p + q)]
        for t, label in enumerate(letters):
            locations[ALPHABET.index(label)].append(t)
        caps = []
        for i, pair in enumerate(row["head_caps"]):
            need(isinstance(pair, list) and len(pair) == 2 and type(pair[1]) is bool, f"bad cap flag: {wid}")
            cap, closed = rat(pair[0]), pair[1]
            need(0 < cap <= 1, f"bad cap value: {wid}")
            a, b = cap.numerator, cap.denominator
            pos = locations[i]
            m = len(pos)
            need(a * period <= b * m, f"head frequency insufficient: {wid}/{i}")
            doubled = pos + [t + period for t in pos]
            # Any interval of <P slots with at most k occurrences is contained
            # between an occurrence and its (k+1)-st successor.  This checks
            # every cyclic start/length using occurrence spans, not a deficit
            # prefix scan.  Equality is allowed exactly for an open cap.
            for start in range(m):
                left = doubled[start]
                for k in range(m):
                    length = doubled[start + k + 1] - left - 1
                    if length <= 0:
                        continue
                    lhs, rhs = a * length, b * (k + 1)
                    need(lhs < rhs if closed else lhs <= rhs,
                         f"head window cap fails: {wid}/{i}, start={start}, k={k}, L={length}")
                    self.count["head_span_inequalities"] += 1
            caps.append((cap, closed))
            self.count["head_indicators"] += 1
        need(caps == sorted(caps, reverse=True), f"head caps not sorted: {wid}")
        gaps = []
        for i in range(p, p + q):
            pos = locations[i]
            gap = max((pos[(j + 1) % len(pos)] - pos[j]) % period or period for j in range(len(pos)))
            gaps.append(gap)
            self.count["tail_indicators"] += 1
        need(gaps == row["tail_gaps"] and gaps == sorted(gaps), f"tail gaps wrong: {wid}")
        self.count["words"] += 1
        self.count["word_slots"] += period
        self.count["max_word_period"] = max(self.count["max_word_period"], period)
        answer = (tuple(caps), tuple(gaps))
        self.word_cache[wid] = answer
        return answer

    def source(self, proof: dict, p: int, tail: tuple[int, ...]):
        kind = proof["kind"]
        need(kind in ("word", "integer_literal"), f"unproved existence leaf: {kind}")
        wid = proof["id"]
        need(wid in self.words, f"missing source id {wid}")
        word = self.words[wid]
        need(word["p"] == p and word["q"] == len(tail), f"source roles differ: {wid}")
        caps, gaps = self.word(wid)
        need(all(g <= c for g, c in zip(gaps, tail)), f"tail source too weak: {wid}")
        self.used_words.add(wid)
        self.count[f"source_{kind}"] += 1
        if kind == "word":
            return caps
        ds = proof["periods"]
        need(len(ds) == p and ds == sorted(ds) and all(type(d) is int and 2 <= d <= 11 for d in ds),
             "invalid literal integer head periods")
        requested = tuple((Fraction(1, d), True) for d in ds)
        for (r, _), (cap, closed) in zip(requested, caps):
            need(r < cap or (r == cap and closed), f"literal source misses integer head: {wid}")
        return requested

    def two_flat_leaf(self, lower: tuple[Fraction, ...], tail: tuple[int, ...], upper: Fraction) -> None:
        """Reject any t with every two-flat cut failing and head sum < upper.

        A sum of maxima equals the maximum of finitely many affine lines.
        Therefore f(t)<upper is an intersection of strict half-lines in one
        variable; intersect them exactly, including endpoint openness.
        """
        p, n = len(lower), len(lower) + len(tail)
        left = max(lower[0], Fraction(1, n),
                   *(Fraction(1, j) * (1 - Fraction(n - j, tail[j - p])) for j in range(p, n)))
        right = upper - sum(lower[1:], Fraction(0))
        if left > right:
            self.count["two_flat_empty_interval"] += 1
            return
        left_open = right_open = False
        for choices in product((False, True), repeat=p - 1):
            slope = Fraction(1)
            intercept = Fraction(0)
            for j, use_affine in enumerate(choices, start=1):
                if use_affine:
                    slope -= Fraction(j, n - j)
                    intercept += Fraction(1, n - j)
                else:
                    intercept += lower[j]
            self.count["two_flat_affine_constraints"] += 1
            if slope == 0:
                if intercept >= upper:
                    self.count["two_flat_constant_barrier"] += 1
                    return
                continue
            cut = (upper - intercept) / slope
            if slope > 0:
                if cut < right:
                    right, right_open = cut, True
                elif cut == right:
                    right_open = True
            else:
                if cut > left:
                    left, left_open = cut, True
                elif cut == left:
                    left_open = True
            if left > right or (left == right and (left_open or right_open)):
                self.count["two_flat_halfline_barrier"] += 1
                return
        need(left > right or (left == right and (left_open or right_open)),
             f"two-flat leaf has a possible uncovered point: {lower}, {tail}, {upper}")

    def region(self, row: dict) -> None:
        p = row["p"]
        tail = tuple(row["tail"])
        upper = image_upper(tail)
        need(row["status"] == "COVERED" and rat(row["U"]) == upper, f"wrong region guard: {p}/{tail}")
        need(upper > Fraction(p, 11) and 2 * p + len(tail) <= 19, f"inadmissible region: {p}/{tail}")
        nodes = row["nodes"]
        need(bool(nodes), f"no region graph: {p}/{tail}")
        root = (Fraction(1, 11),) * p
        pending = [(0, root, (False,) * p)]
        seen = {}
        while pending:
            index, lower, strict = pending.pop()
            need(type(index) is int and 0 <= index < len(nodes), f"bad node index: {p}/{tail}")
            if index in seen:
                need(seen[index] == (lower, strict), f"reused node with different state: {p}/{tail}/{index}")
                continue
            seen[index] = (lower, strict)
            node = nodes[index]
            need(tuple(rat(s) for s in node["lower"]) == lower and tuple(node["strict"]) == strict,
                 f"node state mismatch: {p}/{tail}/{index}")
            need(len(lower) == p and all(type(s) is bool for s in strict), f"bad node coordinates: {p}/{tail}/{index}")
            need(lower == tuple(sorted(lower, reverse=True)) and lower[-1] >= Fraction(1, 11),
                 f"unordered node coordinates: {p}/{tail}/{index}")
            self.count["nodes"] += 1
            kind = node["kind"]
            self.count[f"node_{kind}"] += 1
            if kind == "sum":
                need(sum(lower, Fraction(0)) >= upper, f"false empty-sum leaf: {p}/{tail}/{index}")
                continue
            if kind == "two_flat_envelope":
                self.two_flat_leaf(lower, tail, upper)
                continue
            need(kind == "box", f"unknown leaf kind: {p}/{tail}/{index}")
            caps = self.source(node["proof"], p, tail)
            need(tuple((rat(v), flag) for v, flag in node["caps"]) == caps,
                 f"box differs from literal source: {p}/{tail}/{index}")
            for i, (cap, closed) in enumerate(caps):
                need(cap > lower[i] or (cap == lower[i] and closed and not strict[i]),
                     f"empty source box: {p}/{tail}/{index}/{i}")
            children_raw = node["children"]
            children = dict(children_raw)
            need(len(children) == len(children_raw) and
                 all(type(i) is int and 0 <= i < p for i in children),
                 f"duplicate/invalid child branch: {p}/{tail}/{index}")
            required = set()
            for i, (cap, closed) in enumerate(caps):
                # A cap violation forces each preceding ordered coordinate
                # above its old lower bound or at least cap.  This is the
                # *least possible ordered sum*, computed without multiple-head terminal's B_i.
                least = sum((max(lower[j], cap) if j <= i else lower[j] for j in range(p)), Fraction(0))
                if least >= upper:
                    continue
                required.add(i)
                next_lower = list(lower)
                next_strict = list(strict)
                if cap > next_lower[i]:
                    next_lower[i], next_strict[i] = cap, closed
                else:
                    next_strict[i] = next_strict[i] or closed
                for j in range(i - 1, -1, -1):
                    if next_lower[j] < next_lower[j + 1]:
                        next_lower[j] = next_lower[j + 1]
                        next_strict[j] = next_strict[j + 1]
                    elif next_lower[j] == next_lower[j + 1]:
                        next_strict[j] = next_strict[j] or next_strict[j + 1]
                child_state = (tuple(next_lower), tuple(next_strict))
                need(child_state != (lower, strict), f"nonprogressing branch: {p}/{tail}/{index}/{i}")
                need(i in children, f"missing feasible cap violation: {p}/{tail}/{index}/{i}")
                pending.append((children[i], *child_state))
                self.count["required_branches"] += 1
            need(set(children) == required, f"extra/missing branches: {p}/{tail}/{index}")
        # Every edge strictly increases the state's lower/strict data, while
        # a reused node must have one state, so a directed cycle is impossible.
        need(len(seen) == len(nodes), f"unreachable nodes: {p}/{tail}, {len(seen)}/{len(nodes)}")
        self.count["regions"] += 1


def census(rows: list[dict]) -> dict[str, int]:
    actual = {(r["p"], tuple(r["tail"])) for r in rows}
    need(len(actual) == len(rows), "duplicate region signature")
    expected: set[tuple[int, tuple[int, ...]]] = set()
    for p, qs in ((2, range(2, 7)), (3, range(1, 6)),
                  (4, range(1, 5)), (5, range(1, 4))):
        for q in qs:
            for tail in combinations_with_replacement(range(11, 22), q):
                if 2 * p + q <= 19 and image_upper(tail) > Fraction(p, 11):
                    expected.add((p, tail))
    need(len(expected) == 18458 and expected <= actual, "required multiple-head terminal signature set incomplete")
    remaining = actual - expected
    need(remaining == {(6, (12, 14, 21)), (6, (13, 16, 21))},
         f"unexpected extra multiple-head terminal signatures: {remaining}")
    return {"pw7_relevant": len(expected), "extra_six_head": len(remaining)}


def negative_controls(data: dict) -> dict[str, str]:
    outcomes = {}

    # Exhaustive small-period comparison with literal cyclic windows.  This
    # tests the occurrence-span equivalence independently of the release.
    comparisons = 0
    for period in range(2, 8):
        for mask in range(1, (1 << period) - 1):
            positions = [t for t in range(period) if mask & (1 << t)]
            extended = positions + [t + period for t in positions]
            m = len(positions)
            for denominator in range(1, 9):
                for numerator in range(1, denominator + 1):
                    for closed in (False, True):
                        cap = Fraction(numerator, denominator)
                        a, b = cap.numerator, cap.denominator
                        by_spans = a * period <= b * m and all(
                            (a * (extended[start + k + 1] - extended[start] - 1)
                             < b * (k + 1) if closed else
                             a * (extended[start + k + 1] - extended[start] - 1)
                             <= b * (k + 1))
                            for start in range(m) for k in range(m))
                        by_windows = a * period <= b * m and all(
                            a * length - b * sum(bool(mask & (1 << ((start + t) % period)))
                                                   for t in range(length))
                            <= b - (1 if closed else 0)
                            for start in range(period) for length in range(1, period + 1))
                        need(by_spans == by_windows,
                             f"span/window discrepancy: P={period}, mask={mask}, cap={cap}, closed={closed}")
                        comparisons += 1
    outcomes["small_binary_span_window_comparisons"] = str(comparisons)

    def rejects(name, run):
        try:
            run()
        except (ValueError, KeyError, IndexError, TypeError, ZeroDivisionError):
            outcomes[name] = "rejected"
        else:
            raise ValueError(f"negative control accepted: {name}")

    first = data["regions"][0]
    altered = copy.deepcopy(first)
    altered["nodes"][0]["children"].pop()
    rejects("deleted_required_branch", lambda: Auditor(data).region(altered))
    altered = copy.deepcopy(first)
    altered["U"] = str(rat(first["U"]) + Fraction(1, 1000))
    rejects("inflated_guard", lambda: Auditor(data).region(altered))
    altered = copy.deepcopy(first)
    altered["nodes"][0]["strict"][0] = True
    rejects("changed_closed_root", lambda: Auditor(data).region(altered))
    altered_data = {"words": dict(data["words"])}
    wid = next(w for w, row in data["words"].items() if any(not cap[1] for cap in row["head_caps"]))
    altered_data["words"][wid] = copy.deepcopy(data["words"][wid])
    altered_data["words"][wid]["tail_gaps"][0] -= 1
    rejects("false_tail_gap", lambda: Auditor(altered_data).word(wid))
    # Find an open cap that is actually tight; closing it must be rejected.
    def close_tight_cap():
        for word_id, source in data["words"].items():
            for i, (_, closed) in enumerate(source["head_caps"]):
                if closed:
                    continue
                fake = {"words": {word_id: copy.deepcopy(source)}}
                fake["words"][word_id]["head_caps"][i][1] = True
                try:
                    Auditor(fake).word(word_id)
                except ValueError as exc:
                    if str(exc).startswith("head window cap fails"):
                        return
        raise ValueError("no tight open cap found")
    close_tight_cap()
    outcomes["closed_tight_open_cap"] = "rejected"
    rejects("false_two_flat_leaf", lambda: Auditor(data).two_flat_leaf(
        (Fraction(1, 11), Fraction(1, 11)), (11, 11), Fraction(17, 24)))
    return outcomes


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--archive", type=Path, default=DEFAULT_ARCHIVE)
    ap.add_argument("--negative-controls", action="store_true")
    args = ap.parse_args()
    start = time.monotonic()
    try:
        archive_digest = hashlib.sha256(args.archive.read_bytes()).hexdigest()
        with zipfile.ZipFile(args.archive) as zf:
            compressed = zf.read(MEMBER)
        certificate_digest = hashlib.sha256(compressed).hexdigest()
        data = json.loads(gzip.decompress(compressed))
        need(set(data) >= {"words", "regions"}, "missing certificate fields")
        # The literal-release contract forbids opaque integer-source leaves.
        auditor = Auditor(data)
        sig_counts = census(data["regions"])
        for row in data["regions"]:
            auditor.region(row)
        need(auditor.used_words == set(data["words"]), "unused or missing literal source words")
        controls = negative_controls(data) if args.negative_controls else None
        result = {
            "status": "PASS",
            "archive_sha256": archive_digest,
            "certificate_sha256": certificate_digest,
            "signatures": sig_counts,
            "counts": dict(auditor.count),
            "used_words": len(auditor.used_words),
            "negative_controls": controls,
            "seconds": round(time.monotonic() - start, 3),
        }
        print(json.dumps(result, sort_keys=True))
        return 0
    except Exception as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc),
                          "seconds": round(time.monotonic() - start, 3)}, sort_keys=True))
        return 1


if __name__ == "__main__":
    sys.exit(main())
