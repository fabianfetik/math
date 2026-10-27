#!/usr/bin/env python3
"""Independent exact replay of exceptional six-head and supporting two-tail regions.

This file deliberately does not import either archived verifier or discovery
code.  The two archives and two-tail source's frozen certificate are treated as data.
The output is JSON on stdout; normal execution does not write any files.
"""

from __future__ import annotations

import argparse
import copy
import gzip
import hashlib
import json
import math
import zipfile
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path


PACKAGE = Path(__file__).resolve().parents[1]
R154B = PACKAGE / "data/exceptional-six-head.zip"
R064 = PACKAGE / "data/multiple-head-foundation.zip"
T093 = PACKAGE / "data/two-tail-source"
ALPHA = F(3403, 4290)


def insist(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def fraction_list(items):
    return tuple(F(x) for x in items)


def load_zip_json(z: zipfile.ZipFile, name: str):
    raw = z.read(name)
    return json.loads(gzip.decompress(raw) if name.endswith(".gz") else raw)


def mixed_upper(tail: tuple[int, ...]) -> F:
    reward = F(1, 22) if 21 in tail else F(1, 2 * (tail[0] + 1))
    return F(5, 6) + reward - sum((F(1, d + 1) for d in tail), F())


def admits(rate: F, cap: tuple[F, bool]) -> bool:
    return rate < cap[0] or (rate == cap[0] and cap[1])


def first_integer_period(cap: tuple[F, bool]) -> int:
    d = max(1, cap[0].denominator // cap[0].numerator)
    while not admits(F(1, d), cap):
        d += 1
    insist(d == 1 or not admits(F(1, d - 1), cap), "nonminimal child period")
    return d


def cyclic_cap(word: str, selected: frozenset[str]) -> tuple[F, bool]:
    """Compute the maximal ordinary cap by rotating each interval directly.

    A period with k visits has maximum possible rate k/n. For each residual
    length l, a window containing m visits admits r iff floor(l*r)<=m.
    Thus its cutoff (m+1)/l is open. We slide every interval, rather than
    using the archived verifier's duplicated-prefix vector of minima.
    """
    bits = [int(s in selected) for s in word]
    n = len(bits)
    insist(n > 0 and any(bits), "empty source stream")
    value, closed = F(sum(bits), n), True
    doubled = bits + bits
    for length in range(1, n):
        count = sum(doubled[:length])
        minimum = count
        for start in range(1, n):
            count += doubled[start + length - 1] - doubled[start - 1]
            if count < minimum:
                minimum = count
        edge = F(minimum + 1, length)
        if edge <= value:
            value, closed = edge, False
    return value, closed


def gap(word: str, symbol: str) -> int:
    positions = [i for i, x in enumerate(word) if x == symbol]
    insist(bool(positions), "empty child word")
    return max(b - a for a, b in zip(positions, positions[1:] + [positions[0] + len(word)]))


def source_masks(word: str, heads: list[int], groups: list[list[int]]):
    alphabet = sorted(set(word))
    used = 0
    for mask in heads + [m for m, _ in groups]:
        insist(type(mask) is int and 0 < mask < (1 << len(alphabet)), "invalid carrier mask")
        insist((used & mask) == 0, "overlapping source carriers")
        used |= mask
    insist(all(type(k) is int and k >= 1 for _, k in groups), "invalid carrier multiplicity")

    def symbols(mask: int) -> frozenset[str]:
        return frozenset(s for i, s in enumerate(alphabet) if mask & (1 << i))

    return [symbols(m) for m in heads], [(symbols(m), k) for m, k in groups]


def physical_child_gaps(word: str, groups) -> tuple[int, ...]:
    multiplier = 1
    for symbols, count in groups:
        insist(type(count) is int and count >= 1, "invalid split multiplicity")
        visits = sum(symbol in symbols for symbol in word)
        insist(visits > 0, "empty tail carrier")
        multiplier = math.lcm(multiplier, count // math.gcd(count, visits))
    total_period = len(word) * multiplier
    positions = [[[] for _ in range(count)] for _, count in groups]
    visits = [0] * len(groups)
    for tick in range(total_period):
        symbol = word[tick % len(word)]
        for index, (symbols, count) in enumerate(groups):
            if symbol in symbols:
                positions[index][visits[index] % count].append(tick)
                visits[index] += 1
                break
    result = []
    for index, (_, count) in enumerate(groups):
        insist(visits[index] % count == 0, "split phases do not close")
        for child in positions[index]:
            insist(bool(child), "empty split child")
            result.append(max(b - a for a, b in zip(child, child[1:] + [child[0] + total_period])))
    return tuple(sorted(result))


def envelope_excludes(lower: tuple[F, ...], tail: tuple[int, ...], U: F) -> bool:
    """Exact convex piecewise-affine lower bound for failures of every cut."""
    n = 6 + len(tail)
    start = max([lower[0], F(1, n)] +
                [(1 - F(n - j, tail[j - 6])) / j for j in range(6, n)])
    stop = U - sum(lower[1:])
    if start > stop:
        return True
    switches = {start, stop}
    for j in range(1, 6):
        switch = (1 - (n - j) * lower[j]) / j
        if start <= switch <= stop:
            switches.add(switch)
    for t in switches:
        charge = t + sum((max(lower[j], (1 - j*t) / (n-j)) for j in range(1, 6)), F())
        if charge < U:
            return False
    return True


class R154bSources:
    def __init__(self, templates, searches):
        self.data = templates
        self.words = {}
        self.checked = set()
        self.counts = Counter()
        for release in searches:
            for row in release["words"]:
                key = row["id"]
                insist(key not in self.words or self.words[key] == row, "conflicting literal word ID")
                self.words[key] = row

    @lru_cache(None)
    def cap(self, word: str, symbols: frozenset[str]):
        self.counts["source_masks"] += 1
        return cyclic_cap(word, symbols)

    @lru_cache(None)
    def box(self, serialized: str):
        proof = json.loads(serialized)
        kind = proof["kind"]
        if kind == "template":
            mode, index = proof["ref"].split(":")
            insist(mode in ("flat", "gap"), "unpermitted inherited template kind")
            record = self.data[mode][int(index)]
            word = self.data["words"][record["word"]]
            if mode == "flat":
                alphabet = sorted(set(word))
                sizes = record["sizes"]
                insist(len(sizes) == len(alphabet), "flat stream count mismatch")
                expanded = []
                for label, size in zip(alphabet, sizes):
                    insist(type(size) is int and size >= 0, "invalid flat rotor")
                    if size:
                        rate, closed = self.cap(word, frozenset((label,)))
                        expanded.extend([(rate / size, closed)] * size)
                expanded.sort(reverse=True)
                insist(expanded == [(F(v), flag) for v, flag in record["caps"]], "false flat caps")
                insist(len(expanded) >= 6, "too few source streams")
                heads = tuple(expanded[:6])
                requirements = tuple(first_integer_period(cp) for cp in expanded[6:])
            else:
                head_masks, group_masks = source_masks(word, record["heads"], record["groups"])
                insist(len(head_masks) == 6, "wrong number of head carriers")
                heads = tuple(self.cap(word, symbols) for symbols in head_masks)
                requirements = physical_child_gaps(word, group_masks)
                insist(heads == tuple((F(v), cl) for v, cl in record["caps"]), "false grouped caps")
                insist(requirements == tuple(record["requirements"]), "false grouped child gaps")
            self.checked.add(proof["ref"])
        elif kind == "new_word":
            record = self.words[proof["id"]]
            word = record["word"]
            labels = record["head_labels"] + record["tail_labels"]
            insist(len(labels) == len(set(labels)) and set(labels) == set(word), "invalid new word labels")
            insist(len(word) == record["period"] and len(record["head_labels"]) == 6,
                   "invalid new word period/heads")
            heads = tuple(self.cap(word, frozenset((s,))) for s in record["head_labels"])
            requirements = tuple(sorted(gap(word, s) for s in record["tail_labels"]))
            insist(heads == tuple((F(v), cl) for v, cl in record["caps"]), "false new-word caps")
            insist(requirements == tuple(record["requirements"]), "false new-word gaps")
            self.checked.add(proof["id"])
        else:
            raise ValueError("unpermitted source kind: " + str(kind))
        insist(list(heads) == sorted(heads, reverse=True), "head caps not ordered")
        insist(list(requirements) == sorted(requirements), "tail requirements not ordered")
        self.counts["source_boxes"] += 1
        return heads, requirements


class T093Sources:
    def __init__(self, templates):
        self.data = templates
        self.checked = set()
        self.counts = Counter()

    @lru_cache(None)
    def cap(self, word: str, symbols: frozenset[str]):
        self.counts["source_masks"] += 1
        return cyclic_cap(word, symbols)

    @lru_cache(None)
    def box(self, ref: str):
        mode, index = ref.split(":")
        insist(mode in ("flat", "paid"), "two-tail source proof uses unsupported source")
        record = self.data[mode][int(index)]
        word = self.data["words"][record["word"]]
        if mode == "flat":
            alphabet = sorted(set(word))
            insist(len(record["sizes"]) == len(alphabet), "two-tail source flat sizes mismatch")
            expanded = []
            for label, size in zip(alphabet, record["sizes"]):
                insist(type(size) is int and size >= 0, "invalid two-tail source flat split")
                if size:
                    rate, closed = self.cap(word, frozenset((label,)))
                    expanded.extend([(rate / size, closed)] * size)
            expanded.sort(reverse=True)
            insist(expanded == [(F(v), cl) for v, cl in record["caps"]], "two-tail source false flat cap")
            heads = tuple(expanded[:6])
            requirements = tuple(first_integer_period(cp) for cp in expanded[6:])
        else:
            head_masks, group_masks = source_masks(word, record["heads"], record["groups"])
            insist(len(head_masks) == 6, "two-tail source wrong number of heads")
            heads = tuple(self.cap(word, symbols) for symbols in head_masks)
            requirements = tuple(sorted(first_integer_period((self.cap(word, symbols)[0] / count,
                                                               self.cap(word, symbols)[1]))
                                        for symbols, count in group_masks for _ in range(count)))
            insist(heads == tuple((F(v), cl) for v, cl in record["caps"]), "two-tail source false paid cap")
            insist(requirements == tuple(record["requirements"]), "two-tail source false paid requirement")
        insist(list(heads) == sorted(heads, reverse=True), "two-tail source head caps unordered")
        self.checked.add(ref)
        self.counts["source_boxes"] += 1
        return heads, requirements


def normalize(lower, strict, single_tail_gap):
    lower, strict = list(lower), list(strict)
    if single_tail_gap is not None and lower[4] - single_tail_gap >= lower[5]:
        lower[5], strict[5] = lower[4] - single_tail_gap, True
    return tuple(lower), tuple(strict)


def child_state(lower, strict, index, cap):
    lower, strict = list(lower), list(strict)
    rate, closed = cap
    insist(rate >= lower[index], "source cap below branch lower bound")
    if rate > lower[index]:
        lower[index], strict[index] = rate, closed
    else:
        strict[index] = strict[index] or closed
    for j in range(index - 1, -1, -1):
        if lower[j] < lower[j+1]:
            lower[j], strict[j] = lower[j+1], strict[j+1]
        elif lower[j] == lower[j+1]:
            strict[j] = strict[j] or strict[j+1]
    return tuple(lower), tuple(strict)


def verify_region(row, sources, t093=False):
    tail = tuple(row["tail"])
    insist(tail and tail == tuple(sorted(tail)) and all(11 <= c <= 21 for c in tail),
           "invalid integer-tail signature")
    insist(12 + len(tail) <= 19, "outside mixed-core domain")
    U = mixed_upper(tail)
    insist(F(row["U"]) == U and U > F(6, 11), "wrong image guard")
    gamma = None
    if not t093 and row["bottom_gap_bound"] is not None:
        gamma = F(row["bottom_gap_bound"])
        insist(len(tail) == 1 and tail[0] in (12, 13, 21), "illegal marked-gate signature")
        insist(gamma == U - ALPHA and gamma > 0, "false marked-gate threshold")
        insist(U - F(1, 11) < ALPHA, "marked-gate second term not paid")
    if not t093:
        insist((gamma is not None) == (len(tail) == 1 and tail[0] in (12, 13, 21)),
               "missing or extraneous marked-gate premise")
    if t093:
        insist(tail == (11, 18), "two-tail source wrong imported signature")
    nodes = row["nodes"]
    insist(bool(nodes), "empty region proof")
    seen, active = set(), set()
    counts = Counter()

    def visit(index, lower, strict):
        lower, strict = normalize(lower, strict, gamma)
        insist(type(index) is int and 0 <= index < len(nodes), "invalid node index")
        node = nodes[index]
        insist(fraction_list(node["lower"]) == lower and tuple(node["strict"]) == strict,
               "node state does not match branch")
        insist(len(lower) == len(strict) == 6 and all(type(b) is bool for b in strict),
               "invalid state dimensions or flags")
        insist(list(lower) == sorted(lower, reverse=True) and lower[-1] >= F(1, 11),
               "head order or minimum lost")
        insist(index not in active, "cycle in cover DAG")
        if index in seen:
            return
        active.add(index)
        seen.add(index)
        kind = node["kind"]
        counts[kind] += 1
        if kind == "sum":
            insist(sum(lower) >= U, "false empty-sum leaf")
        elif kind == "envelope":
            insist(envelope_excludes(lower, tail, U), "false two-group exclusion")
        elif kind == "box":
            if t093:
                heads, requirements = sources.box(node["template"])
            else:
                heads, requirements = sources.box(json.dumps(node["proof"], sort_keys=True))
                insist(heads == tuple((F(v), cl) for v, cl in node["caps"]),
                       "node cap differs from source")
            insist(len(requirements) == len(tail) and all(a <= b for a, b in zip(requirements, tail)),
                   "source cannot serve actual integer tails")
            insist(len(heads) == 6 and all(rate > bound or
                                          (rate == bound and closed and not is_strict)
                                          for (rate, closed), bound, is_strict in zip(heads, lower, strict)),
                   "source box does not intersect current region correctly")
            edges = node["children"]
            children = dict(edges)
            insist(len(children) == len(edges) and all(type(i) is int for i in children),
                   "duplicate/invalid branch")
            needed = set()
            for i, cap in enumerate(heads):
                child_lower, child_strict = child_state(lower, strict, i, cap)
                if sum(child_lower) >= U:
                    continue
                needed.add(i)
                insist((child_lower, child_strict) != (lower, strict), "nondecreasing branch")
                insist(i in children, "missing nonempty cap complement")
                visit(children[i], child_lower, child_strict)
            insist(set(children) == needed, "extra or missing branch")
        else:
            raise ValueError("unknown region node kind")
        active.remove(index)

    visit(0, (F(1, 11),)*6, (False,)*6)
    insist(len(seen) == len(nodes), "unreachable certificate nodes")
    return counts


def load_data():
    with zipfile.ZipFile(R154B) as archive:
        templates = load_zip_json(archive, "outputs/templates.json.gz")
        covers = load_zip_json(archive, "outputs/adaptive_release_covers.json.gz")
        historical = load_zip_json(archive, "inputs/remaining-six-head-signatures.json")
        searches = [load_zip_json(archive, "outputs/words.json")]
    t093_templates = json.loads(gzip.decompress((T093 / "templates.json.gz").read_bytes()))
    t093_covers = json.loads(gzip.decompress((T093 / "covers.json.gz").read_bytes()))
    with zipfile.ZipFile(R064) as archive:
        r064_rows = json.loads(archive.read("outputs/cover_p6_aug5_results.json"))
    return templates, covers, historical, searches, t093_templates, t093_covers, r064_rows


def run(data=None):
    if data is None:
        data = load_data()
    templates, covers, historical, searches, t093_templates, t093_covers, r064_rows = data
    inherited = {tuple(c) for c in historical["remaining_six_head_signatures"]}
    r064_residual = {tuple(r["tail"]) for r in r064_rows if r["status"] == "UNCOVERED"}
    insist(len(r064_rows) == 4846 and len(r064_residual) == 89, "multiple-head foundation baseline count changed")
    r064_small = [r for r in r064_rows if len(r["tail"]) <= 2]
    insist(len(r064_small) == 77 and sum(r["status"] == "COVERED" for r in r064_small) == 47,
           "multiple-head foundation one/two-tail strata changed")
    t093_gain = {tuple(r["tail"]) for r in t093_covers["gap"]["rows"]
                 if r["status"] == "COVERED"}
    insist(len(t093_gain) == 5 and (11, 18) in t093_gain and t093_gain <= r064_residual,
           "two-tail source gain inventory changed")
    insist(inherited == r064_residual - t093_gain - {(11,)},
           "exceptional six-head inherited inventory does not follow multiple-head foundation/two-tail source/inherited source selection")
    required = {c for c in inherited if len(c) <= 2}
    rows = {tuple(r["tail"]): r for r in covers["rows"] if len(r["tail"]) <= 2}
    insist(len(rows) == 28 and set(rows) == required, "exceptional six-head required-region inventory mismatch")
    insist({c for c in required if len(c) == 1} == {(12,), (13,), (21,)},
           "single-tail inventory mismatch")
    insist(sum(len(c) == 2 for c in required) == 25, "two-tail inventory mismatch")
    insist((11, 18) not in inherited, "two-tail source region incorrectly counted as exceptional six-head")
    source154 = R154bSources(templates, searches)
    totals154 = Counter()
    for tail, row in sorted(rows.items()):
        insist(row["status"] == "COVERED", "unfinished exceptional six-head required region")
        totals154.update(verify_region(row, source154))
    old_rows = [r for r in t093_covers["paid"]["rows"] if r["tail"] == [11, 18]]
    insist(len(old_rows) == 1 and old_rows[0]["status"] == "COVERED", "two-tail source paid import absent")
    source093 = T093Sources(t093_templates)
    totals093 = verify_region(old_rows[0], source093, t093=True)
    return {
        "status": "PASS",
        "scope": "28 exceptional six-head q<=2 regions plus two-tail source (11,18), exact local second implementation",
        "imported_r064_positive_regions": 47,
        "r154b": {"regions": len(rows), "nodes": sum(totals154.values()),
                  "node_kinds": dict(totals154), "used_sources": len(source154.checked),
                  "source_masks": source154.counts["source_masks"]},
        "t093_11_18": {"regions": 1, "nodes": sum(totals093.values()),
                       "node_kinds": dict(totals093), "used_sources": len(source093.checked),
                       "source_masks": source093.counts["source_masks"]},
        "sha256": {"r154b_zip": hashlib.sha256(R154B.read_bytes()).hexdigest(),
                   "r064_zip": hashlib.sha256(R064.read_bytes()).hexdigest(),
                   "t093_templates": hashlib.sha256((T093 / "templates.json.gz").read_bytes()).hexdigest(),
                   "t093_covers": hashlib.sha256((T093 / "covers.json.gz").read_bytes()).hexdigest()},
    }


def controls(original):
    outcomes = {}

    def must_reject(name, change):
        data = copy.deepcopy(original)
        change(data)
        try:
            run(data)
        except (ValueError, AssertionError, KeyError, IndexError, TypeError, ZeroDivisionError):
            outcomes[name] = "REJECTED"
        else:
            raise ValueError("negative control accepted: " + name)

    def missing_branch(data):
        rows = data[1]["rows"]
        node = next(n for r in rows if r["tail"] == [12] for n in r["nodes"]
                    if n["kind"] == "box" and n["children"])
        node["children"].pop()

    def false_closed_cap(data):
        rows = data[1]["rows"]
        node = next(n for r in rows if r["tail"] == [12] for n in r["nodes"]
                    if n["kind"] == "box" and n["proof"]["kind"] == "template"
                    and n["proof"]["ref"].startswith("flat:"))
        ref = int(node["proof"]["ref"].split(":")[1])
        caps = data[0]["flat"][ref]["caps"]
        index = next(i for i, x in enumerate(caps) if not x[1])
        caps[index][1] = True

    def moved_marked_gate(data):
        row = next(r for r in data[1]["rows"] if r["tail"] == [12])
        row["bottom_gap_bound"] = str(F(row["bottom_gap_bound"]) + F(1, 100000))

    def false_t093_paid(data):
        row = next(r for r in data[5]["paid"]["rows"] if r["tail"] == [11, 18])
        node = next(n for n in row["nodes"] if n["kind"] == "box" and n["template"].startswith("paid:"))
        index = int(node["template"].split(":")[1])
        data[4]["paid"][index]["requirements"][0] -= 1

    for name, change in (("missing_complement", missing_branch),
                         ("false_closed_endpoint", false_closed_cap),
                         ("moved_marked_gate", moved_marked_gate),
                         ("false_two-tail source_tail_requirement", false_t093_paid)):
        must_reject(name, change)
    return outcomes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    data = load_data()
    result = run(data)
    if args.negative_controls:
        result["negative_controls"] = controls(data)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
