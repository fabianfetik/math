#!/usr/bin/env python3
"""Check the exact selected terminal domain of Appendix B.

The larger calendar and cover inventories must also pass their packaged
acceptance programs. This check enumerates every selected signature, verifies
its actual residual classification, and matches its guard and root faces to
those accepted inventories. It also checks the two elementary source families
and the marked-source interfaces used instead of region graphs.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from itertools import combinations_with_replacement
from pathlib import Path
from zipfile import ZipFile
import argparse
import gzip
import hashlib
import json


ROOT = Path(__file__).resolve().parents[1]
D, ALPHA = F(5, 6), F(3403, 4290)
GRID = 465585120


def need(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def loads(raw: bytes):
    return json.loads(raw, object_pairs_hook=unique)


def archive_json(path: str, member: str):
    with ZipFile(ROOT / path) as archive:
        raw = archive.read(member)
    return loads(gzip.decompress(raw) if member.endswith(".gz") else raw)


def upper(tail: tuple[int, ...]) -> F:
    need(bool(tail) and tail == tuple(sorted(tail))
         and all(type(c) is int and 11 <= c <= 21 for c in tail), "invalid actual tail signature")
    gamma = F(1, 22) if tail[-1] == 21 else F(1, 2 * (tail[0] + 1))
    return D + gamma - sum((F(1, c + 1) for c in tail), F())


def selected_domain():
    result = set()
    for heads in range(8):
        for count in range(1, 9 - heads):
            for tail in combinations_with_replacement(range(11, 22), count):
                if heads + count <= 7 or (heads <= 6 and tail.count(21) >= 2):
                    result.add((heads, tail))
    return result


def two_parent_excludes(heads: int, tail: tuple[int, ...]) -> bool:
    """Recompute the root two-parent envelope, with the strict sum guard.

    All tail rates in the cut inequalities are 1/c, whereas the sum guard
    uses 1/(c+1). No volume, sampling, or stored status is used here.
    """
    n = heads + len(tail)
    lo = max([F(1, 11), F(1, n)] +
             [(1 - F(n - j, tail[j - heads])) / j for j in range(heads, n)])
    hi = upper(tail) - F(heads - 1, 11)
    if lo > hi:
        return True
    switches = {lo, hi} | {
        t for j in range(1, heads)
        if lo <= (t := (1 - F(n - j, 11)) / j) <= hi
    }
    return all(t + sum((max(F(1, 11), (1 - j * t) / (n - j))
                        for j in range(1, heads)), F()) >= upper(tail)
               for t in switches)


def word_caps(word: str):
    need(isinstance(word, str) and set(word) == {"1", "2", "3"}, "invalid analytic word labels")
    result, gaps = [], []
    period = len(word)
    for symbol in "123":
        positions = [t for t, x in enumerate(word) if x == symbol]
        count = len(positions)
        doubled = positions + [t + period for t in positions]
        cap, closed = F(count, period), True
        for rank in range(1, count + 1):
            span = max(doubled[start + rank] - doubled[start] for start in range(count))
            if span <= 1:
                continue
            edge = F(rank, span - 1)
            if edge <= cap:
                cap, closed = edge, False
        result.append((cap, closed))
        gaps.append(max(doubled[start + 1] - doubled[start] for start in range(count)))
    return tuple(result), tuple(gaps)


def analytic_two_head(spec):
    rows = spec["analytic_two_head_sources"]
    expected_words = ["1212132112", "213121211", "1211211213",
                      "121112113", "12111211121112113"]
    need([r["word"] for r in rows] == expected_words, "incomplete analytic selector")
    checked = []
    for row in rows:
        caps, gaps = word_caps(row["word"])
        need(all(type(flag) is bool for _, flag in row["caps"]), "invalid analytic cap endpoint")
        need(caps == tuple((F(rate), flag) for rate, flag in row["caps"]),
             "false analytic cap or closed endpoint")
        need(gaps[2] == row["tail_gap"], "false analytic tail gap")
        checked.append(caps)
    # Failure of both closed scalar cuts gives
    # (1-1/c)/2 < a < 2V-1 <= 2/3. The following five intervals
    # partition that open range, retaining their stated endpoint flags.
    a_caps = [(F(1, 2), False), (F(5, 9), True), (F(3, 5), False),
              (F(2, 3), False), (F(2, 3), False)]
    need([caps[0] for caps in checked] == a_caps, "analytic head bands do not match the source caps")
    inequalities = 0
    for c in range(11, 22):
        V = upper((c,))
        need(V <= D and 2 * V - 1 <= F(2, 3), "false outer analytic head bound")
        # In each band b is strictly below this bound. Equality of the
        # bound with an open source cap is therefore safe.
        bounds = [V - (1 - F(1, c)) / 2, V - F(1, 2), V - F(5, 9),
                  V - F(3, 5), V - F(3, 5)]
        bands = range(4) if c <= 20 else (0, 1, 2, 4)
        for i in bands:
            need(bounds[i] <= checked[i][1][0], f"uncovered analytic b-band: c={c}, band={i}")
            need(rows[i]["tail_gap"] <= c, f"analytic source cannot serve actual tail {c}")
            inequalities += 1
    return {"signatures": 11, "literal_words": 5,
            "strict_band_upper_inequalities": inequalities,
            "all_cyclic_cap_endpoints": "PASS"}


def one_head_inclusion(selected):
    targets = {sum(18 ** (c - 11) for c in tail): tail
               for p, tail in selected if p == 1}
    need(len(targets) == 15378, "one-head selection count changed")
    matched = {}
    with ZipFile(ROOT / "data/one-head-templates.zip") as archive:
        for raw in archive.open("routes.tsv"):
            fields = raw.split()
            need(len(fields) == 2, "malformed route row")
            code, face = map(int, fields)
            if code in targets:
                need(code not in matched, "duplicate selected one-head route")
                matched[code] = face
        need(set(matched) == set(targets), "selected one-head signature missing from checked routes")
        faces = {}
        needed_faces = set(matched.values())
        for raw in archive.open("faces.tsv"):
            fields = raw.split()
            need(len(fields) >= 5, "malformed template face")
            index = int(fields[0])
            if index in needed_faces:
                need(index not in faces, "duplicate selected face")
                faces[index] = int(fields[2])
    need(set(faces) == needed_faces, "missing selected literal template face")
    for code, index in matched.items():
        need(F(faces[index], GRID) >= upper(targets[code]),
             "selected head-sum guard exceeds accepted template guard")
    return {"signatures": len(matched), "referenced_templates": len(needed_faces),
            "guard_inclusion": "PASS"}


def residual_inclusion(selected):
    required = {(p, tail) for p, tail in selected if 2 <= p <= 6}
    found = set()
    count = 0
    with ZipFile(ROOT / "data/multiple-head-foundation.zip") as archive:
        for raw in archive.open("outputs/two_group_residual_signatures.csv"):
            fields = raw.decode("ascii").strip().split(",")
            need(len(fields) >= 2, "malformed residual signature")
            p, tail = int(fields[0]), tuple(map(int, fields[1:]))
            need(2 <= p <= 7 and 2 * p + len(tail) <= 19 and
                 tail == tuple(sorted(tail)) and all(11 <= c <= 21 for c in tail),
                 "residual signature outside checked inventory")
            count += 1
            if (p, tail) in required:
                need((p, tail) not in found, "duplicate selected residual signature")
                found.add((p, tail))
    need(count == 1164266 and found == required, "selected residual signature inventory incomplete")
    for p, tail in required:
        need(upper(tail) > F(p, 11), "empty selected root was deleted")
        need(not two_parent_excludes(p, tail), "false selected two-parent residual signature")
    return {"checked_inventory_rows": count, "selected_true_residuals": len(required),
            "actual_integer_tail_rates": "PASS"}


def graph_summary(row, p, tail, *, exceptional=False):
    need(row.get("p", p) == p and tuple(row.get("tail", tail)) == tail,
         "region signature mismatch")
    need(row.get("status", "COVERED") == "COVERED" and F(row["U"]) == upper(tail),
         "selected region has the wrong strict guard")
    nodes = row["nodes"]
    need(isinstance(nodes, list) and bool(nodes), "missing selected cover graph")
    root = nodes[0]
    lower, strict = (F(1, 11),) * p, (False,) * p
    if exceptional:
        gamma = F(row["bottom_gap_bound"])
        need(gamma == upper(tail) - ALPHA and gamma > 0, "false marked gate")
        need(upper(tail) - F(1, 11) < ALPHA, "second marked-source charge unpaid")
        if lower[4] - gamma >= lower[5]:
            lower = lower[:5] + (lower[4] - gamma,)
            strict = strict[:5] + (True,)
    need(tuple(map(F, root["lower"])) == lower and tuple(root["strict"]) == strict
         and len(root["strict"]) == p and all(type(flag) is bool for flag in root["strict"]),
         "selected region loses a closed root face or the strict narrow gate")
    return len(nodes)


def multi_head_inclusion(selected):
    needed = {(p, tail) for p, tail in selected if 2 <= p <= 5 and not (p == 2 and len(tail) == 1)}
    data = archive_json("data/multiple-head-terminal.zip", "release-certificate.json.gz")
    rows = data["regions"]
    seen, node_count = set(), 0
    for row in rows:
        key = (row["p"], tuple(row["tail"]))
        if key in needed:
            need(key not in seen, "duplicate selected terminal graph")
            node_count += graph_summary(row, *key)
            seen.add(key)
    need(seen == needed and len(seen) == 7524 and node_count == 339581,
         "selected terminal graph inventory incomplete")
    del data, rows
    six = {tail for p, tail in selected if p == 6}
    foundation_needed = {(c,) for c in range(14, 21)} | {(21, 21)}
    marked_needed = {(11,)}
    exceptional_needed = {(12,), (13,), (21,)}
    need(six == foundation_needed | marked_needed | exceptional_needed,
         "six-head selected domain is not partitioned")
    preliminary = archive_json("data/multiple-head-foundation.zip",
                               "outputs/cover_p6_aug5_certificates.json.gz")
    preliminary_nodes = 0
    for tail in sorted(foundation_needed):
        key = ",".join(map(str, tail))
        need(key in preliminary, "missing selected preliminary graph")
        preliminary_nodes += graph_summary(preliminary[key], 6, tail)
    need(preliminary_nodes == 1587, "preliminary selected graph census changed")
    del preliminary
    exceptional = archive_json("data/exceptional-six-head.zip", "outputs/adaptive_release_covers.json.gz")
    seen, exceptional_nodes = set(), 0
    for row in exceptional["rows"]:
        tail = tuple(row["tail"])
        if tail in exceptional_needed:
            need(tail not in seen, "duplicate selected exceptional graph")
            exceptional_nodes += graph_summary(row, 6, tail, exceptional=True)
            seen.add(tail)
    need(seen == exceptional_needed and exceptional_nodes == 1371,
         "exceptional selected graph inventory incomplete")
    # The ordinary marked theorem is supplied and separately checked in
    # Appendix A. Its strict charge interface pays the (6,(11)) source.
    need(upper((11,)) == F(19, 24) and F(19, 24) < ALPHA,
         "marked theorem does not cover selected six-head singleton")
    return {"terminal_graphs": len(needed), "terminal_nodes": node_count,
            "six_head_foundation_graphs": 8, "six_head_foundation_nodes": preliminary_nodes,
            "six_head_exceptional_graphs": 3, "six_head_exceptional_nodes": exceptional_nodes,
            "six_head_marked_interfaces": 1}


def run():
    spec = loads((ROOT / "data/small-minimum-domain.json").read_bytes())
    need(spec["schema"] == "selected-small-minimum-domain-1"
         and spec["head_minimum"] == {"rate": "1/11", "closed": True}
         and spec["tail_periods"] == [11, 21]
         and spec["ordinary_maximum_roles"] == 7
         and spec["paired_roles"] == 8
         and spec["paired_tail_period"] == 21
         and spec["paired_minimum_copies"] == 2
         and spec["head_sum_guard"] == "C < 5/6 + gamma(B) - sum(1/(c+1) for c in B)",
         "the selected domain differs from Appendix B")
    selected = selected_domain()
    counts = dict(sorted(Counter(p for p, tail in selected).items()))
    counts.setdefault(7, 0)
    need([counts[p] for p in range(8)] == [39831, 15378, 5368, 1650, 429, 88, 12, 0]
         and len(selected) == 62756, "selected signature census changed")
    for p, tail in selected:
        need(upper(tail) > F(p, 11), "selected nonempty head domain was omitted")
        if p == 0:
            need(len(tail) <= 8 and len(tail) <= min(tail), "round-robin word cannot serve actual tails")
    analytic = analytic_two_head(spec)
    one_head = one_head_inclusion(selected)
    residuals = residual_inclusion(selected)
    graphs = multi_head_inclusion(selected)
    serialization = "".join(f"{p}:" + ",".join(map(str, tail)) + "\n"
                            for p, tail in sorted(selected)).encode()
    return {"status": "PASS", "selected_signatures": len(selected),
            "signatures_by_head_count": counts,
            "selected_set_sha256": hashlib.sha256(serialization).hexdigest(),
            "round_robin_signatures": counts[0], "one_head": one_head,
            "analytic_two_head": analytic, "residuals": residuals,
            "graph_inclusion": graphs, "missing_selected_signatures": 0,
            "extra_selected_signatures": 0,
            "scope": "Exact selected-domain inclusion; larger inventories require their acceptance checks",
            "root_head_lower_face": "closed 1/11", "head_sum_guard": "strict",
            "source_cap_flags_and_narrow_gate": "preserved"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    try:
        print(json.dumps(run(), indent=2, sort_keys=True))
    except (ValueError, OSError, KeyError, IndexError, TypeError, ZeroDivisionError) as exc:
        raise SystemExit(f"Selected-domain verification failed: {exc}") from exc
