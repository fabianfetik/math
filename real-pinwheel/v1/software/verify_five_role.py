#!/usr/bin/env python3
"""Independent stdlib replay of the five-role finite-cover certificate.

Usage::

    python3 software/verify_five_role.py data/five-role

The evidence root is supplied explicitly so this script can be run against an
extracted receipt without relying on the repository layout.  It deliberately
does not import the delivered verifier, discovery code, or a solver.  Python
assertions are part of the checker, so optimized execution fails closed.
"""

import argparse
import json
import math
from collections import Counter
from fractions import Fraction as F
from pathlib import Path


if not __debug__:
    raise RuntimeError("five-role replay requires assertions: do not use Python -O or -OO")


FORMAT = "P001-R021-rational-refutation-v1"
EXPECTED_STREAMS = 13
EXPECTED_WORDS = 84
EXPECTED_ATOMS = 233
EXPECTED_NODES = 5393


def same_formula(left, right):
    """Boolean constants and integer atom IDs are different constructors."""
    if type(left) is not type(right):
        return False
    if isinstance(left, tuple):
        return len(left) == len(right) and all(
            same_formula(a, b) for a, b in zip(left, right)
        )
    return left == right


def primitive(values):
    values = [F(x) for x in values]
    denominator = math.lcm(*(value.denominator for value in values))
    integers = [int(value * denominator) for value in values]
    divisor = math.gcd(*integers)
    return tuple(integers) if not divisor else tuple(x // divisor for x in integers)


def load_json(path):
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def schema(data, certificate):
    assert isinstance(data, dict) and set(data) == {"streams", "words"}
    assert isinstance(data["streams"], list) and len(data["streams"]) == EXPECTED_STREAMS
    assert isinstance(data["words"], list) and len(data["words"]) == EXPECTED_WORDS
    assert isinstance(certificate, dict)
    assert certificate.get("format") == FORMAT
    assert isinstance(certificate.get("atoms"), list)
    assert isinstance(certificate.get("nodes"), list)
    assert len(certificate["atoms"]) == EXPECTED_ATOMS
    assert len(certificate["nodes"]) == EXPECTED_NODES
    assert set(certificate) == {"format", "atoms", "nodes", "root"}


def atom_table(certificate):
    rows = []
    ids = {}
    for number, row in enumerate(certificate["atoms"], 1):
        assert type(row) is list and len(row) == 6
        assert all(type(value) is int for value in row)
        row = tuple(row)
        assert row == primitive(row) and any(row[:5]) and row not in ids
        rows.append(row)
        ids[row] = number
    assert len(rows) == EXPECTED_ATOMS
    return rows, ids


def atom(values, ids):
    row = primitive(values)
    if not any(row[:5]):
        return row[5] <= 0
    assert row in ids, ("certificate omitted atom", row)
    return ids[row]


def normalize(operator, arguments):
    identity = operator == "and"
    parts = []
    for argument in arguments:
        if argument is identity:
            continue
        if argument is (not identity):
            return not identity
        if isinstance(argument, tuple) and argument[0] == operator:
            parts.extend(argument[1:])
        else:
            parts.append(argument)
    # repr keys keep Boolean constants distinct from integer atom IDs.
    parts = list({repr(value): value for value in parts}.values())
    if any(any(same_formula(nnot(value), part) for part in parts) for value in parts):
        return not identity
    if not parts:
        return identity
    return (operator, *sorted(parts, key=repr)) if len(parts) > 1 else parts[0]


def nnot(form):
    if type(form) is bool:
        return not form
    if type(form) is int:
        return -form
    assert isinstance(form, tuple) and form[0] in ("and", "or")
    opposite = "or" if form[0] == "and" else "and"
    return normalize(opposite, [nnot(child) for child in form[1:]])


def inequality(coefs, bound, ids, strict=False):
    row = [F(value) for value in coefs] + [-F(bound)]
    return nnot(atom([-value for value in row], ids)) if strict else atom(row, ids)


def count_caps(word):
    period = len(word)
    result = []
    for label in "12345":
        cap = F(word.count(label), period)
        closed = True
        for length in range(1, period):
            minimum = min(
                sum(word[(start + offset) % period] == label for offset in range(length))
                for start in range(period)
            )
            candidate = F(minimum + 1, length)
            if candidate < cap:
                cap, closed = candidate, False
            elif candidate == cap:
                closed = False
        result.append((cap, closed))
    return result


def cycles(case):
    assert isinstance(case.get("id"), str) and case["id"]
    group = "".join(str(value) for value in case["G"])
    header = [str(value) for value in case["H"]]
    kind = case["id"][0]
    if kind in "AE":
        other = "".join(header)
    elif kind == "B":
        a, b, d, e = header
        other = a + b + a + d + a + b + a + e
    elif kind == "C":
        a, b, d, e = header
        other = a + b + d + a + b + e
    elif kind == "D":
        a, b, d = header
        other = a + b + a + d
    else:
        raise AssertionError(("unknown stream family", case["id"]))
    return group, other


def gaps(word):
    result = {}
    for label in set(word):
        positions = [index for index, value in enumerate(word) if value == label]
        values = [
            right - left
            for left, right in zip(positions, positions[1:] + [positions[0] + len(word)])
        ]
        assert values and len(set(values)) == 1
        result[int(label)] = values[0]
    return result


def catalogue_axioms(data, ids):
    axioms = {}
    axioms["density"] = normalize(
        "and",
        [
            inequality([1] * 5, F(5, 6), ids),
            inequality([-1] * 5, -F(5, 6), ids),
        ],
    )
    for index in range(4):
        row = [0] * 5
        row[index], row[index + 1] = -1, 1
        axioms["order" + str(index)] = inequality(row, 0, ids)
    row = [0] * 5
    row[4] = -1
    axioms["positive"] = inequality(row, 0, ids, strict=True)

    entries = data["streams"] + data["words"]
    assert len(entries) == len({entry["id"] for entry in entries})
    for case in data["streams"]:
        assert isinstance(case.get("G"), list) and all(type(x) is int for x in case["G"])
        assert isinstance(case.get("H"), list) and all(type(x) is int for x in case["H"])
        assert case["G"] == sorted(set(case["G"])) and case["G"]
        assert isinstance(case.get("p"), list) and all(type(x) is int for x in case["p"])
        assert isinstance(case.get("q"), list) and all(type(x) is int for x in case["q"])
        u, v = cycles(case)
        assert set(u).isdisjoint(v) and set(u + v) == set("12345")
        gu, gv = gaps(u), gaps(v)
        assert [gu[i] for i in case["G"]] == case["p"]
        assert [gv[i] for i in case["H"]] == case["q"]
        rows = case["inequalities"]
        assert isinstance(rows, list) and rows
        assert all(
            isinstance(row, list)
            and len(row) == 5
            and all(type(value) is int and value >= 0 for value in row)
            for row in rows
        )
        for i, p in gu.items():
            for j, q in gv.items():
                full = [0] * 5
                full[i - 1], full[j - 1] = p, q
                assert any(
                    all(sum(row[:t]) >= sum(full[:t]) for t in range(1, 6))
                    for row in rows
                )
        axioms[case["id"]] = normalize(
            "or", [nnot(inequality(row, 1, ids)) for row in rows]
        )

    for word_case in data["words"]:
        assert isinstance(word_case.get("word"), str)
        assert word_case["word"] and set(word_case["word"]) == set("12345")
        assert isinstance(word_case.get("rate_caps"), list)
        assert len(word_case["rate_caps"]) == 5
        assert all(
            isinstance(cap, list)
            and len(cap) == 2
            and type(cap[1]) is bool
            for cap in word_case["rate_caps"]
        )
        caps = count_caps(word_case["word"])
        expected = [(F(value), closed) for value, closed in word_case["rate_caps"]]
        assert caps == expected, word_case["id"]
        tests = []
        for index, (bound, closed) in enumerate(caps):
            row = [0] * 5
            row[index] = 1
            tests.append(nnot(inequality(row, bound, ids, strict=not closed)))
        axioms[word_case["id"]] = normalize("or", tests)

    assert len(axioms) == 6 + EXPECTED_STREAMS + EXPECTED_WORDS
    return axioms


def freeze(form):
    return tuple(freeze(child) for child in form) if isinstance(form, list) else form


def validate_formula(form, atom_count):
    if type(form) is bool:
        return
    if type(form) is int:
        assert 1 <= abs(form) <= atom_count
        return
    assert isinstance(form, tuple) and len(form) >= 2 and form[0] in ("and", "or")
    for child in form[1:]:
        validate_formula(child, atom_count)


def as_clause(form):
    if form is False:
        return frozenset()
    if type(form) is int:
        return frozenset([form])
    assert isinstance(form, tuple) and form[0] == "or"
    assert all(type(literal) is int for literal in form[1:])
    return frozenset(form[1:])


def constraints(form, atom_rows):
    if form is True:
        return []
    if form is False:
        return [((0, 0, 0, 0, 0, 1), False)]
    if type(form) is int:
        row = atom_rows[abs(form) - 1]
        return [(row, False)] if form > 0 else [(tuple(-x for x in row), True)]
    assert form[0] == "and"
    return [constraint for child in form[1:] for constraint in constraints(child, atom_rows)]


def replay(data, certificate):
    schema(data, certificate)
    atom_rows, atom_ids = atom_table(certificate)
    axioms = catalogue_axioms(data, atom_ids)

    conclusions = []
    dependencies = []
    stats = Counter()
    input_names = []
    linear_count = 0
    strict_zero_count = 0
    discharge_count = 0

    for index, node in enumerate(certificate["nodes"]):
        assert isinstance(node, dict) and isinstance(node.get("rule"), str)
        rule = node["rule"]
        stats[rule] += 1
        conclusion = freeze(node["conclusion"])
        validate_formula(conclusion, len(atom_rows))
        premises = node.get("premises", [])
        assert isinstance(premises, list)
        assert all(type(premise) is int and 0 <= premise < index for premise in premises)
        deps = set().union(*(dependencies[premise] for premise in premises))

        if rule == "input":
            name = node.get("name")
            assert isinstance(name, str) and not premises and name in axioms
            assert same_formula(conclusion, axioms[name])
            input_names.append(name)
            deps = set()
        elif rule == "hypothesis":
            assert not premises and type(conclusion) is int
            deps = {conclusion}
        elif rule == "and_elim":
            assert len(premises) == 1
            parent = conclusions[premises[0]]
            assert isinstance(parent, tuple) and parent[0] == "and"
            assert any(same_formula(conclusion, child) for child in parent[1:])
        elif rule == "resolve":
            assert len(premises) >= 2
            clause = set(as_clause(conclusions[premises[0]]))
            for premise in premises[1:]:
                literal = conclusions[premise]
                assert type(literal) is int and -literal in clause
                clause.remove(-literal)
            assert frozenset(clause) == as_clause(conclusion)
        elif rule == "linear":
            inequalities = [
                constraint
                for premise in premises
                for constraint in constraints(conclusions[premise], atom_rows)
            ]
            inequalities.extend(constraints(nnot(conclusion), atom_rows))
            weights = [F(value) for value in node["weights"]]
            assert len(weights) == len(inequalities)
            assert all(weight >= 0 for weight in weights) and any(weights)
            total = [
                sum(weight * constraint[0][column] for weight, constraint in zip(weights, inequalities))
                for column in range(6)
            ]
            assert total[:5] == [0] * 5
            has_strict = any(
                weight > 0 and constraint[1]
                for weight, constraint in zip(weights, inequalities)
            )
            assert total[5] > 0 or (total[5] == 0 and has_strict)
            linear_count += 1
            strict_zero_count += int(total[5] == 0 and has_strict)
        elif rule == "discharge":
            assert len(premises) == 1 and conclusions[premises[0]] is False
            literals = as_clause(conclusion)
            deps -= {-literal for literal in literals}
            discharge_count += 1
        else:
            raise AssertionError(("unknown proof rule", rule))

        conclusions.append(conclusion)
        dependencies.append(frozenset(deps))

    assert len(input_names) == len(axioms) == 103
    assert Counter(input_names) == Counter(axioms.keys())
    root = certificate["root"]
    assert type(root) is int and 0 <= root < len(conclusions)
    assert conclusions[root] is False and not dependencies[root]
    assert linear_count == 1197 and strict_zero_count == 173 and discharge_count == 385
    return {
        "verified": True,
        "format": FORMAT,
        "words": len(data["words"]),
        "streams": len(data["streams"]),
        "atoms": len(atom_rows),
        "nodes": len(conclusions),
        "rules": dict(stats),
        "strict_zero_farkas": strict_zero_count,
        "root": root,
        "root_dependencies": [],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "evidence_root",
        type=Path,
        help="extracted five-role proof-data directory",
    )
    args = parser.parse_args(argv)
    root = args.evidence_root
    data = load_json(root / "outputs" / "final-catalogue.json")
    certificate = load_json(root / "outputs" / "coverage-certificate.json")
    result = replay(data, certificate)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
