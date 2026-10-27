"""Bounded scheduling tests and package consistency checks (standard library).

Small-instance feasibility is checked with a separately implemented solver
that enforces the first-visit deadlines and the gaps between visits.
"""
from fractions import Fraction
from functools import lru_cache
import hashlib
import importlib.util
from itertools import combinations_with_replacement
import json
from math import comb, factorial
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'code' / f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require(test, message):
    if not test:
        raise AssertionError(message)


def oracle(deadlines):
    """Enumerate legal prefixes, with exact expiry pruning and a state cap."""
    n = len(deadlines)
    visited = 0

    @lru_cache(None)
    def visit(counts, first):
        nonlocal visited
        visited += 1
        if visited > 20000:
            raise RuntimeError('Oracle state budget exhausted; no feasibility conclusion')
        position = sum(counts) + 1
        if position == 2 * n + 1:
            return ()
        for i, count in enumerate(counts):
            if (count == 0 and position > deadlines[i]
                    or count == 1 and position > first[i] + deadlines[i]):
                return None
        for i, count in enumerate(counts):
            if count == 2:
                continue
            changed = list(counts)
            changed[i] += 1
            times = list(first)
            if count == 0:
                times[i] = position
            tail = visit(tuple(changed), tuple(times))
            if tail is not None:
                return (i,) + tail
        return None

    word = visit((0,) * n, (0,) * n)
    return word, visited


def certificate(deadlines):
    n = len(deadlines)
    return {'deadlines': deadlines, 'status': 'infeasible',
            'certificate': {'family': 'B_n', 'n': n,
                            'forced_total_gap': n * n, 'deadline_sum': n * n - 1,
                            'density': str(1 + Fraction(1, n * (n - 1)))}}


def main():
    construct, verifier = load('construct'), load('verify')
    counts, oracle_counts = {}, {}
    scheduled = critical = oracle_states = max_oracle_states = 0
    # 2,398 sorted inputs in the specified finite deadline boxes.
    domain = sum(comb(3 * n - 1, n) for n in range(2, 6))
    require(domain == 2398, 'Domain estimate changed')
    for n in range(2, 6):
        counts[n] = oracle_counts[n] = 0
        threshold = 1 + Fraction(1, n * (n - 1))
        for deadlines in combinations_with_replacement(range(1, 2 * n + 1), n):
            density = sum((Fraction(1, d) for d in deadlines), Fraction())
            expected_exception = deadlines == (n - 1,) + (n,) * (n - 1)
            if n <= 4:
                oracle_word, used = oracle(deadlines)
                oracle_states += used
                max_oracle_states = max(max_oracle_states, used)
                oracle_counts[n] += 1
                if oracle_word is not None:
                    verifier.verify_document({'deadlines': list(deadlines),
                                              'status': 'feasible', 'word': list(oracle_word)})
                if density <= threshold:
                    require((oracle_word is None) == expected_exception,
                            ('Independent oracle contradicts threshold', deadlines))
            if density > threshold:
                continue
            counts[n] += 1
            if expected_exception:
                try:
                    construct.schedule(deadlines)
                except construct.CriticalInfeasible:
                    critical += 1
                else:
                    raise AssertionError(('Missing critical exception', deadlines))
                verifier.verify_document(certificate(list(deadlines)))
            else:
                for ordered in (list(deadlines), list(reversed(deadlines))):
                    word = construct.schedule(ordered)
                    verifier.verify_document({'deadlines': ordered, 'status': 'feasible', 'word': word})
                    scheduled += 1

    examples = [[], [1], [2, 2], [13] * 13, [9] * 5, [4, 4, 5, 7],
                [3, 4, 4, 6], [2, 4, 4, 12], [6, 6] + [9] * 6,
                [9, 9] + [13] * 10, [10] * 3 + [13] * 9,
                [8] * 3 + [13] * 8, [13, 13] + [16] * 13 + [30],
                [100] * 100, [10 ** 120] * 2]
    traces = []
    for ds in examples:
        trace = []
        word = construct.schedule(ds, trace)
        verifier.verify_document({'deadlines': ds, 'status': 'feasible', 'word': word})
        traces.extend(x for x in trace if x['kind'] == 'sweep')
    require({(t['H'], tuple(t['widths'])) for t in traces}
            >= {(1, (1,)), (1, (2,)), (1, (1, 1)), (2, (1,))}, 'Four repair patterns not covered')
    require(any(t['t'] > 0 and t['M'] >= 13 for t in traces), 'Large-prefix example not covered')

    fixture = json.loads((ROOT / 'source/figures/repair-example.json').read_text())
    trace = []
    word = construct.schedule(fixture['deadlines'], trace)
    require(word == fixture['repaired_word'] and trace == [fixture['trace']], 'Example trace mismatch')
    for label, row in enumerate(fixture['position_table']):
        positions = [i for i, x in enumerate(word, 1) if x == label]
        require(positions + [positions[1] - positions[0]] == row, 'Example position table mismatch')
    require([word[i - 1] for i in fixture['anchors'][1:]] == fixture['P'], 'Example P mismatch')
    require([word[i - 1] for i in fixture['partners'][1:]] == fixture['Q'], 'Example Q mismatch')
    try:
        verifier.verify_document({'deadlines': fixture['deadlines'], 'status': 'feasible',
                                  'word': fixture['sorted_word']})
    except verifier.VerificationError:
        pass
    else:
        raise AssertionError('Sorted example unexpectedly legal')

    # Exercise the two command-line programs using only files in this package.
    for ds in ([1], fixture['deadlines'], [7] + [8] * 7):
        result = subprocess.run([sys.executable, str(ROOT / 'code/construct.py'), *map(str, ds)],
                                capture_output=True, text=True, check=True)
        checked = subprocess.run([sys.executable, str(ROOT / 'code/verify.py'), '-'],
                                 input=result.stdout, capture_output=True, text=True, check=True)
        require(json.loads(checked.stdout)['valid'], 'CLI round trip failed')
    outside = [1, 3, 5]
    verifier.verify_document({'deadlines': outside, 'status': 'feasible', 'word': [0, 0, 1, 1, 2, 2]})
    rejected = subprocess.run([sys.executable, str(ROOT / 'code/construct.py'), *map(str, outside)],
                              capture_output=True, text=True)
    require(rejected.returncode == 2 and 'outside' in rejected.stderr and not rejected.stdout,
            'An outside-promise input was misrepresented as infeasible')
    forged = [
        {'deadlines': [2, 2], 'status': 'feasible', 'word': w}
        for w in ([0, 0, 0, 1], [0, 1, True, 1], [0, 1, 1, 0])]
    forged.append({'deadlines': [2, 2], 'status': 'infeasible', 'certificate': {'family': 'B_n'}})
    for document in forged:
        try:
            verifier.verify_document(document)
        except verifier.VerificationError:
            pass
        else:
            raise AssertionError('Forged certificate accepted')

    md = (ROOT / 'source/manuscript.md').read_text()
    tex = (ROOT / 'source/paper.tex').read_text()
    tags = re.findall(r'\\tag\{(\d+\.\d+)\}', md)
    references = re.findall(r'(?<![\w\\])\((\d+\.\d+)\)', md)
    require(len(tags) == len(set(tags)), 'Duplicate equation tag')
    require(set(references) <= set(tags), 'Missing Markdown equation reference')
    require(re.findall(r'\\tag\{(\d+\.\d+)\}', tex) == tags, 'TeX equation order changed')
    require(set(re.findall(r'\\eqref\{eq:([^}]+)\}', tex)) <= set(tags), 'Missing TeX equation reference')
    citations = re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', tex)
    bibliography = re.findall(r'\\bibitem\[([^]]+)\]\{([^}]+)\}', tex)
    source_labels = re.findall(r'^- \[([^]]+)\]', md.split('## References\n', 1)[1], re.M)
    require([label for label, key in bibliography] == source_labels, 'Bibliography label mismatch')
    keys = {key for label, key in bibliography}
    require(len(keys) == len(bibliography), 'Duplicate bibliography key')
    require({x for citation in citations for x in citation.split(',')} <= keys, 'Missing citation target')
    if (ROOT / 'MANIFEST.sha256').exists():
        for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
            digest, name = line.split('  ', 1)
            path = ROOT / name
            require(path.is_relative_to(ROOT) and path.is_file(), 'Bad manifest path')
            require(hashlib.sha256(path.read_bytes()).hexdigest() == digest, f'Hash mismatch: {name}')
    print(json.dumps({'status': 'PASS', 'domain_inputs': domain,
                      'promised_inputs_by_n': counts, 'constructed_label_orders': scheduled,
                      'critical_instances': critical, 'oracle_inputs_by_n': oracle_counts,
                      'oracle_states': oracle_states, 'max_oracle_states_per_input': max_oracle_states,
                      'oracle_state_budget_per_input': 20000,
                      'largest_complete_word_language': factorial(8) // 2 ** 4,
                      'structured_examples': len(examples), 'equation_tags': len(tags)}, indent=2))


if __name__ == '__main__':
    main()
