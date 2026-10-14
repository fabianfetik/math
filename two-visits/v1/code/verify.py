"""Check a finite 2-Visits output certificate against the visit constraints.

Feasible certificates supply a word. Accepted infeasibility certificates
identify the critical family B_n and its sum-of-gaps obstruction.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
from typing import Any


class VerificationError(ValueError):
    """An invalid output certificate."""


def verify_document(document: Any) -> str:
    """Return the certified status, or raise VerificationError."""
    if not isinstance(document, dict):
        raise VerificationError('Certificate must be a JSON object')
    deadlines = document.get('deadlines')
    if not isinstance(deadlines, list) or any(type(d) is not int or d < 1 for d in deadlines):
        raise VerificationError('Deadlines must be a list of positive integers')
    n = len(deadlines)
    status = document.get('status')
    if status == 'feasible':
        word = document.get('word')
        if not isinstance(word, list) or len(word) != 2 * n:
            raise VerificationError('Word must have exactly 2n positions')
        visits: list[list[int]] = [[] for _ in deadlines]
        for position, label in enumerate(word, start=1):
            if type(label) is not int or not 0 <= label < n:
                raise VerificationError(f'Invalid label at position {position}')
            visits[label].append(position)
            if len(visits[label]) > 2:
                raise VerificationError(f'Label {label} appears more than twice')
        for label, positions in enumerate(visits):
            if len(positions) != 2:
                raise VerificationError(f'Label {label} does not appear twice')
            first, second = positions
            if first > deadlines[label] or second - first > deadlines[label]:
                raise VerificationError(f'Deadline violated by label {label}')
        return status
    if status == 'infeasible':
        if n < 2 or sorted(deadlines) != [n - 1, *([n] * (n - 1))]:
            raise VerificationError('Only the critical B_n family has this negative certificate')
        expected = {
            'family': 'B_n',
            'n': n,
            'forced_total_gap': n * n,
            'deadline_sum': n * n - 1,
            'density': str(1 + Fraction(1, n * (n - 1))),
        }
        submitted = document.get('certificate')
        if (not isinstance(submitted, dict)
                or any(type(submitted.get(key)) is not type(value) for key, value in expected.items())
                or submitted != expected):
            raise VerificationError('Critical-family arithmetic certificate is incorrect')
        return status
    raise VerificationError('Status must be feasible or infeasible')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', help='JSON output from construct.py, or - for stdin')
    args = parser.parse_args()
    try:
        source = sys.stdin.read() if args.certificate == '-' else Path(args.certificate).read_text()
        document = json.loads(source)
        status = verify_document(document)
    except (OSError, json.JSONDecodeError, VerificationError) as error:
        print(f'Invalid certificate: {error}', file=sys.stderr)
        return 1
    print(json.dumps({'valid': True, 'status': status, 'tasks': len(document['deadlines'])}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
