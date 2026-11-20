#!/usr/bin/env python3
"""Check a corral certificate directly from its cyclic partial sums."""
# Copyright (c) 2026 Fabian Fetik
# SPDX-License-Identifier: MIT
import argparse
import json
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, message):
    require(type(value) is int, message)
    return value


def verify(certificate):
    """Verify the original permutation/shift contract and all wrap gaps."""
    require(isinstance(certificate, dict), "certificate must be a JSON object")
    required = {"height", "order", "width", "rows", "permutations", "shifts"}
    require(required <= certificate.keys(), "certificate fields are missing")
    height = integer(certificate["height"], "height must be an integer")
    order = integer(certificate["order"], "order must be an integer")
    width = integer(certificate["width"], "width must be an integer")
    require(height >= 1 and order == 2 * height - 1, "certificate must have positive height and optimal order")
    require(width == order * (order + 1) // 2, "incorrect cycle width")
    rows = certificate["rows"]
    permutations = certificate["permutations"]
    shifts = certificate["shifts"]
    require(all(isinstance(x, list) and len(x) == height for x in (rows, permutations, shifts)),
            "incorrect number of rows, permutations or shifts")
    # Reject malformed nested records before allocating storage for the cycle.
    for row, permutation, shift in zip(rows, permutations, shifts):
        integer(shift, "shift must be an integer")
        require(isinstance(row, list) and len(row) == order, "incorrect row length")
        require(isinstance(permutation, list) and len(permutation) == order, "incorrect permutation length")
        require(all(type(x) is int for x in row) and all(type(x) is int for x in permutation),
                "sites and gaps must be integers")
        require(all(0 <= site < width for site in row), "row sites must lie in the cycle")
        require(all(left < right for left, right in zip(row, row[1:])),
                "row sites must be strictly increasing")
        require(sorted(permutation) == list(range(1, order + 1)), "row gaps are not a permutation")

    occupied = [-1] * width
    for owner, (row, permutation, shift) in enumerate(zip(rows, permutations, shifts)):
        position = shift
        arrivals = []
        for gap in permutation:
            position = (position + gap) % width
            arrivals.append(position)
            require(occupied[position] == -1, "cyclic partial sums collide")
            occupied[position] = owner
        expected = sorted(arrivals)
        require(row == expected, "listed row differs from its cyclic partial sums")
        gaps = [right - left for left, right in zip(expected, expected[1:])]
        gaps.append(expected[0] + width - expected[-1])
        require(sorted(gaps) == list(range(1, order + 1)), "cyclic gaps, including wrap, are incorrect")
    require(all(owner >= 0 for owner in occupied), "the optimal cycle is not fully occupied")
    return {"status": "PASS", "height": height, "rows": height, "sites": width, "cyclic_gaps": height * order}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", help="JSON certificate filename, or - for standard input")
    args = parser.parse_args()
    try:
        raw = sys.stdin.read() if args.certificate == "-" else Path(args.certificate).read_text(encoding="utf-8")
        result = verify(json.loads(raw))
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
