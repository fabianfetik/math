#!/usr/bin/env python3
"""Construct optimal corrals using the even and one-swap odd formulas."""
# Copyright (c) 2026 Fabian Fetik
# SPDX-License-Identifier: MIT
import argparse
from itertools import accumulate
import json


SMALL_ODD_ROWS = {
    1: ((0,),),
    3: ((0, 1, 3, 6, 10), (4, 8, 9, 11, 14), (2, 5, 7, 12, 13)),
}


def positive_height(height):
    if type(height) is not int or height < 1:
        raise ValueError("height must be a positive integer")


def even_rows(height):
    half = height // 2
    order = 2 * height - 1
    period = 2 * order
    width = height * order
    starts = list(range(height - 1, 0, -2)) + list(range(height - 2, 0, -2))
    gaps = [x for start in starts for x in (start, 2 * height - start)] + [height]
    prefixes = [0] + list(accumulate(gaps))[:-1]
    reflection = half - 1 if half % 2 == 0 else 5 * half - 2
    direct = [sorted((x + j * period) % width for x in prefixes) for j in range(half)]
    reflected = [
        sorted((reflection - x + j * period) % width for x in prefixes)
        for j in range(half)
    ]
    return direct + reflected


def odd_core(height):
    parameter = (height - 3) // 2
    length = 2 * height - 3
    gaps = [length + 2, length - 1]
    for j in range(parameter):
        gaps.extend((length - 3 - 4 * j, 4 * j + 5))
    gaps.append(length + 1)
    for j in range(parameter - 1):
        gaps.extend((4 * j + 2, length - 4 - 4 * j))
    gaps.extend((length - 5, 1))
    prefixes = [0] + list(accumulate(gaps))[:-1]
    assignment = [(owner + parameter + 2) % height for owner in range(height)]
    assignment[height - 2], assignment[height - 1] = assignment[height - 1], assignment[height - 2]
    return prefixes, assignment


def odd_rows(height):
    if height in SMALL_ODD_ROWS:
        return [list(row) for row in SMALL_ODD_ROWS[height]]
    length = 2 * height - 3
    core_width = height * length
    translation = height - 3
    prefixes, assignment = odd_core(height)
    result = []
    for owner, partner in enumerate(assignment):
        core = sorted((x + translation + length * owner) % core_width for x in prefixes)
        pair = sorted((2 * partner, (2 * partner + 3) % (2 * height)))
        result.append(core + [core_width + x for x in pair])
    return result


def construct(height):
    """Return rows, permutations and shifts at order 2*height-1."""
    positive_height(height)
    order = 2 * height - 1
    width = height * order
    rows = odd_rows(height) if height % 2 else even_rows(height)
    permutations = [
        [right - left for left, right in zip(row, row[1:])]
        + [row[0] + width - row[-1]]
        for row in rows
    ]
    return {
        "height": height,
        "order": order,
        "width": width,
        "rows": rows,
        "permutations": permutations,
        "shifts": [row[0] for row in rows],
    }


def owner_decoder(height):
    """Return a site-to-owner map for the same row order as construct."""
    positive_height(height)
    width = height * (2 * height - 1)
    if height % 2 and height >= 5:
        length = 2 * height - 3
        core_width = height * length
        translation = height - 3
        prefixes, assignment = odd_core(height)
        residue_prefix = {x % length: x for x in prefixes}
        inverse = {partner: owner for owner, partner in enumerate(assignment)}

        def decode(site):
            if type(site) is not int or not 0 <= site < width:
                raise ValueError("site must be an integer in the corral cycle")
            if site < core_width:
                prefix = residue_prefix[(site - translation) % length]
                return ((site - translation - prefix) % core_width) // length
            local = site - core_width
            partner = ((local - 3) // 2) % height if local % 2 else local // 2
            return inverse[partner]
    else:
        rows = odd_rows(height) if height % 2 else even_rows(height)
        inverse = [-1] * width
        for owner, row in enumerate(rows):
            for site in row:
                inverse[site] = owner

        def decode(site):
            if type(site) is not int or not 0 <= site < width:
                raise ValueError("site must be an integer in the corral cycle")
            return inverse[site]
    return decode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("height", type=int)
    args = parser.parse_args()
    try:
        result = construct(args.height)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
