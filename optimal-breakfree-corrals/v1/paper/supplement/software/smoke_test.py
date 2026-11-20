#!/usr/bin/env python3
"""Run finite constructor, decoder and checker controls."""
import json
from pathlib import Path

import construct
import verify


def main():
    heights = list(range(1, 64)) + [100, 101, 201]
    sites = 0
    for height in heights:
        certificate = construct.construct(height)
        result = verify.verify(certificate)
        decode = construct.owner_decoder(height)
        for owner, row in enumerate(certificate["rows"]):
            for site in row:
                if decode(site) != owner:
                    raise AssertionError((height, owner, site))
        sites += result["sites"]
    example = Path(__file__).resolve().parents[1] / "examples/height-seven.json"
    if construct.construct(7) != json.loads(example.read_text(encoding="utf-8")):
        raise AssertionError("height-seven example differs")
    corrupt = construct.construct(7)
    corrupt["permutations"][0][0] = corrupt["permutations"][0][1]
    rejects = [corrupt]
    corrupt = construct.construct(7)
    corrupt["rows"][0][0] = corrupt["rows"][1][0]
    rejects.append(corrupt)
    for certificate in rejects:
        try:
            verify.verify(certificate)
        except ValueError:
            continue
        raise AssertionError("checker accepted an intentionally damaged certificate")
    print(f"PASS: {len(heights)} heights, {sites} sites, example identical, "
          f"{len(rejects)} damaged certificates rejected")


if __name__ == "__main__":
    main()
