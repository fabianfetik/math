#!/usr/bin/env python3
"""Validate the complete file inventory and hashes before building."""

import hashlib
import json
from pathlib import Path, PurePosixPath


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def main():
    root = Path(__file__).resolve().parent
    manifest_path = root / "MANIFEST.json"
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise ValueError("manifest must be a regular file")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"),
                          object_pairs_hook=unique_object)
    expected = manifest["files"]
    for name, record in expected.items():
        item = PurePosixPath(name)
        if item.is_absolute() or not item.parts or any(p in {"", ".", ".."} for p in item.parts):
            raise ValueError(f"unsafe path: {name}")
        path = root.joinpath(*item.parts)
        if any(parent.is_symlink() for parent in (path, *path.parents) if parent != root.parent):
            raise ValueError(f"symlink in path: {name}")
        if not path.is_file():
            raise ValueError(f"missing or non-regular file: {name}")
        data = path.read_bytes()
        if len(data) != record["bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
            raise ValueError(f"content mismatch: {name}")
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file() or p.is_symlink()}
    if actual != set(expected) | {"MANIFEST.json"}:
        raise ValueError(f"unexpected or missing files: {actual ^ (set(expected) | {'MANIFEST.json'})}")
    print(f"PASS: {len(expected)} files and complete source inventory match MANIFEST.json")


if __name__ == "__main__":
    main()
