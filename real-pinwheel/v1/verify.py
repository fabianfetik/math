#!/usr/bin/env python3
"""Verify the finite proof data in this stand-alone publication package.

Run from any working directory: python3 /path/to/package/verify.py
Python assertions must be enabled. A C++17 compiler is needed for the
one-head terminal certificates. The optional Lean build is described in
proof-artifacts.md and is not part of this finite-data replay.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory
from zipfile import ZipFile


ROOT = Path(__file__).resolve().parent


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    sha = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            sha.update(block)
    return sha.hexdigest()


def check_manifest() -> int:
    manifest = json.loads((ROOT / "manifest.json").read_text())
    need(manifest.get("schema") == "real-pinwheel-5-6-proof-package-1",
         "unexpected package manifest")
    files = manifest.get("files")
    need(isinstance(files, dict) and bool(files), "manifest files must be a nonempty object")
    need(not any(p.is_symlink() for p in ROOT.rglob("*")), "symbolic links are not package files")
    actual_files = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
                    if p.is_file() and p != ROOT / "manifest.json"}
    need(set(files) == actual_files, "manifest file set differs from package")
    for name, expected in files.items():
        relative = Path(name)
        need(not relative.is_absolute() and ".." not in relative.parts,
             f"unsafe manifest path: {name}")
        need(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected) is not None,
             f"malformed SHA-256 digest: {name}")
        need(digest(ROOT / relative) == expected, f"SHA-256 mismatch: {name}")
    return len(files)


def run(args: list[str], cwd: Path = ROOT) -> str:
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONHASHSEED"] = "0"
    completed = subprocess.run(args, cwd=cwd, env=env,
                               text=True, capture_output=True, check=False)
    need(completed.returncode == 0,
         f"command failed: {' '.join(args)}\n"
         f"stdout:\n{completed.stdout[-4000:]}\n"
         f"stderr:\n{completed.stderr[-4000:]}")
    return completed.stdout


def json_run(args: list[str]) -> dict:
    return json.loads(run(args))


def foundations() -> dict:
    four = json_run([sys.executable, "-I", str(ROOT / "software/verify_four_role.py")])
    need(four.get("result") == "VERIFIED: Delta4 is contained in K_star"
         and four.get("nodes") == 735 and four.get("regions") == 93,
         "four-role real cover failed")
    five = json_run([sys.executable, "-I", str(ROOT / "software/verify_five_role.py"),
                     str(ROOT / "data/five-role")])
    need(five.get("verified") is True and five.get("nodes") == 5393
         and five.get("words") == 84 and five.get("streams") == 13,
         "five-role real cover failed")
    marked = json_run([sys.executable, "-I", str(ROOT / "software/verify_marked_core.py"),
                       str(ROOT / "data/marked-core.zip")])
    need(marked.get("status") == "pass" and marked.get("target") == "3403/4290",
         "marked-core real cover failed")
    return {"four_role_nodes": four["nodes"], "four_role_regions": four["regions"],
            "five_role_nodes": five["nodes"],
            "marked_core_roots": len(marked["roots"])}


def one_head(scratch: Path) -> dict:
    path = ROOT / "data/one-head-templates.zip"
    with ZipFile(path) as archive:
        for member in ("words.tsv", "faces.tsv", "routes.tsv"):
            (scratch / member).write_bytes(archive.read(member))
    with ZipFile(ROOT / "data/multiple-head-foundation.zip") as archive:
        (scratch / "residual.csv").write_bytes(archive.read(
            "outputs/two_group_residual_signatures.csv"))
    binary = scratch / "verify_one_head"
    run(["g++", "-O2", "-std=c++17", "-Wall", "-Wextra",
         "-fsanitize=undefined", "-fno-sanitize-recover=all",
         str(ROOT / "software/verify_one_head.cpp"), "-o", str(binary)], scratch)
    result = json.loads(run([str(binary), str(scratch / "words.tsv"),
                             str(scratch / "faces.tsv"), str(scratch / "routes.tsv"),
                             str(scratch / "residual.csv")], scratch))
    need(result.get("outcome") == "VERIFIED"
         and result.get("r063_routes") == 2117841
         and result.get("missing_or_extra_signatures") == 0,
         "one-head terminal or residual inventory failed")
    return {"base_words": result["r063_words"], "templates": result["r063_templates"],
            "routes": result["r063_routes"], "signature_classification": "closures and true residuals"}


def lower(scratch: Path) -> dict:
    one = one_head(scratch)
    output = run([sys.executable, "-I",
                  str(ROOT / "software/verify_multiple_head_foundation.py")])
    foundation = json.loads(output.splitlines()[-1])
    need(foundation.get("outcome") == "VERIFIED" and
         {row["heads"]: row["covered_signatures"]
          for row in foundation.get("coverage", [])} ==
         {7: 780, 6: 4757, 2: 11}, "multiple-head foundation failed")

    exceptional = json_run([sys.executable, "-I",
                            str(ROOT / "software/verify_exceptional_six_head.py")])
    need(exceptional.get("status") == "PASS"
         and exceptional.get("r154b", {}).get("regions") == 28
         and exceptional.get("r154b", {}).get("nodes") == 11014
         and exceptional.get("t093_11_18", {}).get("regions") == 1,
         "exceptional six-head covers failed")
    terminal = json_run([sys.executable, "-I",
                         str(ROOT / "software/verify_multiple_head_terminal.py"),
                         "--archive", str(ROOT / "data/multiple-head-terminal.zip")])
    need(terminal.get("status") == "PASS" and
         terminal.get("signatures", {}).get("pw7_relevant") == 18458 and
         terminal.get("counts", {}).get("regions") == 18460 and
         terminal.get("counts", {}).get("nodes") == 936816,
         "multiple-head terminal covers failed")
    selected = selection()
    return {"one_head": one, "foundation": "PASS",
            "exceptional": "PASS", "terminal_signatures": terminal["signatures"]["pw7_relevant"],
            "terminal_nodes": terminal["counts"]["nodes"],
            "selected_domain": selected}


def selection() -> dict:
    result = json_run([sys.executable, "-I", str(ROOT / "software/verify_small_minimum.py")])
    need(result.get("status") == "PASS" and result.get("selected_signatures") == 62756
         and result.get("missing_selected_signatures") == 0
         and result.get("extra_selected_signatures") == 0,
         "selected Appendix B domain is not included in accepted inventories")
    return result


def upper() -> dict:
    result = json_run([sys.executable, "-I",
                       str(ROOT / "software/verify_eleventh_band.py"),
                       "--archive", str(ROOT / "data/eleventh-band.zip")])
    need(result.get("result") == "PASS" and result.get("total_nodes") == 60345,
         "eleventh-band real cover failed")
    return {"cover_nodes": result["total_nodes"]}


def middle(scratch: Path) -> dict:
    output_file = scratch / "middle-primary-result.json"
    run([sys.executable, "-I", str(ROOT / "software/verify_middle_cover_primary.py"),
         str(ROOT / "data/middle-cover.json.gz"), "--require-complete",
         "--output", str(output_file)])
    primary = json.loads(output_file.read_text())
    second = json_run([sys.executable, "-I",
                       str(ROOT / "software/verify_middle_cover.py"),
                       str(ROOT / "data/middle-cover.json.gz")])
    need(primary.get("complete") is True and second.get("frontier") == 0
         and (primary.get("sources"), primary.get("nodes")) == (4707, 55175)
         and (second.get("sources"), second.get("nodes")) == (4707, 55175),
         "middle real cover failed")
    return {"sources": 4707, "nodes": 55175, "frontier": 0}


def lean_source() -> dict:
    with ZipFile(ROOT / "lean-source.zip") as archive:
        info = json.loads(archive.read("SOURCE-MANIFEST.json"))
        file_names = archive.namelist()
        names = set(file_names)
        need(len(names) == len(file_names), "duplicate Lean archive member")
        need(info.get("schema") == "pinwheel-lean-source-1", "unexpected Lean source manifest")
        need(info.get("local_namespaces") == ["Pinwheel", "OccurrenceSpans"],
             "unexpected local Lean module namespaces")
        need(info.get("entries") == ["Pinwheel/FiveTask.lean", "Pinwheel/WeakSevenBand.lean"],
             "missing formalized subresult entry point")
        need(names == set(info["files"]) | {"SOURCE-MANIFEST.json"},
             "Lean source file set differs from manifest")
        for name, expected in info["files"].items():
            relative = Path(name)
            need(not relative.is_absolute() and ".." not in relative.parts,
                 f"unsafe Lean source path: {name}")
            need(hashlib.sha256(archive.read(name)).hexdigest() == expected,
                 f"Lean source hash mismatch: {name}")
        toolchain = archive.read("lean-toolchain").decode().strip()
        lake = json.loads(archive.read("lake-manifest.json"))
        mathlib = [row for row in lake["packages"] if row["name"] == "mathlib"]
        need(toolchain == info["lean_toolchain"] == "leanprover/lean4:v4.33.1"
             and len(mathlib) == 1 and mathlib[0]["rev"] == info["mathlib_revision"]
             == "0df444a360eaa60ab8c11dca51a86af692955474", "Lean dependency pin mismatch")
        need(re.search(r'rev\s*=\s*"' + re.escape(info["mathlib_revision"]) + '"',
                       archive.read("lakefile.toml").decode()) is not None,
             "lakefile does not request the pinned mathlib revision")
        pending, visited = list(info["entries"]), set()
        while pending:
            name = pending.pop()
            if name in visited:
                continue
            need(name in names, f"missing transitive Lean source: {name}")
            visited.add(name)
            for line in re.findall(r"(?m)^\s*import\s+([^\n]+)", archive.read(name).decode()):
                for module in line.split("--", 1)[0].split():
                    if module.split(".", 1)[0] in info["local_namespaces"]:
                        dependency = module.replace(".", "/") + ".lean"
                        need(dependency in names, f"missing local Lean import: {dependency}")
                        pending.append(dependency)
        need(len(visited) == info["local_module_count"] == 289,
             "Lean local source closure has the wrong module count")
        need({name for name in names if name.endswith(".lean")} == visited | {"PublicationAudit.lean"},
             "unused or missing Lean module in source archive")
    return {"source_files": len(info["files"]),
            "transitive_local_modules": len(visited),
            "lean_toolchain": info["lean_toolchain"],
            "mathlib_revision": info["mathlib_revision"],
            "scope": "source hashes, import closure and pins; no Lean kernel execution"}


def main() -> None:
    need(__debug__, "run without Python -O")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", choices=("all", "foundations", "lower", "upper",
                                            "middle", "selection", "lean-source"), default="all")
    parser.add_argument("--output", type=Path,
                        help="write the JSON report to a file outside the package")
    args = parser.parse_args()
    count = check_manifest()
    result = {"status": "PASS", "manifest_files": count, "groups": {}}
    with TemporaryDirectory(prefix="pinwheel-proof-") as temporary:
        scratch = Path(temporary)
        if args.group in ("all", "foundations"):
            result["groups"]["foundations"] = foundations()
        if args.group in ("all", "lower"):
            result["groups"]["lower"] = lower(scratch)
        if args.group == "selection":
            result["groups"]["selected_domain_inclusion"] = selection()
        if args.group in ("all", "upper"):
            result["groups"]["upper"] = upper()
        if args.group in ("all", "middle"):
            result["groups"]["middle"] = middle(scratch)
        if args.group in ("all", "lean-source"):
            result["groups"]["lean_source_integrity"] = lean_source()
    report = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        need(not args.output.resolve().is_relative_to(ROOT),
             "write check reports outside the manifested package")
        args.output.write_text(report)
    print(report, end="")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as exc:
        raise SystemExit(f"Verification failed: {exc}") from exc
