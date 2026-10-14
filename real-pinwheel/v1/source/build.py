#!/usr/bin/env python3
"""Compile the standalone paper.tex with a local TeX installation."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", default="pdflatex", help="pdflatex-compatible executable, or tectonic")
    parser.add_argument("--output-dir", type=Path,
                        help="build directory (default: sibling of the manuscript package)")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    default_output = here.parent.parent / (here.parent.name + "-typeset")
    output = (args.output_dir or default_output).resolve()
    executable = shutil.which(args.engine)
    if executable is None:
        raise SystemExit(f"TeX executable unavailable: {args.engine}. Install the documented TeX dependencies or supply --engine.")
    output.mkdir(parents=True, exist_ok=True)
    if "tectonic" in Path(executable).name.lower():
        command = [executable, "--keep-logs", "--keep-intermediates", "--outdir", str(output), str(here / "paper.tex")]
        result = subprocess.run(command, cwd=here, capture_output=True, text=True)
        (output / "compiler-stdout.txt").write_text(result.stdout+result.stderr, encoding="utf-8")
        if result.returncode:
            raise SystemExit(result.stdout+result.stderr)
    else:
        command = [executable, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
                   "-no-shell-escape", f"-output-directory={output}", "paper.tex"]
        for number in range(1, 4):
            result = subprocess.run(command, cwd=here, capture_output=True, text=True)
            (output / f"compiler-pass-{number}.txt").write_text(result.stdout+result.stderr, encoding="utf-8")
            if result.returncode:
                raise SystemExit(result.stdout+result.stderr)
    pdf, log = output / "paper.pdf", output / "paper.log"
    if not pdf.is_file() or pdf.stat().st_size == 0:
        raise SystemExit("TeX did not produce paper.pdf")
    if log.is_file():
        text = log.read_text(encoding="utf-8", errors="replace")
        failures = ("There were undefined references", "There were undefined citations",
                    "Label(s) may have changed", "multiply defined", "Missing character:",
                    "destination with the same identifier")
        for failure in failures:
            if failure in text:
                raise SystemExit(f"Final TeX log requires correction: {failure}")
        for line in text.splitlines():
            if "Overfull" in line:
                print(f"LAYOUT REVIEW: {line}")
    print(f"Compiled {pdf}")

if __name__ == "__main__":
    main()
