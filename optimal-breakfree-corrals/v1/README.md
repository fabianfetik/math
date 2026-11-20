# Optimal Breakfree Corrals

The [article PDF](paper/reader.pdf) and
[editable article](paper/manuscript.md) use the eight figures in
[paper/figures](paper/figures/README.md). The [formal scope](paper/FORMAL-SCOPE.md)
and [statement map](paper/CLAIM-MAP.md) describe the Lean evidence and its premises.
The [license notice](LICENSE.md) states the terms for the supplied files.

Check the inventory after extraction, before building.

    python3 -B verify_manifest.py

The article can be regenerated with Pandoc and typeset with pdfLaTeX.
The TeX source uses the supplied vector exports and the font notices in
[paper/source](paper/source/THIRD-PARTY-NOTICES.md).

    cd paper
    python3 -B typeset.py
    cd source
    latexmk -pdf -halt-on-error -interaction=nonstopmode -outdir=build paper.tex

Run the Python constructor and checker as described in the
[supplement guide](paper/supplement/README.md).
From the package root, use the pinned toolchain to build and audit Lean.

    cd lean
    lake build
    lake env lean Audit.lean

After building Lean, run the [height-seven certificate check](paper/supplement/formal/README.md).
From the package root, use the following command.

    cd paper
    sh supplement/formal/check.sh ../lean supplement/examples/height-seven.json

The manifest records the public version and hashes all supplied files.
The Lean toolchain and Lake dependency manifest pin the build.
