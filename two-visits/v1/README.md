# Sharp density thresholds for finite two-visit scheduling

**Author:** Fabian Fetik

This package contains a self-contained analytic article, a constructive
algorithm, an independent output-certificate checker, and selected exact checks.
The article concerns finite labelled **positive integer deadlines**: each task
occurs twice in a word of length `2n`, its first visit is at most its deadline,
and the gap to its second visit is at most its deadline.

Theorem A proves feasibility at density at most one. Theorem B identifies
`1 + 1/[n(n-1)]` as the minimum infeasible density for each fixed `n>=2`;
among inputs at or below that density, the unique infeasible deadline
multiset is `(n-1,n,...,n)`. The proofs are analytic. The supplied software
checks constructed words and selected exact identities.

## Contents

- `paper.pdf`: the typeset article.
- `source/manuscript.md` and `source/paper.tex`: editable Markdown and portable
  LaTeX. Title, author and references in the TeX are generated from Markdown.
- `source/figures/`: vector PDF/SVG, exact example fixture, and figure generator.
- `code/construct.py` and `code/verify.py`: constructor and independent checker.
- `checks/check_bundle.py`: bounded scheduling, certificate, example and source
  checks using the Python standard library.
- `checks/check_algebra.py`: selected exact symbolic identities and sign checks.
- `checks/optional-requirements.txt`: pinned optional checking/figure dependencies.
- `validation.json`: the tool versions and results of the reproducible checks.
- `LICENSE.md` and `licenses/`: the material-by-material license notice and full texts.
- `MANIFEST.sha256`: hashes of the supplied files, excluding the manifest itself.

## Run the algorithm and checker

Python 3.10 or newer is sufficient; neither program needs third-party packages.
Run these commands from the extracted package root:

```sh
python3 code/construct.py 6 6 9 9 9 9 9 9 > example.json
python3 code/verify.py example.json
python3 code/construct.py 7 8 8 8 8 8 8 8 > critical.json
python3 code/verify.py critical.json
python3 checks/check_bundle.py
```

Input labels in JSON are zero-based; positions in the article are one-based.
`--input deadlines.json` accepts a JSON array, and `--trace` adds cluster data.
The checker also accepts `-` to read a certificate from standard input.

A positive certificate is checked directly for length, label multiplicity,
first-visit deadlines, and consecutive-visit gaps. The only accepted negative
certificate identifies the critical family and its sum-of-gaps obstruction.
The constructor reports an unsupported input when the density promise is
exceeded. The empty and one-task inputs are supported.

## Bounded scheduling checks

The checker examines 2,398 sorted inputs with `2<=n<=5` and deadlines in
`[1,2n]`. Exactly 873 satisfy the promise, including four critical instances;
the other 869 are constructed in both original and reversed label orders.
For all 396 inputs with `2<=n<=4` in these boxes, a separately written exact
recursive solver decides feasibility from the first-visit deadlines and
successive-visit gaps. It stops with an error if it exceeds its 20,000-state
cap per input. The observed maximum was 267 states.
The word language for the largest oracle input has at most `8!/(2!)^4=2,520`
words. Fifteen structured examples include all four repair patterns, a large
charged prefix, density equality, append cascades, and very large deadlines.
The example fixture is compared with the constructor's word and calendar trace.
Forged certificates and a feasible input outside the promise are also checked.

For the optional symbolic check, use an environment containing SymPy 1.14.0:

```sh
python3 checks/check_algebra.py
```

It verifies 31 specified identities or polynomial coefficient signs, including
the four bad-capacity differences in equation (9.19).

## Rebuild the PDF

Compile the supplied TeX and vector figure with pdfLaTeX:

```sh
cd source
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The two runs resolve citations and equation references. They produce a PDF in
`source/`; the package-root article is `paper.pdf`.
The tested tools were pdfTeX 1.40.25 / TeX Live 2023 and the standard LaTeX
packages named in the preamble. Fresh rebuilds can differ in PDF metadata;
the archived reading copy is identified by the manifest.

To regenerate TeX after editing Markdown, run `python3 typeset.py` from
`source/` with Pandoc available (tested: 3.1.3). To redraw Figure 1, run
`python3 figures/generate_figure.py` there with Matplotlib 3.11.1. The generator
uses its bundled BaKoMa Computer Modern Sans font (`cmss10`) and exports SVG
lettering as vector outlines. Regenerating the figure with this pinned version
requires Python 3.11 or newer. The provided
figure is already sufficient for compiling the article. Edit the title, author
and reference entries in `manuscript.md`; `typeset.py` reads them from that
single source, including citation labels and location notes.

## Licenses

The article, documentation, example data and figures are licensed under
CC BY 4.0. All supplied Python software, including the constructor, checker,
checks, figure generator and typesetting helper, is licensed under MIT.
The exact allocation and full license texts are in [LICENSE.md](LICENSE.md).

## Version

Version `v1`, 1 October 2026.
