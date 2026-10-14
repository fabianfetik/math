# Editable manuscript source

`paper.tex` is the complete editable production manuscript. It contains the
author metadata, typesetting definitions, all mathematical text, and both
bibliography entries. No private paths, external figures, private style files,
network resources, or research repository are required to compile it.

Use Python 3 and a TeX installation providing `pdflatex`, the standard LaTeX
packages `amsmath`, `amssymb`, `amsthm`, `geometry`, `hyperref`, `microtype`,
`longtable`, `booktabs`, `array`, `calc`, and Latin Modern fonts (`lmodern`).
The TeX Live collections `latex-base`, `latex-recommended`, and
`fonts-recommended`, with Latin Modern installed, provide this dependency set.

From an extracted package's root directory run:

```sh
python3 source/build.py --output-dir ../pinwheel-typeset
```

From this `source` directory the equivalent command is
`python3 build.py --output-dir ../../pinwheel-typeset`. The script runs three
TeX passes and writes `paper.pdf`, `paper.log`, and the ordinary auxiliary
files to the selected directory. Generated files stay outside the manifested
package. The default output is also a sibling of the manuscript package.
The script rejects unresolved references, unresolved
citations, missing glyphs, and unstable final labels. Reported overfull boxes
require visual layout review. Select an executable or output directory with
`--engine` and `--output-dir`.

Alternatively, an installed Tectonic engine with its TeX bundle available can
compile the same source:

```sh
python3 source/build.py --engine tectonic --output-dir ../pinwheel-typeset
```

For a direct TeX build without Python, copy `paper.tex` to a working directory
and run the following command there three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape paper.tex
```

`latexmk -pdf paper.tex` in that working directory is another option. The
release PDF was compiled with pdfTeX 1.40.25 (TeX Live 2023/Debian).

The main statements share one theorem counter; each appendix starts its own
statement counter. Equation numbers retain the manuscript's explicit tags.
Section, statement, equation and literature references use LaTeX labels and
citation keys, so changes can be checked by compiling the editable source.

The manuscript and this documentation are licensed under CC BY 4.0;
`build.py` is licensed under MIT. The package's [license notice](../LICENSE.md)
and [license texts](../licenses/) identify the applicable terms.
