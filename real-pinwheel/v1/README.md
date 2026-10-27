# Real-period pinwheel scheduling at density 5/6

**Author:** Fabian Fetik

This package contains the complete editable manuscript in
`source/paper.tex`, finite proof data, verification
programs, and pinned Lean source for the five-role and upper-band subresults.

After extraction into a new directory, run:

```sh
python3 verify.py
```

The [supplementary guide](proof-artifacts.md) explains the acceptance rules,
the exact 62,756-signature selection, requirements, and the separate Lean
kernel build. Every finite-check input is included. The typesetting build
instructions are in `source/README.md`.

The compiled manuscript is [paper.pdf](paper.pdf); its editable typesetting source and build instructions are included.

The manuscript proves the main theorem using written arguments, finite
certificates and the formalized subresults identified in the supplementary
guide. The Lean archive does not formalize the entire main theorem.

The manuscript, documentation and finite proof data are licensed under
CC BY 4.0. The verification programs, typesetting helper and local Lean
sources are licensed under MIT. See [LICENSE.md](LICENSE.md) for the exact
scope and the included license texts.
