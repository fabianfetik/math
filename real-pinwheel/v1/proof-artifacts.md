# Supplementary proof data

This supplement accompanies *Real-period pinwheel scheduling at density
5/6* by Fabian Fetik. The certificate acceptance rules and their
mathematical soundness are in Appendices A–D of the manuscript. Its
complete editable source is `source/paper.tex`.

Extract the supplement into a new directory and run:

```sh
python3 verify.py
```

Python 3.10 or later and GCC's `g++` with C++17 support are required. The
Python programs use only the standard library. Run Python with assertions
enabled. All inputs are packaged; the finite replay needs no network or
research-repository files. It checks file hashes first and performs the
mathematical checks using exact integer and rational arithmetic.
Allow roughly 3 GiB of RAM and several minutes for the complete replay.

Some certificate format tags, report keys and identifiers in the pinned
Lean sources retain historical provenance labels. They are preserved to
match the checked proof objects and source snapshots; they do not refer
to additional files that a reader needs to obtain. Historical paths in
discovery metadata are not used by the verification programs.

To save a report outside the package, use:

```sh
python3 verify.py --output /tmp/pinwheel-verification.json
```

The report contains the complete finite-check results and the exact
Appendix B selection. `--group foundations`, `--group lower`,
`--group upper`, and `--group middle` replay individual certificate groups.
`--group selection` checks the selection's inclusion and elementary source
interfaces; the larger inventories still need their acceptance checks.

| Mathematical claim | Proof data | Acceptance program |
| --- | --- | --- |
| Four-role real cover, Theorem A.5 | `data/four-role/catalogue.json`, `coverage-proof.json`, `word-certificates.json` in the same directory | `software/verify_four_role.py` |
| Five-role real cover, Theorem A.5 | `data/five-role/outputs/final-catalogue.json`, `coverage-certificate.json` in the same directory | `software/verify_five_role.py` |
| Marked-core source, Theorem A.6 | `data/marked-core.zip` | `software/verify_marked_core.py` |
| One-head sources and full residual classification, B.3 | `data/one-head-templates.zip`, the residual-signature CSV in `data/multiple-head-foundation.zip` | `software/verify_one_head.cpp` |
| Preliminary multiple-head cover graphs, B.3 | `data/multiple-head-foundation.zip` | `software/verify_multiple_head_foundation.py` |
| Multiple-head terminal cover graphs, B.3 | `data/multiple-head-terminal.zip` | `software/verify_multiple_head_terminal.py` |
| Exceptional six-head graphs and supporting two-tail source, B.3 | `data/exceptional-six-head.zip`, `data/two-tail-source/` | `software/verify_exceptional_six_head.py` |
| Exact selected terminal domain, B.3 | `data/small-minimum-domain.json` and the checked inventories above | `software/verify_small_minimum.py` |
| Closed eleventh-to-tenth strip, C.1 | `data/eleventh-band.zip` | `software/verify_eleventh_band.py` |
| Middle paired band, D | `data/middle-cover.json.gz` | `software/verify_middle_cover_primary.py`, `software/verify_middle_cover.py` |

The four-role catalogue is mathematical JSON: 63 four-label words, six
three-role words, and three direct load constructions. Its 93 regions and
735-node cover tree are checked with the original open and closed faces.
The five-role replay checks 13 stream constructions, 84 periodic words,
and the 5,393-node real-domain refutation.

The lower-band inventories are larger than the subset needed by the
paper. Their acceptance programs check all 2,117,841 one-head routes,
the preliminary cover inventories, 18,460 multiple-head terminal graphs
with 936,816 nodes, and 28 exceptional six-head graphs plus one supporting
two-tail graph. The residual checker enumerates the whole bounded
signature inventory and checks both its two-parent closures and its
1,164,266 remaining signatures. All physical tail tests use the actual
deadline `c`; only the head-sum guard uses the discounted `1/(c+1)`.

The selection program independently enumerates all **62,756** signatures
in (B.7). Its report gives their exact set hash, the counts for each head
count, and zero missing or extra signatures. The selected multi-head
terminal subset has 7,524 graphs and 339,581 nodes. Its twelve six-head
cases use eight preliminary graphs (1,587 nodes), three exceptional graphs
(1,371 nodes), and one marked-source interface. The program checks the
five-word analytic selector for the eleven two-head singleton tails,
including its open cap endpoints, and rederives the true residual test
for every selected signature with two through six heads. The strict
head-sum guard, the closed head lower face `1/11`, equal-head faces, and
the exceptional strict narrow-band condition are retained.

The middle proof object has 4,707 sources, 55,175 nodes and an empty
frontier. Two implementations check its whole-region acceptance rules.
The finite replay establishes these certificate predicates. The
unbounded reductions, reconstruction, and the implication from the
predicates to scheduling existence are proved in the manuscript.

The upper source in C.2 uses a Lean theorem. `lean-source.zip` contains
all 289 transitive local modules needed by that theorem and the five-role
theorem, three dependency configuration files, and an axiom-audit entry
point. It pins Lean `leanprover/lean4:v4.33.1` and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

To check these formalized subresults, make Elan's `lake` available and run:

```sh
unzip lean-source.zip -d ../pinwheel-lean-source
cd ../pinwheel-lean-source
lake exe cache get
lake build Pinwheel.FiveTask Pinwheel.WeakSevenBand
lake env lean PublicationAudit.lean
```

The dependency download needs network access on a fresh machine. The
audit prints the axioms of
`RealPinwheel.five_task_real_period_pinwheel` and
`RealPinwheel.weakSeven_tenth_band`; their expected dependencies are
`propext`, `Classical.choice`, and `Quot.sound`.
`python3 verify.py --group lean-source` checks the source hashes, actual
import closure and dependency pins. It does not execute the Lean kernel.
The two declarations formalize their named subresults; the main theorem
combines written arguments, finite certificates, and the upper Lean source.

The editable typesetting source and its build instructions are in
`source/`. Rebuild outside the manifested package:

```sh
python3 source/build.py --output-dir ../pinwheel-typeset
```

The supplied paper.pdf was compiled from source/paper.tex using pdfTeX 1.40.25 (TeX Live 2023/Debian), three pdflatex passes via source/build.py. Its generation method and status are recorded in manifest.json.
