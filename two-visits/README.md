# Sharp density thresholds for finite two-visit scheduling

**Fabian Fetik · Preprint · v1 · 1 October 2026**

[PDF](two-visits-v1.pdf) · [Material](v1/) ·
[Zenodo](https://doi.org/10.5281/zenodo.23089289)

Each task must occur exactly twice, with a positive integer deadline bounding
its first visit and the gap between visits. Every instance of density at most
one is feasible. For each task count $n\geq 2$, the paper gives the
sharp threshold $1+1/[n(n-1)]$ and identifies $(n-1,n,\ldots,n)$ as the unique
infeasible deadline multiset at that threshold. The proofs are analytic and
give a constructive scheduling algorithm.

| Material | Contents |
| --- | --- |
| [Manuscript source](v1/source/) | Markdown, TeX, figure and build instructions |
| [Algorithm and checker](v1/code/) | Constructor and independent output-certificate checker |
| [Exact checks](v1/checks/) | Bounded scheduling and symbolic checks |
| [Original ZIP](two-visits-v1.zip) | Complete archived v1 package |

The [unpacked v1 package](v1/) matches the Zenodo ZIP. Its
[README](v1/README.md) gives commands for running the algorithm and checks and
rebuilding the paper.

The article, documentation, example data and figures are licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); supplied Python
software is licensed under MIT. The ZIP contains the precise license allocation
and full texts.
