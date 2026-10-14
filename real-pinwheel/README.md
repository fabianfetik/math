# Real-period pinwheel scheduling at density 5/6

**Fabian Fetik · Preprint · v1 · 28 September 2026**

[PDF](real-pinwheel-5-6-v1.pdf) · [Material](v1/) ·
[Zenodo](https://doi.org/10.5281/zenodo.23018098)

Tasks must recur indefinitely under timing constraints given by real-valued
periods. Schedules exist for every finite task family whose reciprocal periods
sum to at most 5/6.

| Material | Contents |
| --- | --- |
| [Manuscript source](v1/source/) | TeX and build instructions |
| [Verification programs](v1/software/) | Python and C++ acceptance checks |
| [Proof data and guide](v1/proof-artifacts.md) | Certificate data, acceptance rules and reproduction instructions |
| [Lean sources](lean-v1/) | Pinned sources for the five-role and upper-band subresults |
| [Original ZIP](real-pinwheel-5-6-v1.zip) | Complete archived v1 package |

The [unpacked v1 package](v1/) matches the Zenodo ZIP. Follow its
[README](v1/README.md) and [guide](v1/proof-artifacts.md) to run the checks.
The Lean sources are unpacked separately from its `lean-source.zip` and retain
the archived dependency pins. They formalize the named subresults; the main
theorem also uses written arguments and finite certificates.

The article, documentation and finite proof data are licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); supplied software and
local Lean sources are licensed under MIT. The ZIP contains the precise license
allocation and full texts.
