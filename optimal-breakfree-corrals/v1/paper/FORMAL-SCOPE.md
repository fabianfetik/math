# Scope of the accompanying Lean development

The Lean development checks mathematical propositions stated in its own
formal language. The table gives the principal matches for this article;
[CLAIM-MAP.md](CLAIM-MAP.md) covers the named lemmas and proof interfaces
in more detail. The exact theorem types, including explicit hypotheses,
should be read alongside this guide. The checked formal proof may use a
different construction or proof from the one printed here.

The illustrations show finite examples and schematics. Their checks cover
the displayed data and the corresponding SVG elements. The Lean project
addresses the mathematical claims mapped below.

| Article statement | Selected formal conclusion | Scope |
| --- | --- | --- |
| Theorem 1 and Corollary 2 | `CorralFormalization.optimalCorral_exists`; `CorralFormalization.originalCorral_iff_order_bound` | Every positive height and the positive height/order criterion. The general odd existence theorem uses an earlier witness; the printed one-swap construction is also verified separately. Lean proves the larger-order extension separately, whereas the written corollary cites BDGM26. |
| Height-seven certificate | `HeightSevenCertificate.supplied_checked` | The [supplementary check](supplement/formal/README.md) proves the header and dimensions, equality of the seven increasing row lists with the one-swap rows, the gap permutations, and the arrivals reconstructed from the stored shifts. A Python helper translates the supplied JSON values into Lean literals. |
| Theorem 3 | `CorralFormalization.EvenSwitches.evenSwitchFamily_odd_k`; `CorralFormalization.PhysicalCensus.evenSwitchFamily_real_log_lower` | The explicit family, its exact asymmetric physical orbit count and its lower bound on the full census. The exported type asserts that such a family exists; the proof uses the concrete construction, which the type does not name. |
| Theorems 7 and 8 | `CorralFormalization.Results.PrimeHeight.every_odd_prime_optimal_originalWitness_asymmetric`; `CorralFormalization.Results.PhysicalPartitionUpper.sharp_global_census_bounds` | Odd-prime asymmetry and the three stated global physical-counting bounds. |
| Theorem 9 | `EndpointFactor.uniformPhysicalEndpointCompletion_from_AKS_Pippenger`; `EndpointPippenger.uniformPhysicalEndpointCompletion_from_pippenger` | The AKS-and-Pippenger result follows the quantitative receiver used in the written proof. The second result gives the same uniform odd-abelian cycle/path-factor conclusion from Pippenger alone. Neither prescribes endpoint pairings. The AKS premise of the first result is the near-regular form `EndpointMatching.Fractional.Rounding.AKSSetFamilyTheorem`; `AKSSourceIteration.absolute_AKS_input_from_native_bite` derives it from the one-bite statement, but no single declaration composes the two. |
| Proposition 9.1 | `CorralFormalization.Results.DensityObstruction.arbitrarily_large_density_obstructions_with_endpoint_budget` | Arbitrarily large odd cyclic counterexamples for every tolerance above one quarter, including the `K=1` budget. No claim is made about the boundary. |
| Theorem 10 | `CorralFormalization.Results.MatchingSharedTolerance.endpoint_and_finite_diversity_from_matching_inputs`; `endpoint_and_diversity_from_matching_inputs`; `EndpointPippenger.shared_tolerance_endpoint_path_and_diversity_pippenger` | The first result connects the AKS-and-Pippenger endpoint and both finite physical diversity floors with one tolerance, without the Latin-square input. The second additionally takes that input for the logarithmic conclusion. The Pippenger-only route has a corresponding finite statement and uses the Latin-square input for its logarithmic conclusion. The formal old-floor construction differs from the direct written proof. The AKS-route declarations take the near-regular AKS premise, as for Theorem 9. Their shared tolerance is produced by the declaration: it is a valid Theorem 9 tolerance, not an arbitrary one. |
| Corollary A.1, Theorem A.2 and Proposition A.3 | `EndpointPippenger.uniform_endpoint_and_path_terrace_from_pippenger`; `EndpointPippenger.switch_family_from_pippenger`; `EndpointPippenger.decorated_physical_counting_from_pippenger` | Path completion and the physical switch-family conclusions from Pippenger, including the shared tolerance. The count of a family is not a census of all corrals. Formula (A9) is stated with natural-number division, which is exact by Burnside's lemma. |
| Theorem B.1 | `EndpointMatching.UniversalCore.original_exact_matching_probability_at_smaller_rate`; `EndpointPippenger.original_exact_matching_probability_pippenger_at_smaller_rate` | Same original-sample exact-matching event, radius and a rate at least as strong as the stated rate, through the AKS or Pippenger route respectively. The required rate parameter is an explicit argument; the two routes need not have identical intermediate constructions. The AKS route takes the near-regular input, derivable from the one-bite statement as above. |
| Fractional Supplier and Actual Remainder Lemmas | `EndpointMatching.Fractional.JointRawEvent.common_fractional_and_quantitative_failure_probability` | Under the explicit source-shaped AKS one-bite input and its stated size threshold, one original-sample event satisfies both the complete robust fractional supplier and the full adaptive quantitative remainder conclusion, with the printed failure bound. The exact zero-or-three charge is no larger than the printed `+3`; the zero-free case needs no charge. Reservations, preselected matching and later edge ban retain their displayed scope, and the ban is not asserted for the subsequent absorber matching. |

The fractional supplier's displayed weight interval has a positive denominator. The Lean theorem for the tagged size bounds derives $q n/2\le m$ from the raw event and target-distance hypotheses. The [included audit](../lean/Audit.lean) checks the transitive axioms of the 19 principal declarations. Read each declaration's explicit assumptions alongside its axiom report.

The written bounded-error rounding argument is included with its proof;
the related [Beck–Fiala integer-making method](https://doi.org/10.1016/0166-218X%2881%2990022-6)
is classical. An explicit near-regular form of the quantitative matching
input is also recorded by [Arman, Rödl and Sales](https://arxiv.org/html/2102.09633v1),
preprint v1, Theorem 2.2. These are source-context citations, not new
assumptions introduced into the Lean development.

The external mathematical inputs are explicit theorem arguments:

- `EndpointTransitions.PippengerTheorem`, a 3-uniform formulation of
  [Alon–Yuster, Theorem 1.1](https://web.math.princeton.edu/~nalon/PDFS/ayhyper2.pdf);
- `AKSSubsetTransport.NativeBiteTheorem`, a source-shaped one-bite statement
  based on [Alon–Kim–Spencer, Theorem 2.1](https://tau.ac.il/~nogaa/PDFS/aks7.pdf);
- `EndpointMatching.Fractional.Rounding.AKSSetFamilyTheorem`, the near-regular
  consequence of that one-bite statement. The AKS-route declarations for
  Theorems 9, 10 and B.1 take it directly. The checked iteration
  `AKSSourceIteration.absolute_AKS_input_from_native_bite` derives it from
  `NativeBiteTheorem`; those declarations are not composed with it;
- `CorralFormalization.LatinCompletion.TerraceCompletion.Asymptotic.LatinSquareFactorialBound`,
  the standard bound for labelled Latin squares, recorded for example by
  [McKay–Wanless](https://arxiv.org/pdf/0909.2101).

The deterministic iteration deriving the near-regular AKS input from its
one-bite form is checked in Lean; the external one-bite theorem and its
probabilistic proof are not. The AKS-and-Pippenger endpoint and shared-tolerance
diversity declarations give the formal comparison for the written route.
The additional Pippenger-only formal route avoids an AKS premise for its
path-factor and finite-diversity conclusions; it does not prove the stated
square-root/logarithmic actual-remainder estimate. The written Appendix B
uses the quantitative AKS-based receiver as well as Pippenger for ordinary
transitions. The respective source-to-Lean interpretations have been reviewed
in writing, not formally derived from published prose.

The [claim map](CLAIM-MAP.md) identifies the declarations used together to
verify intermediate results. The [axiom audit](../lean/Audit.lean) reports
the ordinary Lean axioms `propext`, `Classical.choice` and `Quot.sound`.
The declaration types include the explicit mathematical theorem arguments
in addition to the axioms reported by the audit.
Neither the Python programs nor every line of the written proofs is claimed
to be formally verified.
