# Statement and proof map

This guide locates the written arguments and the corresponding Lean declarations or proof chains. The [formal scope](FORMAL-SCOPE.md) records their premises and proof differences. The [included audit](../lean/Audit.lean) checks the transitive axioms of the selected principal statements.

## Main article

| Statement | Written proof | Selected Lean declaration or chain and boundary |
| --- | --- | --- |
| Theorem 1 | Sections 2–5 | `CorralFormalization.optimalCorral_exists`: every `h>0`. Its general odd witness is the older construction; `CorralFormalization.OneSwapOdd.literal_original_witness` and `R_partition_and_exact_gaps` separately cover the printed odd construction. |
| Corollary 2 | Immediately after Theorem 1 | `CorralFormalization.originalCorral_iff_order_bound`: positive `h,n`. Lean proves the larger-order extension independently; the written proof cites BDGM26 for larger orders. |
| Lemma 4 | Section 2 | `CorralFormalization.transversal_block_translates_partition`, for arbitrary positive block size and actual residue transversals. |
| Lemma 5 | Section 2 | `CorralFormalization.finite_set_cyclic_gap_join`, for actual finite cyclic-gap multisets, equal heads or equal tail deficits, including the closing seams. |
| Theorem 3 | Section 6 | `CorralFormalization.EvenSwitches.evenSwitchFamily_odd_k` and `CorralFormalization.PhysicalCensus.evenSwitchFamily_real_log_lower`. The exact orbit count is for the constructed family. |
| Lemma 6 | Sections 6.1–6.3 | `CorralFormalization.Results.ConstructionCorrespondence.LiteralSwitchRows.symmetric_bit_rows_represented`, `CorralFormalization.EvenSwitches.rowA_gap_inventory`, `rowB_gap_inventory`, and `CorralFormalization.Results.ConstructionCorrespondence.SwitchBits.base_decompositions_card`. These declarations describe the literal row coordinates, the gap inventories and the number of unordered decompositions. |
| Theorem 7 | Section 7 | `CorralFormalization.Results.PrimeHeight.every_odd_prime_optimal_originalWitness_asymmetric`, for every original witness at odd prime height. |
| Theorem 8 | Section 7 | `CorralFormalization.Results.PhysicalPartitionUpper.sharp_global_census_bounds`, including all three displayed bounds for `h≥2`. In the same namespace, `prefix_allowed_card_le` bounds the available choices at each row, and `valid_families_count_le_branching_product` bounds the total count. |
| Theorem 9 | Appendix B | `EndpointFactor.uniformPhysicalEndpointCompletion_from_AKS_Pippenger` and definition `EndpointFactor.CycleCut.UniformPhysicalEndpointCompletion` supply the uniform odd-group conclusion along the quantitative matching route. `EndpointPippenger.uniformPhysicalEndpointCompletion_from_pippenger` gives the same conclusion from Pippenger alone. Both retain exact inventories and terminal sets, without a prescribed pairing. The AKS-route declaration takes the near-regular input; `AKSSourceIteration.absolute_AKS_input_from_native_bite` derives it from the one-bite statement. |
| Proposition 9.1 | Immediately after its statement | `CorralFormalization.Results.DensityObstruction.arbitrarily_large_density_obstructions_with_endpoint_budget`. It supplies arbitrarily large odd cyclic examples for each `ε>1/4`, with `1≤εn` and the exact physical counterexample predicate. The boundary `ε=1/4` is not asserted. |
| Theorem 10 | Sections 8.1–8.5 | `CorralFormalization.Results.MatchingSharedTolerance.endpoint_and_finite_diversity_from_matching_inputs` connects the AKS-and-Pippenger endpoint (near-regular AKS input, as for Theorem 9) and both finite floors at one tolerance; its `endpoint_and_diversity_from_matching_inputs` counterpart additionally takes the labelled Latin-square bound for the logarithmic conclusion. `EndpointPippenger.shared_tolerance_endpoint_path_and_finite_diversity_pippenger` gives both finite floors from Pippenger; its `shared_tolerance_endpoint_path_and_diversity_pippenger` counterpart additionally takes the Latin-square bound. The formal old-floor construction differs from the direct printed proof. |
| Lemma 11 | Section 8.3 | `CorralFormalization.LatinCompletion.GeneralTiles.explicit_optimal_corral`, `explicit_distinguished_tails`, `explicit_modified_isometry` and the related unchanged-segment, modified-tail and same-layout declarations. The input is an actual eligible terrace and an arbitrary cyclic 2/3 tiling; palette and retained-marker hypotheses remain explicit. |
| Corollary A.1 | Immediately after its statement | `EndpointPippenger.uniform_endpoint_and_path_terrace_from_pippenger`, retaining the actual path and the endpoint tolerance within that declaration. |
| Theorem A.2 | Sections A.1–A.4 | `EndpointPippenger.switch_family_from_pippenger`, with the stated eventual-height switch family and physical orbit lower bound. Pippenger supplies the terrace; no effective threshold or efficient terrace constructor is claimed. |
| Proposition A.3 | Section A.5 | `EndpointPippenger.decorated_physical_counting_from_pippenger`; the finite tiling identity is also `CorralFormalization.Results.SwitchFamily.Counting.C_binomial_formula_A8`. The exact counts are for the constructed physical family; `Q=2^m` is fixed at the actual height in all divisor terms. |
| Height-seven example | Sections 5.1 and 9 | The [check from the supplied JSON](supplement/formal/README.md) produces `HeightSevenCertificate.supplied_checked`. It checks the complete imported certificate and compares every stored row with the one-swap construction. The JSON importer supplies the values that Lean proves properties about. |

## Appendix B: matching and endpoint proof

| Statement or interface | Written proof | Selected Lean declaration or chain and boundary |
| --- | --- | --- |
| Theorem B.1 | Section B.4 | `EndpointMatching.UniversalCore.original_exact_matching_probability_at_smaller_rate` and `EndpointPippenger.original_exact_matching_probability_pippenger_at_smaller_rate`. Both state the original-sample event for all later allowed targets and permit the named rate after its parameter inequalities are supplied. The first takes the near-regular AKS input; the second uses Pippenger. The input can be derived from the source-shaped bite using `AKSSourceIteration.absolute_AKS_input_from_native_bite`. |
| Lemma B.2, selection graph | Section B.2.2 | `EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence.exists_selectionGraph_with_right_degree`, for every `s≥1`; the single graph handles all permitted later variable subsets. |
| Lemma B.3, coupled reservoirs | Section B.2.3 | The coupled-law chain includes `EndpointOriginalReservoir.parentLabel_mass`, `childLabel_P_mass`, `childLabel_Q_mass`, `original_to_independent_joint_labels` and `EndpointFullProduct.child_signed_containment`. The construction uses the categorical sampling law in groups of odd order. |
| Lemma B.4, packed availability | Section B.2.4 | `AbsorberInputs.AffineAvailability.uniform_affine_general_categorical_availability` and `uniform_affine_availability_on_augmented_sample`. They use nonempty fixed affine lists, complete collision tests, fixed label requests and the stated pivot and polynomial-query hypotheses. They do not infer extra gadget identities or completeness of an incorrectly supplied collision list. |
| Lemma B.5, coloured selectors | Section B.2.4 | `EndpointFlow.AbelianTransport.ColouredSelectors`, `AbsorberInputs.selector_same_sample_external_explicit_chernoff_error` and the deterministic selector/transport chain. The local availability and its numerical bounds must be supplied through that chain. |
| Lemma B.6, paired cover | Section B.2.5 | `AbsorberInputs.CategoricalQ.free_density_ordinary_cover_probability`, `PairedCoverAndBuffersEvent`, and `EndpointMatching.Tetrahedron.fourThirds_cover_exact_abelian`. The formal result covers the stated one-event adaptive choices, counts and buffers at free `0<τ≤1/3`. |
| Lemma B.7, fixed-cardinality absorber | Section B.2.6 | `EndpointSelector.FixedCardinality.fixedSelector_of_degreeSixteenGraph`, the selection graph and the selector supply. The deterministic assembly has graph and local-supply hypotheses; B.2 and B.5 are the corresponding suppliers. |
| Lemma B.8, universal core | Sections B.2.6–B.2.7 | `EndpointMatching.UniversalCore.universalCoreEvent_explicit_statement`, `originalCore_explicit_failure_probability` and `coreFailureBound_eventually_explicit_rate`, together with the sample-event chain. The order is one event, then every exclusion `U`, then a core, then every allowed residual. The statement is not a later-edge-ban guarantee for the absorber. |
| Fractional Supplier Lemma | Section B.3.2 | `EndpointMatching.UniversalCore.physicalRobustFractionalEvent_failure_probability` and `PhysicalRobustFractionalEvent`. One original event handles all permitted later targets and rooted-degree bans; no checksum, physical endpoint disjointness or odd-order hypothesis is required for this fractional statement. `EndpointMatching.Fractional.JointRawEvent.common_fractional_and_quantitative_failure_probability` additionally joins this supplier to the quantitative remainder on the same original event, under the explicit AKS one-bite input and size threshold. |
| Bounded-error Rounding Lemma | Section B.3.3 | `EndpointMatching.Fractional.Rounding.exists_matrix_rounding`, for finite zero-one matrices and a **positive** integer column bound, including already integral inputs. |
| Diffuse-perfect Rounding Corollary | Section B.3.3 | `EndpointMatching.Fractional.Rounding.diffuse_perfect_matching_from_AKS_set_family` and `diffuse_perfect_edge_deficit_of_AKS_set_family`. The near-regular AKS input is explicit and is supplied by the checked iteration from the native one-bite assumption. Unit fractional load at every actual vertex is required. |
| Actual Remainder Lemma | Section B.3.3 | `EndpointMatching.Fractional.JointRawEvent.QuantitativeActualRemainderEvent` and `common_fractional_and_quantitative_failure_probability` give the complete later-choice contract and the common event's probability from the explicit AKS one-bite input. `three_budget_controls_zeroCharge` pays the printed `+3`; `zero_free_budget_controls_zeroCharge` pays the no-zero exception. `AKSSourceIteration.physical_actual_remainder_from_native_bite` is the underlying raw-event result. |
| Lemma B.9 | Section B.5 | `EndpointTransitions.existsToleranceForOrdinaryMatching`, from Pippenger and the stated Fourier/target hypotheses. Lean uses bounded-error rounding for the regularisation where the written argument uses independent edge retention. |
| Router and factor closure | Section B.6 | `EndpointRouter.Switch.vertex_collision_classification`, `color_collision_classification`, `zero_color_coefficient`, `number_collision_equations`; `EndpointRouter.explicit_reservoirEvent_probability`; `EndpointRouter.adjacent_two_layers_router`; and the connected endpoint declarations in the Theorem 9 row. The 121 finite tests use the stated legal-port conditions; the final router setting is chosen after the matching. |

The quantitative near-regular theorem and its rate are due to
Alon–Kim–Spencer. The article discusses the antecedents of the qualitative
fractional-to-integral implication and states the hypotheses of the joint
adaptive result in the Actual Remainder Lemma.

## Scope of this map

The table identifies the statements and proof components covered by the Lean
development. The [axiom audit](../lean/Audit.lean) reports the transitive
axioms of the principal declarations. The AKS-and-Pippenger formal path and
the written proof use the quantitative matching, core and router framework.
The Pippenger-only path
proves the same endpoint conclusion through a different near-matching route.
The displayed mathematical proofs are not all claimed to be literal Lean
translations, and the external source statements are explicit arguments
rather than proved Lean theorems. The Python implementation is not formally
verified.
