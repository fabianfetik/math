import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.Availability
import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.RawMinusCore

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly
open EndpointFullProduct
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The proved Q event and supplied P selectors, graph and numerical
inventory budgets yield one fixed absorbing core after every U and before
all later residuals. The remaining P/graph/count hypotheses are explicit. -/
theorem explicitQEvent_core_of_selector_graph_and_budgets
    (τ : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3)
    (hodd : Odd (Fintype.card G)) (hnlarge : (4000 : ℝ) ≤ τ^2 * Fintype.card G)
    (ω : FullSample G) (pBudget : ℕ) (hlocal : ColouredSelectors ω pBudget)
    (hQevent : Buffer.CoreConstructionEvent τ ω)
    (hquery : ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      ∀ p, let Q := availablePairInventory (ReservoirVertex ω true) U p
        1 ≤ Q.card - paddingQuota τ (Fintype.card G) ∧
        Q.card - paddingQuota τ (Fintype.card G) ≤ Q.card ∧
        Q.card ≤ 2 * (Q.card - paddingQuota τ (Fintype.card G)) ∧
        Nonempty (ContiguousSelectionGraph (Q.card - paddingQuota τ (Fintype.card G)) 16))
    (hbudget : ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      let Q := availablePairInventory (ReservoirVertex ω true) U
      2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
        ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - paddingQuota τ (Fintype.card G)))) +
          1724 * ((Q p).card - paddingQuota τ (Fintype.card G))) ≤ pBudget) :
    ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      ∃ A : Finset (Vertex G),
        (∀ v ∈ A, v.2 ≠ 0 ∧ signedMinus v.1 ω v.2) ∧
        Disjoint (support A) U ∧
        A.card ≤ (∑ p : Fin 3, 862 *
          ((availablePairInventory (ReservoirVertex ω true) U p).card -
            paddingQuota τ (Fintype.card G))) +
          ∑ p : Fin 3, 2 * (availablePairInventory (ReservoirVertex ω true) U p).card ∧
        AbsorbsUpTo A (quadraticCoreCapacity τ (Fintype.card G)) := by
  intro U hU
  obtain ⟨B,hcount,hmem,huniq,hmatch⟩ := hQevent.2 U hU
  have hfloor := quadratic_capacity_budgets τ (Fintype.card G) U.card hτ hτmax hnlarge hU
  exact sampled_rawMinus_core_of_tetrahedron_parameters hodd ω pBudget
    (quadraticCoverBudget τ (Fintype.card G)) (quadraticCoreCapacity τ (Fintype.card G))
    (paddingQuota τ (Fintype.card G)) U hlocal hQevent.1 hfloor.1 hfloor.2.1
    (hquery U hU) (hbudget U hU) B Buffer.pick hmem huniq hmatch hcount

end
end EndpointMatching.UniversalCore
