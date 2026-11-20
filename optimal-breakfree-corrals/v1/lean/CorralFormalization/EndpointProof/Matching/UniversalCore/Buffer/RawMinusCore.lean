import CorralFormalization.EndpointProof.Matching.UniversalCore.SampledCore
import CorralFormalization.EndpointProof.Flow.Tetrahedron.Supplier
import CorralFormalization.EndpointProof.Flow.Tetrahedron.PairedCover

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly
open EndpointFullProduct EndpointOriginalReservoir
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Every vertex of either actual paired child reservoir lies in the
corresponding signed raw-minus part of that same augmentation. -/
theorem reservoirVertex_signedMinus (ω : FullSample G) (isQ : Bool) (v : Vertex G)
    (hv : ReservoirVertex ω isQ v) : signedMinus v.1 ω v.2 := by
  obtain ⟨o,side,hcoord,hchild⟩ := hv
  rw [← hcoord]
  exact child_signed_containment v.1 isQ side ω o hchild

/-- The fixed core retains the stronger raw-minus containment required
by the universal absorbing core theorem; all supplied data belong to the same actual augmentation. -/
theorem sampled_rawMinus_core_of_fourThirds_covers {ι : Type*} [DecidableEq ι]
    (hodd : Odd (Fintype.card G)) (ω : FullSample G)
    (pBudget qBudget capacity K : ℕ) (U : Finset G)
    (hlocal : ColouredSelectors ω pBudget)
    (hcovers : FourThirdsCoversAvailable (ReservoirVertex ω true) qBudget)
    (hcoverBudget : 2 * U.card + 20 * capacity ≤ qBudget)
    (hK : 4 * capacity ≤ 3 * K)
    (hquery : ∀ p, let Q := availablePairInventory (ReservoirVertex ω true) U p
      1 ≤ Q.card - K ∧ Q.card - K ≤ Q.card ∧ Q.card ≤ 2 * (Q.card - K) ∧
        Nonempty (ContiguousSelectionGraph (Q.card - K) 16))
    (hbudget :
      let Q := availablePairInventory (ReservoirVertex ω true) U
      2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
        ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
          1724 * ((Q p).card - K)) ≤ pBudget)
    (buffers : Finset ι) (pick : ι → Fin 3 → Finset (Vertex G))
    (hBmem : ∀ i ∈ buffers, ∀ p, pick i p ∈
      availablePairInventory (ReservoirVertex ω true) U p)
    (hBunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hBmatch : ∀ i ∈ buffers, Nonempty (Matching (Finset.univ.biUnion (pick i))))
    (hcount : 3 * K ≤ buffers.card) :
    ∃ A : Finset (Vertex G),
      (∀ v ∈ A, v.2 ≠ 0 ∧ signedMinus v.1 ω v.2) ∧
      Disjoint (support A) U ∧
      A.card ≤ (∑ p : Fin 3, 862 *
        ((availablePairInventory (ReservoirVertex ω true) U p).card - K)) +
        ∑ p : Fin 3, 2 * (availablePairInventory (ReservoirVertex ω true) U p).card ∧
      AbsorbsUpTo A capacity := by
  let P := ReservoirVertex ω false
  let Qprop := ReservoirVertex ω true
  let Q := availablePairInventory Qprop U
  let R : Vertex G → Prop := fun v => v.2 ≠ 0 ∧ signedMinus v.1 ω v.2
  have hP := pairReservoir_of_reservoirVertex ω false
  have hQ := pairReservoir_of_reservoirVertex ω true
  have hlocal' : LocalSupply P pBudget 16 :=
    localSupply_of_colouredSelectors ω pBudget 16 (by omega) hlocal
  have hrawP : ∀ v, P v → R v := by
    intro v hv
    exact ⟨hP.nonzero v hv, reservoirVertex_signedMinus ω false v hv⟩
  have hrawQ : ∀ p T, T ∈ Q p → ∀ v, v ∈ T → R v := by
    intro p T hT v hv
    have hvQ : Qprop v := availablePairInventory_inside Qprop hQ U p T hT v hv
    exact ⟨hQ.nonzero v hvQ, reservoirVertex_signedMinus ω true v hvQ⟩
  have hcover := fourThirdsCovers_supply_core hodd Qprop hQ qBudget capacity K U
    hcovers hcoverBudget hK
  exact fixed_core_from_supplies hP hlocal' Q U (availablePairInventory_legal Qprop hQ U)
    hquery hbudget hrawP hrawQ (availablePairInventory_avoids Qprop U)
    buffers pick hBmem hBunique hBmatch hcount hcover

/-- Concrete tetrahedron parameters supply the four-thirds cover;
the raw-minus core is then assembled from the same Q/P sample. -/
theorem sampled_rawMinus_core_of_tetrahedron_parameters {ι : Type*} [DecidableEq ι]
    (hodd : Odd (Fintype.card G)) (ω : FullSample G)
    (pBudget qBudget capacity K : ℕ) (U : Finset G)
    (hlocal : ColouredSelectors ω pBudget)
    (hparameters : EndpointMatching.Tetrahedron.TetrahedronParametersAvailable
      (ReservoirVertex ω true) qBudget)
    (hcoverBudget : 2 * U.card + 20 * capacity ≤ qBudget)
    (hK : 4 * capacity ≤ 3 * K)
    (hquery : ∀ p, let Q := availablePairInventory (ReservoirVertex ω true) U p
      1 ≤ Q.card - K ∧ Q.card - K ≤ Q.card ∧ Q.card ≤ 2 * (Q.card - K) ∧
        Nonempty (ContiguousSelectionGraph (Q.card - K) 16))
    (hbudget :
      let Q := availablePairInventory (ReservoirVertex ω true) U
      2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
        ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
          1724 * ((Q p).card - K)) ≤ pBudget)
    (buffers : Finset ι) (pick : ι → Fin 3 → Finset (Vertex G))
    (hBmem : ∀ i ∈ buffers, ∀ p, pick i p ∈
      availablePairInventory (ReservoirVertex ω true) U p)
    (hBunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hBmatch : ∀ i ∈ buffers, Nonempty (Matching (Finset.univ.biUnion (pick i))))
    (hcount : 3 * K ≤ buffers.card) :
    ∃ A : Finset (Vertex G),
      (∀ v ∈ A, v.2 ≠ 0 ∧ signedMinus v.1 ω v.2) ∧
      Disjoint (support A) U ∧
      A.card ≤ (∑ p : Fin 3, 862 *
        ((availablePairInventory (ReservoirVertex ω true) U p).card - K)) +
        ∑ p : Fin 3, 2 * (availablePairInventory (ReservoirVertex ω true) U p).card ∧
      AbsorbsUpTo A capacity := by
  have hsupply := EndpointMatching.Tetrahedron.fourPairSupplier_of_parameters
    (ReservoirVertex ω true) qBudget hparameters
  have hcovers := EndpointMatching.Tetrahedron.fourThirdsCovers_of_fourPairSupplier_abelian
    G (inferInstance : AddCommGroup G) hodd (ReservoirVertex ω true) qBudget hsupply
  exact sampled_rawMinus_core_of_fourThirds_covers hodd ω pBudget qBudget capacity K U
    hlocal hcovers hcoverBudget hK hquery hbudget buffers pick hBmem hBunique hBmatch hcount

end
end EndpointMatching.UniversalCore
