import CorralFormalization.EndpointProof.Matching.UniversalCore.PairedCoverInventory

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly
open EndpointFullProduct
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Every vertex of the canonical inverse-pair inventory is actually in
its paired nonzero reservoir. -/
theorem availablePairInventory_inside (Q : Vertex G → Prop) (hQ : PairReservoir Q)
    (U : Finset G) : ∀ p T, T ∈ availablePairInventory Q U p → ∀ v ∈ T, Q v := by
  intro p T hT v hv
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hT
  have hQa : Q (p,a) := (Finset.mem_filter.mp ha).2.1
  simp only [pairOf, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact hQa
  · exact hQ.paired (p,a) hQa

/-- The older native cover output is also a valid four-thirds cover at its
own, unchanged budget. -/
theorem fourThirdsCovers_of_pairedCovers (ω : FullSample G) (budget : ℕ)
    (hcovers : PairedCoversAvailable ω budget) :
    FourThirdsCoversAvailable (ReservoirVertex ω true) budget := by
  intro S hb hnz hsum U hbudget
  obtain ⟨C⟩ := hcovers S hb hnz hsum U hbudget
  refine ⟨{
    added := C.added
    pairsPerPart := C.pairsPerPart
    added_Q := C.added_Q
    added_paired := C.added_paired
    added_nonzero := C.added_nonzero
    avoids := ?_
    part_card := C.part_card
    pair_bound := ?_
    matching := C.matching
  }⟩
  · apply C.avoids.mono_right
    intro x hx
    simp only [Finset.mem_union, support, Finset.mem_image] at hx ⊢
    rcases hx with hU | ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
    · exact Or.inl (Or.inl hU)
    · exact Or.inl (Or.inr ⟨v,hv,rfl⟩)
    · exact Or.inr ⟨v.2, Or.inr ⟨v,hv,rfl⟩, rfl⟩
  · have h := C.pairs_le
    omega

/-- A single actual augmented sample supplies a fixed universal core from
its local selector event, a four-thirds paired-cover event, a canonical Q
inventory, and explicit graph, count, buffer and numerical conditions. -/
theorem sampled_core_of_fourThirds_covers {ι : Type*} [DecidableEq ι]
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
      (∀ v ∈ A, v.2 ≠ 0 ∧ EndpointFullProduct.originalSigned v.1
        (EndpointFullProduct.originalProcess ω) v.2) ∧
      Disjoint (support A) U ∧
      A.card ≤ (∑ p : Fin 3, 862 *
        ((availablePairInventory (ReservoirVertex ω true) U p).card - K)) +
        ∑ p : Fin 3, 2 * (availablePairInventory (ReservoirVertex ω true) U p).card ∧
      AbsorbsUpTo A capacity := by
  let P := ReservoirVertex ω false
  let Qprop := ReservoirVertex ω true
  let Q := availablePairInventory Qprop U
  let R : Vertex G → Prop := fun v => v.2 ≠ 0 ∧
    EndpointFullProduct.originalSigned v.1 (EndpointFullProduct.originalProcess ω) v.2
  have hP := pairReservoir_of_reservoirVertex ω false
  have hQ := pairReservoir_of_reservoirVertex ω true
  have hlocal' : LocalSupply P pBudget 16 :=
    localSupply_of_colouredSelectors ω pBudget 16 (by omega) hlocal
  have hrawP : ∀ v, P v → R v := by
    intro v hv
    exact ⟨hP.nonzero v hv, ReservoirVertex.originalSigned ω false v hv⟩
  have hrawQ : ∀ p T, T ∈ Q p → ∀ v, v ∈ T → R v := by
    intro p T hT v hv
    have hvQ : Qprop v := availablePairInventory_inside Qprop hQ U p T hT v hv
    exact ⟨hQ.nonzero v hvQ, ReservoirVertex.originalSigned ω true v hvQ⟩
  have hcover := fourThirdsCovers_supply_core hodd Qprop hQ qBudget capacity K U
    hcovers hcoverBudget hK
  exact fixed_core_from_supplies hP hlocal' Q U (availablePairInventory_legal Qprop hQ U)
    hquery hbudget hrawP hrawQ (availablePairInventory_avoids Qprop U)
    buffers pick hBmem hBunique hBmatch hcount hcover

end
end EndpointMatching.UniversalCore
