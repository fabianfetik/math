import CorralFormalization.EndpointProof.Matching.UniversalCore.CoreAssembly
import CorralFormalization.EndpointProof.Matching.UniversalCore.SelectorInstallation

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- The deterministic core from local-selector, graph, buffer and paired-cover
supplies. The cover may depend on S but the resulting A is chosen before S. -/
theorem fixed_core_from_supplies {ι : Type*} [DecidableEq ι]
    {P R : Vertex G → Prop} {budget K capacity : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget 16)
    (Q : Fin 3 → Finset (Finset (Vertex G))) (U : Finset G)
    (hlegal : ∀ p T, T ∈ Q p → LegalPair p T)
    (hquery : ∀ p, 1 ≤ (Q p).card - K ∧
      (Q p).card - K ≤ (Q p).card ∧
      (Q p).card ≤ 2 * ((Q p).card - K) ∧
      Nonempty (ContiguousSelectionGraph ((Q p).card - K) 16))
    (hbudget : 2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
      ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
        1724 * ((Q p).card - K)) ≤ budget)
    (hrawP : ∀ v, P v → R v)
    (hrawQ : ∀ p T, T ∈ Q p → ∀ v, v ∈ T → R v)
    (hQavoid : Disjoint (support ((Finset.univ.biUnion Q).biUnion id)) U)
    (buffers : Finset ι) (pick : ι → Fin 3 → Finset (Vertex G))
    (hBmem : ∀ i ∈ buffers, ∀ p, pick i p ∈ Q p)
    (hBunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hBmatch : ∀ i ∈ buffers, Nonempty (Matching (Finset.univ.biUnion (pick i))))
    (hcount : 3 * K ≤ buffers.card)
    (hcover : ∀ S : Finset (Vertex G),
      (∀ v ∈ S, v.2 ≠ 0) → Balanced S → (∑ v ∈ S, v.2 = 0) →
      Disjoint ((Finset.univ.biUnion Q).biUnion id) S → S.card ≤ capacity →
      ∃ (T : Finset (Finset (Vertex G))) (m : ℕ),
        T ⊆ Finset.univ.biUnion Q ∧
        (∀ p, (T ∩ Q p).card = m) ∧ m ≤ K ∧
        Nonempty (Matching (S ∪ T.biUnion id))) :
    ∃ A : Finset (Vertex G),
      (∀ v ∈ A, R v) ∧ Disjoint (support A) U ∧
      A.card ≤ (∑ p : Fin 3, 862 * ((Q p).card - K)) +
        ∑ p : Fin 3, 2 * (Q p).card ∧
      AbsorbsUpTo A capacity := by
  classical
  have hquery' : ∀ p, 1 ≤ (Q p).card - K ∧
      (Q p).card - K ≤ (Q p).card ∧
      (Q p).card ≤ 2 * ((Q p).card - K) ∧
      (∀ T ∈ Q p, LegalPair p T) ∧
      Nonempty (ContiguousSelectionGraph ((Q p).card - K) 16) := by
    intro p
    exact ⟨(hquery p).1, (hquery p).2.1, (hquery p).2.2.1,
      hlegal p, (hquery p).2.2.2⟩
  obtain ⟨sel, hselcard, hselavoid, hseldis, hselQ⟩ :=
    three_selectors_of_localSupply_and_graphs hP hlocal Q U hquery' hbudget
  let I : Fin 3 → Finset (Vertex G) := fun p => (sel p).interior
  let A := coreVertices Q I
  have hAbs : AbsorbsUpTo A capacity := by
    apply fixed_core_absorbs_of_pair_covers P Q K capacity sel buffers pick
      hlegal hseldis hselQ hBmem hBunique hBmatch hcount
    intro S hnz hb hsum hAS hsize
    apply hcover S hnz hb hsum ?_ hsize
    exact hAS.mono_left Finset.subset_union_right
  refine ⟨A, ?_, ?_, ?_, hAbs⟩
  · apply coreVertices_inside Q I R ?_ hrawQ
    intro p v hv
    exact hrawP v ((sel p).inside v hv)
  · exact coreVertices_support_avoids Q I U hselavoid hQavoid
  · calc
      _ ≤ (∑ p : Fin 3, (I p).card) + ∑ p : Fin 3, 2 * (Q p).card :=
        coreVertices_card_le Q I hlegal
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum (fun p _ => hselcard p)) _

end
end EndpointMatching.UniversalCore
