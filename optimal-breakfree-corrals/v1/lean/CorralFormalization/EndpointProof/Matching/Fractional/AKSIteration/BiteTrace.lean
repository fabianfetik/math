import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.SourceBite
/-!
# Actual matching and waste across a finite bite trace

These are deterministic consequences of a supplied sequence of finite
bites. They do not assert that such a sequence exists or pay the source's
numerical bounds. The sequence may be padded by empty bites after stopping.
-/

open scoped Classical BigOperators
open EndpointMatching.Fractional.Rounding

namespace AKSBiteTrace
open AKSSourceBite
noncomputable section
universe u

variable {V : Type u} [Fintype V]

def roundEdges (M : ℕ → Finset (Finset V)) (m : ℕ) : Finset (Finset V) :=
  (Finset.range m).biUnion M

def roundWaste (W : ℕ → Finset V) (m : ℕ) : Finset V :=
  (Finset.range m).biUnion W

omit [Fintype V] in
/-- Once a vertex is removed it does not reappear in a later round. -/
theorem vertices_antitone (U : ℕ → Finset V) (M : ℕ → Finset (Finset V))
    (W : ℕ → Finset V) (hstep : ∀ i, U (i+1) = remaining (U i) (M i) (W i)) :
    Antitone U := by
  apply antitone_nat_of_succ_le
  intro i
  rw [hstep i]
  exact remaining_subset _ _ _

omit [Fintype V] in
/-- Edges chosen in different rounds are physically disjoint. -/
theorem different_rounds_disjoint (U : ℕ → Finset V) (M : ℕ → Finset (Finset V))
    (W : ℕ → Finset V) (hstep : ∀ i, U (i+1) = remaining (U i) (M i) (W i))
    (hinside : ∀ i e, e ∈ M i → e ⊆ U i)
    {i j : ℕ} (hij : i < j) {e f : Finset V} (he : e ∈ M i) (hf : f ∈ M j) :
    Disjoint e f := by
  have hanti := vertices_antitone U M W hstep
  have hfj : f ⊆ U (i+1) := (hinside j f hf).trans (hanti (Nat.succ_le_of_lt hij))
  apply Finset.disjoint_left.mpr
  intro x hxe hxf
  have hcovered : x ∈ covered (M i) := Finset.mem_biUnion.mpr ⟨e,he,hxe⟩
  have hrem : x ∈ remaining (U i) (M i) (W i) := by
    rw [← hstep i]
    exact hfj hxf
  have hn := (Finset.mem_sdiff.mp hrem).2
  exact hn (Finset.mem_union_left _ hcovered)

omit [Fintype V] in
/-- The union of the actual local matchings is again an actual matching. -/
theorem union_isMatching (U : ℕ → Finset V) (M : ℕ → Finset (Finset V))
    (W : ℕ → Finset V) (hstep : ∀ i, U (i+1) = remaining (U i) (M i) (W i))
    (hinside : ∀ i e, e ∈ M i → e ⊆ U i)
    (hmatching : ∀ i, IsMatching id (M i)) (m : ℕ) :
    IsMatching id (roundEdges M m) := by
  intro e he f hf hne
  obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp he
  obtain ⟨j,hj,hfj⟩ := Finset.mem_biUnion.mp hf
  rcases lt_trichotomy i j with hij | hij | hji
  · exact different_rounds_disjoint U M W hstep hinside hij hei hfj
  · subst j
    exact hmatching i hei hfj hne
  · exact (different_rounds_disjoint U M W hstep hinside hji hfj hei).symm

omit [Fintype V] in
/-- Every unmatched initial vertex either remains at the end or was wasted
in at least one round. Waste is not required to be disjoint from a matching
or from other waste sets. -/
theorem uncovered_subset_final_or_waste
    (U : ℕ → Finset V) (M : ℕ → Finset (Finset V)) (W : ℕ → Finset V)
    (hstep : ∀ i, U (i+1) = remaining (U i) (M i) (W i)) (m : ℕ) :
    U 0 \ covered (roundEdges M m) ⊆ U m ∪ roundWaste W m := by
  intro x hx
  have hx0 := (Finset.mem_sdiff.mp hx).1
  have hxcover := (Finset.mem_sdiff.mp hx).2
  by_cases hxw : x ∈ roundWaste W m
  · exact Finset.mem_union_right _ hxw
  · apply Finset.mem_union_left
    have hin : ∀ i ≤ m, x ∈ U i := by
      intro i hi
      induction i with
      | zero => exact hx0
      | succ i ih =>
        have him : i < m := by omega
        have hprev : x ∈ U i := ih (by omega)
        have hnotM : x ∉ covered (M i) := by
          intro hxm
          obtain ⟨e,he,hxe⟩ := Finset.mem_biUnion.mp hxm
          apply hxcover
          exact Finset.mem_biUnion.mpr ⟨e,
            Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr him,he⟩,hxe⟩
        have hnotW : x ∉ W i := by
          intro hxWi
          apply hxw
          exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr him,hxWi⟩
        rw [hstep i]
        exact Finset.mem_sdiff.mpr ⟨hprev, by
          simp only [Finset.mem_union, not_or]
          exact ⟨hnotM,hnotW⟩⟩
    exact hin m le_rfl

omit [Fintype V] in
/-- The source's finite uncovered-set accounting, proved on actual sets. -/
theorem uncovered_card_le
    (U : ℕ → Finset V) (M : ℕ → Finset (Finset V)) (W : ℕ → Finset V)
    (hstep : ∀ i, U (i+1) = remaining (U i) (M i) (W i)) (m : ℕ) :
    (U 0 \ covered (roundEdges M m)).card ≤
      (U m).card + ∑ i ∈ Finset.range m, (W i).card := by
  calc
    _ ≤ (U m ∪ roundWaste W m).card :=
      Finset.card_le_card (uncovered_subset_final_or_waste U M W hstep m)
    _ ≤ (U m).card + (roundWaste W m).card := Finset.card_union_le _ _
    _ ≤ (U m).card + ∑ i ∈ Finset.range m, (W i).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le _

omit [Fintype V] in
/-- Successive induced edge families contain only original edges. -/
theorem induced_edge_families_antitone (U : ℕ → Finset V)
    (H : ℕ → Finset (Finset V))
    (hstep : ∀ i, H (i+1) = induced (H i) (U (i+1))) : Antitone H := by
  apply antitone_nat_of_succ_le
  intro i
  rw [hstep i]
  exact Finset.filter_subset _ _

omit [Fintype V] in
/-- The collected matchings form an actual subfamily of the initial graph. -/
theorem roundEdges_subset_initial (U : ℕ → Finset V)
    (H M : ℕ → Finset (Finset V))
    (hH : ∀ i, H (i+1) = induced (H i) (U (i+1)))
    (hM : ∀ i, M i ⊆ H i) (m : ℕ) : roundEdges M m ⊆ H 0 := by
  have hanti := induced_edge_families_antitone U H hH
  intro e he
  obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp he
  exact hanti (Nat.zero_le i) (hM i hei)

/-- A supplied finite bite trace produces an actual matching in the
original edge family and bounds its actual uncovered vertices by the final
inventory plus the sum of the waste counts. -/
theorem matching_of_finite_trace
    (U : ℕ → Finset V) (H M : ℕ → Finset (Finset V)) (W : ℕ → Finset V)
    (hU0 : U 0 = Finset.univ)
    (hU : ∀ i, U (i+1) = remaining (U i) (M i) (W i))
    (hH : ∀ i, H (i+1) = induced (H i) (U (i+1)))
    (hMH : ∀ i, M i ⊆ H i)
    (hinside : ∀ i e, e ∈ M i → e ⊆ U i)
    (hmatching : ∀ i, IsMatching id (M i)) (m : ℕ) :
    ∃ P : Finset (Finset V), P ⊆ H 0 ∧ IsMatching id P ∧
      (uncovered id P).card ≤ (U m).card + ∑ i ∈ Finset.range m, (W i).card := by
  refine ⟨roundEdges M m, roundEdges_subset_initial U H M hH hMH m,
    union_isMatching U M W hU hinside hmatching m, ?_⟩
  have hb := uncovered_card_le U M W hU m
  simpa [uncovered,covered,hU0] using hb

end
end AKSBiteTrace
