import CorralFormalization.EndpointProof.Flow.AbelianTransport.AdditiveModel

/-!
The deterministic last step of the exact receiver, over the existing
additive-group hypergraph.  Existence of the universal core and of the near
matching is deliberately not claimed here.  The unmatched set is the actual
set difference of the target, with no padding or replacement vertices.
-/

open scoped Classical BigOperators

namespace EndpointMatching.AbsorptionAssembly

open EndpointFlow.AbelianTransport

noncomputable section

variable {G : Type*} [AddCommGroup G]

theorem matching_edge_subset {T : Finset (Vertex G)} (M : Matching T)
    {E : Finset (Vertex G)} (hE : E ∈ M.edges) : E ⊆ T := by
  intro v hv
  rw [← M.cover]
  exact Finset.mem_biUnion.mpr ⟨E, hE, hv⟩

def emptyMatching : Matching (∅ : Finset (Vertex G)) where
  edges := ∅
  valid := by simp
  disjoint := by simp
  cover := by simp

def unionMatching {S T : Finset (Vertex G)}
    (M : Matching S) (N : Matching T) (hST : Disjoint S T) : Matching (S ∪ T) where
  edges := M.edges ∪ N.edges
  valid := by
    intro E hE
    rcases Finset.mem_union.mp hE with hE | hE
    · exact M.valid E hE
    · exact N.valid E hE
  disjoint := by
    intro E hE F hF hEF
    rcases Finset.mem_union.mp hE with hE | hE <;>
      rcases Finset.mem_union.mp hF with hF | hF
    · exact M.disjoint hE hF hEF
    · exact hST.mono (matching_edge_subset M hE) (matching_edge_subset N hF)
    · exact hST.symm.mono (matching_edge_subset N hE) (matching_edge_subset M hF)
    · exact N.disjoint hE hF hEF
  cover := by rw [Finset.union_biUnion, M.cover, N.cover]

theorem hyperedge_slice_card {E : Finset (Vertex G)} (hE : Hyperedge E)
    (p : Fin 3) : (slice E p).card = 1 := by
  obtain ⟨x, y, z, _, rfl⟩ := hE
  fin_cases p <;> simp [slice, Finset.filter_insert, Finset.filter_singleton]

theorem hyperedge_sum_eq_zero {E : Finset (Vertex G)} (hE : Hyperedge E) :
    ∑ v ∈ E, v.2 = 0 := by
  obtain ⟨x, y, z, hsum, rfl⟩ := hE
  simpa [add_assoc] using hsum

theorem matching_slice_card {T : Finset (Vertex G)} (M : Matching T) (p : Fin 3) :
    (slice T p).card = M.edges.card := by
  have hcover : slice T p = M.edges.biUnion (fun E => slice E p) := by
    conv_lhs => rw [← M.cover]
    ext v
    simp [slice]
    aesop
  have hd : (M.edges : Set (Finset (Vertex G))).PairwiseDisjoint (fun E => slice E p) := by
    intro E hE F hF hEF
    exact (M.disjoint hE hF hEF).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [hcover, Finset.card_biUnion hd]
  calc
    _ = ∑ _E ∈ M.edges, (1 : ℕ) := Finset.sum_congr rfl (fun E hE =>
      hyperedge_slice_card (M.valid E hE) p)
    _ = M.edges.card := by simp

theorem matching_balanced {T : Finset (Vertex G)} (M : Matching T) : Balanced T := by
  intro p
  rw [matching_slice_card M p, matching_slice_card M 0]

theorem matching_sum_eq_zero {T : Finset (Vertex G)} (M : Matching T) :
    ∑ v ∈ T, v.2 = 0 := by
  rw [← M.cover]
  change (∑ v ∈ M.edges.biUnion (fun E => E), v.2) = 0
  rw [Finset.sum_biUnion M.disjoint]
  exact Finset.sum_eq_zero (fun E hE => hyperedge_sum_eq_zero (M.valid E hE))

/-- The actual unmatched inventory in the receiver. -/
def residual (T A P : Finset (Vertex G)) : Finset (Vertex G) := T \ (A ∪ P)

omit [AddCommGroup G] in
theorem residual_disjoint_reserved (T A P : Finset (Vertex G)) :
    Disjoint (residual T A P) (A ∪ P) := Finset.sdiff_disjoint

omit [AddCommGroup G] in
theorem reserved_union_residual {T A P : Finset (Vertex G)}
    (hA : A ⊆ T) (hP : P ⊆ T) : (A ∪ P) ∪ residual T A P = T := by
  exact Finset.union_sdiff_of_subset (Finset.union_subset hA hP)

theorem residual_balanced {T A P : Finset (Vertex G)}
    (hT : Balanced T) (hA : Balanced A) (M : Matching P)
    (hAT : A ⊆ T) (hPT : P ⊆ T) (hAP : Disjoint A P) :
    Balanced (residual T A P) := by
  have hsplit (p : Fin 3) :
      (slice T p).card = (slice A p).card + (slice P p).card +
        (slice (residual T A P) p).card := by
    have hfilter : slice T p =
        (slice A p ∪ slice P p) ∪ slice (residual T A P) p := by
      conv_lhs => rw [← reserved_union_residual hAT hPT]
      simp only [slice, Finset.filter_union]
    have hdAP : Disjoint (slice A p) (slice P p) :=
      hAP.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hdS : Disjoint (slice A p ∪ slice P p) (slice (residual T A P) p) := by
      apply (residual_disjoint_reserved T A P).symm.mono
      · exact Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      · exact Finset.filter_subset _ _
    rw [hfilter, Finset.card_union_of_disjoint hdS, Finset.card_union_of_disjoint hdAP]
  intro p
  have hp := hsplit p
  have h0 := hsplit 0
  have ht := hT p
  have ha := hA p
  have hm := matching_balanced M p
  omega

theorem residual_sum_eq_zero {T A P : Finset (Vertex G)}
    (hT : ∑ v ∈ T, v.2 = 0) (hA : ∑ v ∈ A, v.2 = 0) (M : Matching P)
    (hAT : A ⊆ T) (hPT : P ⊆ T) (hAP : Disjoint A P) :
    ∑ v ∈ residual T A P, v.2 = 0 := by
  have hsplit : (∑ v ∈ T, v.2) =
      ((∑ v ∈ A, v.2) + ∑ v ∈ P, v.2) + ∑ v ∈ residual T A P, v.2 := by
    calc
      _ = ∑ v ∈ (A ∪ P) ∪ residual T A P, v.2 := by
        rw [reserved_union_residual hAT hPT]
      _ = _ := by
        rw [Finset.sum_union (residual_disjoint_reserved T A P).symm,
          Finset.sum_union hAP]
  simpa only [hT, hA, matching_sum_eq_zero M, zero_add] using hsplit.symm

/-- Exactly the residual class in H1: nonzero, balanced, zero-sum, disjoint
from the already chosen core, and bounded in total tagged cardinality. -/
def AbsorbsUpTo (A : Finset (Vertex G)) (capacity : ℕ) : Prop :=
  ∀ S : Finset (Vertex G), (∀ v ∈ S, v.2 ≠ 0) → Balanced S →
    (∑ v ∈ S, v.2 = 0) → Disjoint A S → S.card ≤ capacity →
      Nonempty (Matching (A ∪ S))

theorem AbsorbsUpTo.matches_empty {A : Finset (Vertex G)} {capacity : ℕ}
    (hA : AbsorbsUpTo A capacity) : Nonempty (Matching A) := by
  simpa using hA ∅ (by simp) (by simp [EndpointFlow.AbelianTransport.Balanced, slice]) (by simp) (by simp) (by simp)

/-- Near matching data on the actual complement.  Balance and checksum of
the residual are not premises: they are proved from the target and core.
The nonzero conclusion is the separate endpoint-zero step in the paper. -/
structure CompatibleNearMatching (T A : Finset (Vertex G)) (capacity : ℕ) where
  covered : Finset (Vertex G)
  matching : Matching covered
  inside : covered ⊆ T \ A
  nonzero : ∀ v ∈ residual T A covered, v.2 ≠ 0
  deficit : (residual T A covered).card ≤ capacity

/-- Absorption plus an actually compatible near matching gives an exact
matching on precisely the original target.  No residual balancing or sum
condition is smuggled into the near-matching output. -/
theorem exact_of_absorber_and_nearMatching {T A : Finset (Vertex G)} {capacity : ℕ}
    (hT : Balanced T) (hsum : ∑ v ∈ T, v.2 = 0) (hAT : A ⊆ T)
    (habs : AbsorbsUpTo A capacity) (near : CompatibleNearMatching T A capacity) :
    Nonempty (Matching T) := by
  obtain ⟨MA⟩ := habs.matches_empty
  have hPT : near.covered ⊆ T := fun _ hv => (Finset.mem_sdiff.mp (near.inside hv)).1
  have hAP : Disjoint A near.covered := Finset.disjoint_left.mpr (by
    intro v hvA hvP
    exact (Finset.mem_sdiff.mp (near.inside hvP)).2 hvA)
  have hAS : Disjoint A (residual T A near.covered) :=
    (residual_disjoint_reserved T A near.covered).symm.mono
      Finset.subset_union_left (Finset.Subset.refl _)
  obtain ⟨MAS⟩ := habs _ near.nonzero
    (residual_balanced hT (matching_balanced MA) near.matching hAT hPT hAP)
    (residual_sum_eq_zero hsum (matching_sum_eq_zero MA) near.matching hAT hPT hAP)
    hAS near.deficit
  have hPS : Disjoint near.covered (A ∪ residual T A near.covered) := by
    apply Finset.disjoint_union_right.mpr
    refine ⟨hAP.symm, ?_⟩
    exact (residual_disjoint_reserved T A near.covered).symm.mono
      Finset.subset_union_right (Finset.Subset.refl _)
  have hcover : near.covered ∪ (A ∪ residual T A near.covered) = T := by
    calc
      _ = (A ∪ near.covered) ∪ residual T A near.covered := by ac_rfl
      _ = T := reserved_union_residual hAT hPT
  exact ⟨hcover ▸ unionMatching near.matching MAS hPS⟩


end
end EndpointMatching.AbsorptionAssembly
