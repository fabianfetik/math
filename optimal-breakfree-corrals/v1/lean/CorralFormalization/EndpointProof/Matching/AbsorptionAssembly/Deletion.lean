import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.FiniteAssembly

open scoped Classical BigOperators
namespace EndpointMatching.Deletion
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- Delete every matching edge meeting F.  The original uncovered vertices,
plus at most k-1 vertices per newly touched edge, bound the new deficit. -/
theorem residual_card_le (R F : Finset α) (edges : Finset (Finset α)) (k : ℕ)
    (hdis : (↑edges : Set (Finset α)).PairwiseDisjoint id)
    (hsize : ∀ e ∈ edges, e.card ≤ k) :
    ((R \ F) \ ((edges.filter (fun e => Disjoint e F)).biUnion id)).card ≤
      (R \ edges.biUnion id).card + (k - 1) * F.card := by
  classical
  let bad := edges.filter (fun e => ¬ Disjoint e F)
  have hbad_mem {e : Finset α} (he : e ∈ bad) : e ∈ edges ∧ ¬ Disjoint e F := by
    simpa [bad] using he
  have hint_nonempty {e : Finset α} (he : e ∈ bad) : (e ∩ F).Nonempty := by
    obtain ⟨x, hxe, hxF⟩ := Finset.not_disjoint_iff.mp (hbad_mem he).2
    exact ⟨x, Finset.mem_inter.mpr ⟨hxe, hxF⟩⟩
  have hint_dis :
      (↑bad : Set (Finset α)).PairwiseDisjoint (fun e => e ∩ F) := by
    intro e he e' he' hne
    exact (hdis (hbad_mem he).1 (hbad_mem he').1 hne).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hbad_card : bad.card ≤ F.card := by
    calc
      bad.card = ∑ _e ∈ bad, (1 : ℕ) := by simp
      _ ≤ ∑ e ∈ bad, (e ∩ F).card := by
        apply Finset.sum_le_sum
        intro e he
        exact Finset.one_le_card.mpr (hint_nonempty he)
      _ = (bad.biUnion (fun e => e ∩ F)).card := (Finset.card_biUnion hint_dis).symm
      _ ≤ F.card := Finset.card_le_card (by
        intro x hx
        obtain ⟨e, _, hx⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_inter.mp hx).2)
  have hedge_bound : ∀ e ∈ bad, (e \ F).card ≤ k - 1 := by
    intro e he
    obtain ⟨x, hx⟩ := hint_nonempty he
    have hss : e \ F ⊂ e := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro heq
      have : x ∈ e \ F := heq.symm ▸ (Finset.mem_inter.mp hx).1
      exact (Finset.mem_sdiff.mp this).2 (Finset.mem_inter.mp hx).2
    have hlt := Finset.card_lt_card hss
    have hs := hsize e (hbad_mem he).1
    omega
  have hsubset :
      (R \ F) \ ((edges.filter (fun e => Disjoint e F)).biUnion id) ⊆
        (R \ edges.biUnion id) ∪ bad.biUnion (fun e => e \ F) := by
    intro x hx
    have hxR : x ∈ R := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
    have hxF : x ∉ F := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2
    have hxgood := (Finset.mem_sdiff.mp hx).2
    by_cases hcover : x ∈ edges.biUnion id
    · obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hcover
      have hbad : ¬ Disjoint e F := by
        intro hd
        apply hxgood
        exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hd⟩, hxe⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨e, Finset.mem_filter.mpr ⟨he, hbad⟩, Finset.mem_sdiff.mpr ⟨hxe, hxF⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxR, hcover⟩)
  have hb : (bad.biUnion (fun e => e \ F)).card ≤ (k - 1) * bad.card := by
    calc
      _ ≤ ∑ e ∈ bad, (e \ F).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ bad, (k - 1) := Finset.sum_le_sum hedge_bound
      _ = (k - 1) * bad.card := by simp [Nat.mul_comm]
  calc
    _ ≤ ((R \ edges.biUnion id) ∪ bad.biUnion (fun e => e \ F)).card :=
      Finset.card_le_card hsubset
    _ ≤ (R \ edges.biUnion id).card + (bad.biUnion (fun e => e \ F)).card :=
      Finset.card_union_le _ _
    _ ≤ (R \ edges.biUnion id).card + (k - 1) * F.card := by
      have := Nat.mul_le_mul_left (k - 1) hbad_card
      omega
end
end EndpointMatching.Deletion

namespace EndpointMatching.AbsorptionAssembly
open EndpointFlow.AbelianTransport
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- The vertices still covered after discarding edges that meet the forbidden set. -/
def survivingVertices {T : Finset (Vertex G)} (M : Matching T)
    (F : Finset (Vertex G)) : Finset (Vertex G) :=
  (M.edges.filter (fun e => Disjoint e F)).biUnion id

/-- The remaining edges retain their original zero-sum matching structure. -/
def survivingMatching {T : Finset (Vertex G)} (M : Matching T)
    (F : Finset (Vertex G)) : Matching (survivingVertices M F) where
  edges := M.edges.filter (fun e => Disjoint e F)
  valid := by
    intro e he
    exact M.valid e (Finset.mem_filter.mp he).1
  disjoint := by
    intro e he e' he' hne
    exact M.disjoint (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he').1 hne
  cover := rfl

theorem hyperedge_card_eq_three {E : Finset (Vertex G)} (hE : Hyperedge E) :
    E.card = 3 := by
  obtain ⟨x, y, z, _, rfl⟩ := hE
  simp

/-- A three-part matching loses at most two additional vertices for each
forbidden vertex. The original unmatched inventory is retained in the bound. -/
theorem surviving_deficit_le {T : Finset (Vertex G)} (M : Matching T)
    (R F : Finset (Vertex G)) :
    ((R \ F) \ survivingVertices M F).card ≤
      (R \ T).card + 2 * F.card := by
  have hs : ∀ e ∈ M.edges, e.card ≤ 3 := by
    intro e he
    exact (hyperedge_card_eq_three (M.valid e he)).le
  have h := EndpointMatching.Deletion.residual_card_le R F M.edges 3 M.disjoint hs
  simpa only [survivingVertices, M.cover, Nat.reduceSub] using h

/-- If the original matching is inside R, its edges that avoid R \ W
really are edges on W. No new or padded vertices are introduced. -/
theorem survivingVertices_subset {T : Finset (Vertex G)} (M : Matching T)
    {R W : Finset (Vertex G)} (hTR : T ⊆ R) :
    survivingVertices M (R \ W) ⊆ W := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  have he' := Finset.mem_filter.mp he
  have hxT : x ∈ T := by
    rw [← M.cover]
    exact Finset.mem_biUnion.mpr ⟨e, he'.1, hxe⟩
  by_contra hxW
  exact Finset.disjoint_left.mp he'.2 hxe (Finset.mem_sdiff.mpr ⟨hTR hxT, hxW⟩)

/-- The bound on an arbitrary actual subinventory W of R. -/
theorem surviving_subinventory_deficit_le {T : Finset (Vertex G)} (M : Matching T)
    {R W : Finset (Vertex G)} (hWR : W ⊆ R) :
    (W \ survivingVertices M (R \ W)).card ≤
      (R \ T).card + 2 * (R \ W).card := by
  have hset : R \ (R \ W) = W := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · intro ⟨hxR, hx⟩
      by_contra hxW
      exact hx ⟨hxR, hxW⟩
    · intro hxW
      exact ⟨hWR hxW, fun hx => hx.2 hxW⟩
  have h := surviving_deficit_le M R (R \ W)
  simpa only [hset] using h

end
end EndpointMatching.AbsorptionAssembly

namespace EndpointMatching.Deletion

/-- One triple and one deleted vertex attain the coefficient two. -/
theorem coefficient_two_sharp :
    let R : Finset (Fin 3) := {0, 1, 2}
    let F : Finset (Fin 3) := {0}
    let edges : Finset (Finset (Fin 3)) := {R}
    ((R \ F) \ ((edges.filter (fun e => Disjoint e F)).biUnion id)).card =
      (R \ edges.biUnion id).card + 2 * F.card := by
  decide

end EndpointMatching.Deletion
