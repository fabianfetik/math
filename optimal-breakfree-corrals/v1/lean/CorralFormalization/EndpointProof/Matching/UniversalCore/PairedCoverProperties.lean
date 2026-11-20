import CorralFormalization.EndpointProof.Matching.UniversalCore.PairedCoverInventory

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
noncomputable section
variable {G : Type*} [AddCommGroup G]

theorem FourThirdsPairedCover.added_balanced {Q : Vertex G → Prop}
    {S : Finset (Vertex G)} {U : Finset G} (C : FourThirdsPairedCover Q S U) :
    Balanced C.added := by
  intro p
  rw [C.part_card p, C.part_card 0]

theorem FourThirdsPairedCover.original_added_disjoint {Q : Vertex G → Prop}
    {S : Finset (Vertex G)} {U : Finset G} (C : FourThirdsPairedCover Q S U) :
    Disjoint S C.added := by
  apply Finset.disjoint_left.mpr
  intro v hvS hvA
  have hvSuppA : v.2 ∈ support C.added :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hvA,rfl⟩)
  have hvSuppS : v.2 ∈ support S :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hvS,rfl⟩)
  exact Finset.disjoint_left.mp C.avoids hvSuppA (Finset.mem_union_right _ hvSuppS)

theorem support_neg_mem {X : Finset (Vertex G)} {g : G} (hg : g ∈ support X) :
    -g ∈ support X := by
  simp only [support, Finset.mem_union, Finset.mem_image] at hg ⊢
  rcases hg with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
  · exact Or.inr ⟨v,hv,rfl⟩
  · exact Or.inl ⟨v,hv,by simp⟩

/-- The cover avoids the complete inverse closure of both the
forbidden set and the original residual's numerical coordinates. -/
theorem FourThirdsPairedCover.avoids_closure {Q : Vertex G → Prop}
    {S : Finset (Vertex G)} {U : Finset G} (C : FourThirdsPairedCover Q S U) :
    Disjoint (support C.added)
      ((U ∪ S.image Prod.snd) ∪ (U ∪ S.image Prod.snd).image Neg.neg) := by
  have hbase : Disjoint (support C.added) (U ∪ S.image Prod.snd) := by
    apply C.avoids.mono_right
    exact Finset.union_subset_union (Finset.Subset.refl _) Finset.subset_union_left
  apply Finset.disjoint_left.mpr
  intro g hg htarget
  rcases Finset.mem_union.mp htarget with h | h
  · exact Finset.disjoint_left.mp hbase hg h
  · obtain ⟨z,hz,hzg⟩ := Finset.mem_image.mp h
    have hng : -g ∈ support C.added := support_neg_mem hg
    have hz' : -g = z := by rw [← hzg,neg_neg]
    rw [hz'] at hng
    exact Finset.disjoint_left.mp hbase hng hz

theorem FourThirdsPairedCover.total_card {Q : Vertex G → Prop}
    {S : Finset (Vertex G)} {U : Finset G} (C : FourThirdsPairedCover Q S U) :
    C.added.card = 6 * C.pairsPerPart := by
  have hunion : Finset.univ.biUnion (slice C.added) = C.added := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, slice, Finset.mem_filter]
    constructor
    · rintro ⟨p,hv,_⟩
      exact hv
    · intro hv
      exact ⟨v.1,hv,rfl⟩
  have hd : (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (slice C.added) := by
    intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact hpq ((Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hw).2)
  calc
    C.added.card = (Finset.univ.biUnion (slice C.added)).card := by rw [hunion]
    _ = ∑ p : Fin 3, (slice C.added p).card := Finset.card_biUnion hd
    _ = ∑ _p : Fin 3, (2 * C.pairsPerPart) :=
      Finset.sum_congr rfl (fun p _ => C.part_card p)
    _ = 6 * C.pairsPerPart := by simp; omega

theorem FourThirdsPairedCover.added_card_le {Q : Vertex G → Prop}
    {S : Finset (Vertex G)} {U : Finset G} (C : FourThirdsPairedCover Q S U) :
    C.added.card ≤ 8 * S.card := by
  have hc := C.total_card
  have hm := C.pair_bound
  omega

theorem FourThirdsPairedCover.added_sum_zero [Fintype G] (hodd : Odd (Fintype.card G))
    {Q : Vertex G → Prop} {S : Finset (Vertex G)} {U : Finset G}
    (C : FourThirdsPairedCover Q S U) : (∑ v ∈ C.added, v.2) = 0 :=
  paired_coordinate_sum_zero hodd C.added C.added_paired

end
end EndpointMatching.UniversalCore
