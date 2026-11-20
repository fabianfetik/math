import CorralFormalization.EndpointProof.Flow.Cover.Partial

/-!
The output-sum and final-edge invariants of an open paired cover.

The results hold for actual finite matchings and supplied paired reservoir
sets. They do not supply or iterate any six-root flows.
-/

open scoped Classical BigOperators

namespace EndpointFlow.Cover

open EndpointSelector EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- Every actual matching of zero-sum hyperedges has total coordinate sum 0. -/
theorem matching_coordinate_sum_zero {S : Finset (Vertex G)} (M : MatchingOn S) :
    ∑ v ∈ S, v.2 = 0 := by
  rw [← M.cover]
  change (∑ v ∈ M.edges.biUnion (fun E ↦ E), v.2) = 0
  rw [Finset.sum_biUnion M.disjoint]
  apply Finset.sum_eq_zero
  intro E hE
  obtain ⟨a,b,c,hzero,rfl⟩ := M.valid E hE
  simpa [edge,add_assoc] using hzero

/-- A nonzero inverse-paired augmentation in an odd-order group has sum 0. -/
theorem paired_coordinate_sum_zero (hodd : Odd (Fintype.card G))
    (T : Finset (Vertex G))
    (hpair : ∀ v ∈ T, (v.1,-v.2) ∈ T) : ∑ v ∈ T, v.2 = 0 := by
  exact Finset.sum_involution (fun v _ ↦ (v.1,-v.2))
    (fun v _ ↦ by simp)
    (fun v _ hne heq ↦ (ne_neg_of_odd hodd hne) (congrArg Prod.snd heq).symm)
    hpair (fun v _ ↦ by simp)

/-- In an actual partial cover, the output sum equals the original sum.
It follows from matching and pairing and need not be assumed at every merge. -/
theorem PartialCover.output_coordinate_sum (hodd : Odd (Fintype.card G))
    {Q : Vertex G → Prop} {S : Finset (Vertex G)} (P : PartialCover Q S) :
    (∑ v ∈ P.output, v.2) = ∑ v ∈ S, v.2 := by
  have hmatch := matching_coordinate_sum_zero P.matching
  have hadded := paired_coordinate_sum_zero hodd P.added P.added_paired
  have hsplit := Finset.sum_sdiff (f := fun v : Vertex G ↦ v.2) P.output_subset
  have hunion := Finset.sum_union (f := fun v : Vertex G ↦ v.2) P.original_added_disjoint
  rw [hmatch,zero_add] at hsplit
  rw [hadded,add_zero] at hunion
  exact hsplit.trans hunion

/-- Exactly one tagged coordinate in each of the three parts. -/
def OnePerPart (S : Finset (Vertex G)) : Prop :=
  ∀ part : Fin 3, ∃! x : G, (part,x) ∈ S

/-- A one-per-part set of total coordinate sum 0 is an actual hyperedge. -/
theorem onePerPart_zero_hyperedge {S : Finset (Vertex G)}
    (hone : OnePerPart S) (hsum : ∑ v ∈ S, v.2 = 0) : IsHyperedge S := by
  choose f hf huniq using hone
  have hinj : Function.Injective (fun i : Fin 3 ↦ (i,f i)) := by
    intro i j h
    exact congrArg Prod.fst h
  have hset : S = Finset.univ.image (fun i : Fin 3 ↦ (i,f i)) := by
    ext ⟨i,x⟩
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · intro hx
      refine ⟨i,?_⟩
      simp [huniq i x hx]
    · rintro ⟨j,hj⟩
      have hji : j = i := congrArg Prod.fst hj
      subst j
      have hfx : f i = x := congrArg Prod.snd hj
      simpa only [← hfx] using hf i
  have heq : S = edge (f 0) (f 1) (f 2) := by
    rw [hset,edge_eq_image]
    congr 1
    funext i
    fin_cases i <;> rfl
  refine ⟨f 0,f 1,f 2,?_,heq⟩
  rw [hset,Finset.sum_image] at hsum
  · simpa [Fin.sum_univ_succ,add_assoc] using hsum
  · intro x hx y hy he
    exact hinj he

/-- For a zero-sum original set, a one-per-part output closes into the
actual perfect matching carried by the partial cover. -/
def PartialCover.close_of_zero_sum (hodd : Odd (Fintype.card G))
    {Q : Vertex G → Prop} {S : Finset (Vertex G)} (P : PartialCover Q S)
    (hsum : ∑ v ∈ S, v.2 = 0) (hone : OnePerPart P.output) :
    MatchingOn (S ∪ P.added) := by
  apply P.close
  apply onePerPart_zero_hyperedge hone
  rw [P.output_coordinate_sum hodd,hsum]

end
end EndpointFlow.Cover
