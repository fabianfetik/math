import CorralFormalization.EndpointProof.Flow.Cover.Supplier
import CorralFormalization.EndpointProof.Flow.Cover.Parity

/-! Inventory and inverse-support facts used by the paired cover construction iteration. -/

open scoped Classical BigOperators

namespace EndpointFlow.Cover

open EndpointSelector EndpointSelector.Assembly

noncomputable section

set_option maxHeartbeats 1500000

variable {G : Type*} [CommRing G] [Fintype G]

theorem balanced_empty : Balanced (∅ : Finset (Vertex G)) := by simp [Balanced,partSlice]

theorem balanced_union {A B : Finset (Vertex G)}
    (ha : Balanced A) (hb : Balanced B) (hd : Disjoint A B) : Balanced (A ∪ B) := by
  intro p
  have hslice (p : Fin 3) : partSlice (A ∪ B) p = partSlice A p ∪ partSlice B p := by
    simp [partSlice,Finset.filter_union]
  have hdis (p : Fin 3) : Disjoint (partSlice A p) (partSlice B p) :=
    hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [hslice p,hslice 0,Finset.card_union_of_disjoint (hdis p),
    Finset.card_union_of_disjoint (hdis 0),ha p,hb p]

/-- Pairing pays the inverse closure by the occupied vertices themselves. -/
theorem numericalSupport_paired (T : Finset (Vertex G))
    (hp : ∀ v ∈ T, (v.1,-v.2) ∈ T) : numericalSupport T = T.image Prod.snd := by
  apply Finset.union_eq_left.mpr
  intro x hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨(v.1,-v.2),hp v hv,rfl⟩

theorem numericalSupport_paired_card_le (T : Finset (Vertex G))
    (hp : ∀ v ∈ T, (v.1,-v.2) ∈ T) : (numericalSupport T).card ≤ T.card := by
  rw [numericalSupport_paired T hp]
  exact Finset.card_image_le

def numericalClosure (F : Finset G) : Finset G := F ∪ F.image Neg.neg

def initialForbidden (U : Finset G) (S : Finset (Vertex G)) : Finset G :=
  numericalClosure U ∪ numericalSupport S

theorem initialForbidden_card_le (U : Finset G) (S : Finset (Vertex G)) :
    (initialForbidden U S).card ≤ 2*U.card+2*S.card := by
  have hU : (numericalClosure U).card ≤ 2*U.card := by
    have hi := Finset.card_image_le (s := U) (f := Neg.neg)
    have hu := Finset.card_union_le U (U.image Neg.neg)
    change (U ∪ U.image Neg.neg).card ≤ _
    omega
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hU (numericalSupport_card_le S))

theorem initialForbidden_eq (U : Finset G) (S : Finset (Vertex G)) :
    initialForbidden U S = numericalClosure (U ∪ S.image Prod.snd) := by
  ext x
  simp only [initialForbidden,numericalClosure,numericalSupport,Finset.image_union,
    Finset.image_image,Function.comp_def,Finset.mem_union]
  tauto

end
end EndpointFlow.Cover
