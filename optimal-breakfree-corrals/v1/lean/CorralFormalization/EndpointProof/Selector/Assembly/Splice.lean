import CorralFormalization.EndpointProof.Selector.Assembly.Matchings

/-!
Exact finite selector splicing. Each splice consumes one common reservoir
pair. The constructor builds all alternative matchings on one fixed interior.
The construction bound counts modules, not sampled orbits.
-/

open scoped Classical

namespace EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [DecidableEq G]

/-- Every target receives its own actual matching on the same fixed interior. -/
structure SelectorOn (P : Vertex G → Prop) (R : Finset (Finset (Vertex G))) where
  interior : Finset (Vertex G)
  inside : ∀ v ∈ interior, P v
  fresh : ∀ T ∈ R, Disjoint interior T
  matching : ∀ T ∈ R, Nonempty (MatchingOn (interior ∪ T))

/-- Precise freshness requirements when one reservoir pair H is internalised. -/
structure SpliceCompatible {P : Vertex G → Prop} {A B : Finset (Finset (Vertex G))}
    {H : Finset (Vertex G)} (L : SelectorOn P (insert H A))
    (R : SelectorOn P (insert H B)) : Prop where
  interiors : Disjoint L.interior R.interior
  left_external : ∀ T ∈ B, Disjoint L.interior T
  right_external : ∀ T ∈ A, Disjoint R.interior T
  helper_external : ∀ T ∈ A ∪ B, Disjoint H T
  helper_inside : ∀ v ∈ H, P v

def splice {P : Vertex G → Prop} {A B : Finset (Finset (Vertex G))}
    {H : Finset (Vertex G)} (L : SelectorOn P (insert H A))
    (R : SelectorOn P (insert H B)) (C : SpliceCompatible L R) :
    SelectorOn P (A ∪ B) where
  interior := L.interior ∪ R.interior ∪ H
  inside := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact L.inside v hv
      · exact R.inside v hv
    · exact C.helper_inside v hv
  fresh := by
    intro T hT
    apply Finset.disjoint_union_left.mpr
    refine ⟨Finset.disjoint_union_left.mpr ⟨?_,?_⟩,C.helper_external T hT⟩
    · rcases Finset.mem_union.mp hT with hT | hT
      · exact L.fresh T (Finset.mem_insert_of_mem hT)
      · exact C.left_external T hT
    · rcases Finset.mem_union.mp hT with hT | hT
      · exact C.right_external T hT
      · exact R.fresh T (Finset.mem_insert_of_mem hT)
  matching := by
    intro T hT
    by_cases hTA : T ∈ A
    · obtain ⟨mL⟩ := L.matching T (Finset.mem_insert_of_mem hTA)
      obtain ⟨mR⟩ := R.matching H (Finset.mem_insert_self _ _)
      have hd : Disjoint (L.interior ∪ T) (R.interior ∪ H) := by
        simp only [Finset.disjoint_union_left,Finset.disjoint_union_right]
        exact ⟨⟨C.interiors,(C.right_external T hTA).symm⟩,
          ⟨L.fresh H (Finset.mem_insert_self _ _),(C.helper_external T hT).symm⟩⟩
      exact ⟨by simpa only [Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
        using mL.union mR hd⟩
    · have hTB : T ∈ B := (Finset.mem_union.mp hT).resolve_left hTA
      obtain ⟨mL⟩ := L.matching H (Finset.mem_insert_self _ _)
      obtain ⟨mR⟩ := R.matching T (Finset.mem_insert_of_mem hTB)
      have hd : Disjoint (L.interior ∪ H) (R.interior ∪ T) := by
        simp only [Finset.disjoint_union_left,Finset.disjoint_union_right]
        exact ⟨⟨C.interiors,(R.fresh H (Finset.mem_insert_self _ _)).symm⟩,
          ⟨C.left_external T hTB,C.helper_external T hT⟩⟩
      exact ⟨by simpa only [Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
        using mL.union mR hd⟩

theorem splice_card_le {P : Vertex G → Prop} {A B : Finset (Finset (Vertex G))}
    {H : Finset (Vertex G)} (L : SelectorOn P (insert H A))
    (R : SelectorOn P (insert H B)) (C : SpliceCompatible L R) :
    (splice L R C).interior.card ≤ L.interior.card + R.interior.card + H.card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)

/-- A finite, compositional certificate for a selector built out of small
modules. Every constructor records genuine matchings, not just cardinalities. -/
inductive Built (P : Vertex G → Prop) :
    {R : Finset (Finset (Vertex G))} → SelectorOn P R → ℕ → Prop
  | small {R} (S : SelectorOn P R) (hcard : S.interior.card ≤ 16) : Built P S 1
  | join {A B H} (L : SelectorOn P (insert H A)) (R : SelectorOn P (insert H B))
      (C : SpliceCompatible L R) (hH : H.card ≤ 2)
      {k l : ℕ} (left : Built P L k) (right : Built P R l) :
      Built P (splice L R C) (k+l)

theorem Built.paid_bound {P : Vertex G → Prop} {R : Finset (Finset (Vertex G))}
    {S : SelectorOn P R} {k : ℕ} (h : Built P S k) :
    1 ≤ k ∧ S.interior.card + 2 ≤ 18*k := by
  induction h with
  | small S hcard => omega
  | join L R C hH hL hR ihL ihR =>
    have hc := splice_card_le L R C
    constructor <;> omega

/-- coloured selector construction's exact `18k-2` bound applies to every actual construction with at
most k small modules; no probability is raised to the size of this interior. -/
theorem Built.selector_cardinality_bound {P : Vertex G → Prop} {R : Finset (Finset (Vertex G))}
    {S : SelectorOn P R} {m k : ℕ} (h : Built P S m) (hm : m ≤ k) :
    S.interior.card ≤ 18*k-2 := by
  have hp := h.paid_bound
  omega

theorem Built.support_bound {P : Vertex G → Prop} {R : Finset (Finset (Vertex G))}
    {S : SelectorOn P R} {m k : ℕ} (h : Built P S m)
    (hm : m ≤ k) (hk : k ≤ 100) (hR : R.card ≤ k)
    (hpair : ∀ T ∈ R, T.card ≤ 2) :
    (numericalSupport (S.interior ∪ R.biUnion id)).card ≤ 3996 := by
  have hI : S.interior.card ≤ 1798 := by
    have hb := h.selector_cardinality_bound hm
    omega
  apply support_bound_3996 _ _ hI
  calc
    (R.biUnion id).card ≤ ∑ T ∈ R, T.card := Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ R, 2 := Finset.sum_le_sum hpair
    _ ≤ 200 := by simp; omega

end
end EndpointSelector.Assembly
