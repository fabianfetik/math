import CorralFormalization.EndpointProof.Router.Installation.Tables

/-! # Exact arity of all used units in a matching layer -/
namespace EndpointRouter
open scoped BigOperators Classical
noncomputable section
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : Type v} [AddCommGroup G] [DecidableEq G]
namespace MatchingLayer

private def trackMap (L : MatchingLayer α) :
    Sum ({e : α × α // e ∈ L.edges} × Bool) {i : α // L.Isolated i} → α
  | .inl (e,b) => if b then e.1.2 else e.1.1
  | .inr i => i

private theorem trackMap_bijective (L : MatchingLayer α) : Function.Bijective L.trackMap := by
  constructor
  · intro a b hab
    rcases a with ⟨e,s⟩ | i <;> rcases b with ⟨d,t⟩ | j
    · have he : L.Incident (L.trackMap (.inl (e,s))) e := by cases s <;> simp [trackMap,Incident]
      have hd : L.Incident (L.trackMap (.inl (d,t))) d := by cases t <;> simp [trackMap,Incident]
      have hed : e.1 = d.1 := L.incident_unique _ _ e.property _ d.property he (hab ▸ hd)
      have hed' : e = d := Subtype.ext hed
      subst d
      have hst : s = t := by
        cases s <;> cases t
        · rfl
        · exact False.elim ((L.no_loop e e.property) hab)
        · exact False.elim ((L.no_loop e e.property) hab.symm)
        · rfl
      simp [hst]
    · exfalso
      apply j.property
      refine ⟨e,e.property,?_⟩
      cases s
      · exact Or.inl hab.symm
      · exact Or.inr hab.symm
    · exfalso
      apply i.property
      refine ⟨d,d.property,?_⟩
      cases t
      · exact Or.inl hab
      · exact Or.inr hab
    · exact congrArg Sum.inr (Subtype.ext hab)
  · intro i
    by_cases hi : L.Isolated i
    · exact ⟨.inr ⟨i,hi⟩,rfl⟩
    · obtain ⟨e,he,hie⟩ : ∃ e ∈ L.edges, L.Incident i e := not_not.mp hi
      rcases hie with rfl | rfl
      · exact ⟨.inl (⟨e,he⟩,false),rfl⟩
      · exact ⟨.inl (⟨e,he⟩,true),rfl⟩

/-- Each track belongs to exactly one switch endpoint or one idle unit. -/
theorem unit_arity_sum (L : MatchingLayer α) (input output : α → G) :
    ∑ u : L.Unit, (L.unitQuery input output u).arity = Fintype.card α := by
  have hc := Fintype.card_congr (Equiv.ofBijective L.trackMap L.trackMap_bijective)
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool] at hc
  simpa [Unit,unitQuery,Query.arity,Fintype.sum_sum_type,Nat.mul_comm] using hc

/-- Eighteen numerical random requests for each track across two layers. -/
theorem twoLayer_weight_sum {n : ℕ} (L₁ L₂ : MatchingLayer (Fin n))
    (input intermediate output : Fin n → G) :
    (∑ u : Sum L₁.Unit L₂.Unit, 9 * (Sum.elim (L₁.unitQuery input intermediate)
      (L₂.unitQuery intermediate output) u).arity) = 18*n := by
  rw [← Finset.mul_sum]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,L₁.unit_arity_sum,L₂.unit_arity_sum,Fintype.card_fin]
  omega

end MatchingLayer
end
end EndpointRouter
