import CorralFormalization.EndpointProof.Selector.Assembly.ManySelectors
import CorralFormalization.EndpointProof.Selector.Stars.Helpers

/-!
Actual nonzero inverse pairs in one fixed tagged part, and the helper-pair
supplier obtained from the all-rotations one-arm star on the same ω.
-/

open scoped Classical

namespace EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

def pair (p : Fin 3) (a : G) : Finset (Vertex G) := {(p,a),(p,-a)}

def LegalPair (p : Fin 3) (T : Finset (Vertex G)) : Prop :=
  ∃ a : G, a ≠ 0 ∧ T = pair p a

theorem legalPair_rootDomain (p : Fin 3) : RootDomain (LegalPair (G := G) p) := by
  constructor
  · intro T hT
    obtain ⟨a,ha,rfl⟩ := hT
    exact ⟨(p,a),by simp [pair]⟩
  · intro T hT
    obtain ⟨a,ha,rfl⟩ := hT
    exact Finset.card_le_two

@[simp] theorem numericalSupport_pair (p : Fin 3) (a : G) :
    numericalSupport (pair p a) = {a,-a} := by
  ext x
  simp [numericalSupport,pair]
  tauto

theorem helperSupply_of_rotated_star_available
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : EndpointFullProduct.FullAvailable
      (Stars.rotatedStarQueryEmbedding (k := 1) (by omega) hodd hn)
      (fun r _ ↦ Stars.rotatedStarDemand r.1) budget ω) (p : Fin 3) :
    HelperSupply (PVertex ω) (LegalPair p) budget := by
  intro F hF
  obtain ⟨u,hu,hd,hp,hnp⟩ :=
    Stars.exists_P_pair_of_rotated_star_available hodd hn budget ω hgood p F hF
  refine ⟨pair p u,⟨u,hu,rfl⟩,?_,by simpa using hd⟩
  intro v hv
  simp only [pair,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact hp
  · exact hnp

theorem pair_eq_target (a : G) : pair (0 : Fin 3) a = target a := rfl

theorem rotate_pair (σ : Equiv.Perm (Fin 3)) (p : Fin 3) (a : G) :
    rotate σ (pair p a) = pair (σ p) a := by
  simp [rotate,pair,tagEquiv]

theorem pair_ne_of_rootCondition (p : Fin 3) {a b : G} (h : RootCondition a b) :
    pair p a ≠ pair p b := by
  intro he
  have ha : (p,a) ∈ pair p b := he ▸ (by simp [pair])
  simp only [pair,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,true_and] at ha
  exact ha.elim h.2.2.1 h.2.2.2

theorem rootCondition_of_pair_ne (p : Fin 3) {a b : G}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : pair p a ≠ pair p b) : RootCondition a b := by
  refine ⟨ha,hb,?_,?_⟩
  · intro he
    exact h (congrArg (pair p) he)
  · intro he
    apply h
    simp [pair,he,Finset.pair_comm]

/-- A finite family of distinct legal inverse pairs has actual nonzero
representatives satisfying exactly the star root hypotheses. -/
theorem exists_root_enumeration (p : Fin 3) (R : Finset (Finset (Vertex G)))
    (hlegal : ∀ T ∈ R, LegalPair p T) :
    ∃ a : Fin R.card → G, Stars.StarRoots a ∧
      Finset.univ.image (fun i ↦ pair p (a i)) = R := by
  let e : R ≃ Fin R.card := Fintype.equivFinOfCardEq (by simp)
  let T : Fin R.card → Finset (Vertex G) := fun i ↦ (e.symm i).val
  have hT (i : Fin R.card) : T i ∈ R := (e.symm i).property
  have hinj : Function.Injective T := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  choose a ha hp using (fun i ↦ hlegal (T i) (hT i))
  refine ⟨a,⟨ha,?_⟩,?_⟩
  · intro i j hij
    have hpair : pair p (a i) ≠ pair p (a j) := by
      intro he
      apply hij
      apply hinj
      exact (hp i).trans (he.trans (hp j).symm)
    exact (rootCondition_of_pair_ne p (ha i) (ha j) hpair).2.2
  · ext U
    constructor
    · intro hU
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hU
      simpa only [← hp i] using hT i
    · intro hU
      refine Finset.mem_image.mpr ⟨e ⟨U,hU⟩,Finset.mem_univ _,?_⟩
      have hTU : T (e ⟨U,hU⟩) = U := by simp [T]
      exact (hp _).symm.trans hTU

end
end EndpointSelector.Assembly
