import CorralFormalization.EndpointProof.Selector.Assembly.Matchings
import CorralFormalization.EndpointProof.Selector.SwitchAvailability

/-!
The concrete switch at every tag permutation, with actual permuted P demands.
These are demands on one unchanged full sample, not a separately rotated or
resampled source. A common availability event must quantify these queries.
-/

open scoped Classical NNReal

namespace EndpointSelector.Assembly

open EndpointBlockAvailability EndpointOriginalReservoir EndpointSharedSample

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

def rotatedSwitchDemand (σ : Equiv.Perm (Fin 3)) (j : Fin 4) : Label :=
  EndpointReservoirAvailability.encodeChild (some (σ (switchPart j),false))

theorem labelWeights_P (p τ : ℝ≥0) (part : Fin 3) :
    labelWeights p τ (EndpointReservoirAvailability.encodeChild (some (part,false))) = p := by
  fin_cases part <;> rfl

theorem rotatedSwitchDemand_probability (σ : Equiv.Perm (Fin 3)) (p τ : ℝ≥0) :
    successProbability p τ (rotatedSwitchDemand σ) = (p : ℝ)^4 := by
  simp [successProbability,rotatedSwitchDemand,labelWeights_P]

theorem rotated_candidate_interior_P {a b : G} {M : ℕ}
    (P : PackedSwitches a b M) (hodd : Odd (Fintype.card G))
    (σ : Equiv.Perm (Fin 3)) (ω : EndpointFullProduct.FullSample G) (i : Fin M)
    (hsuccess : ∀ j, EndpointFullProduct.fullLabels ω (P.orbitEmbedding hodd (i,j)) =
      rotatedSwitchDemand σ j) :
    ∀ v ∈ rotate σ (interior a b (P.parameter i)), PVertex ω v := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  rw [interior_image] at hw
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
  have hc : childLabel ((EndpointFullProduct.regroup ω).1 (P.orbitEmbedding hodd (i,j))) =
      some (σ (switchPart j),false) := by
    apply EndpointReservoirAvailability.encodeChild_bijective.injective
    exact hsuccess j
  exact ⟨P.orbitEmbedding hodd (i,j),
    (locate hodd (representative a b (P.parameter i) j) ((P.valid i).1 j)).2,
    locate_spec hodd (representative a b (P.parameter i) j) ((P.valid i).1 j),hc⟩

theorem rotated_switch_of_fullAvailable
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (σ : Equiv.Perm (Fin 3)) (ω : EndpointFullProduct.FullSample G)
    (hgood : EndpointFullProduct.FullAvailable (queryEmbedding hodd hn)
      (fun _ _ ↦ rotatedSwitchDemand σ) budget ω)
    (r : RootQuery G) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ u : G,
      Valid r.val.1 r.val.2 u ∧
      Disjoint (orbitSupport r.val.1 r.val.2 u) F ∧
      (∀ v ∈ rotate σ (interior r.val.1 r.val.2 u), PVertex ω v) ∧
      (rotate σ (interior r.val.1 r.val.2 u)).card = 4 ∧
      Nonempty (MatchingOn (rotate σ (interior r.val.1 r.val.2 u) ∪
        rotate σ (target r.val.1))) ∧
      Nonempty (MatchingOn (rotate σ (interior r.val.1 r.val.2 u) ∪
        rotate σ (target r.val.2))) := by
  obtain ⟨i,hi,hd⟩ := hgood r F hF
  let P := linearOrbitPacking hodd hn r
  have hv := P.valid i
  have hm := two_pair_switch r.val.1 r.val.2 (P.parameter i) r.property hodd hv
  change Disjoint (support (P.orbitEmbedding hodd) orbitPlace i) F at hd
  rw [P.support_eq hodd i] at hd
  refine ⟨P.parameter i,hv,hd,?_,by simpa using hm.1,?_,?_⟩
  · exact rotated_candidate_interior_P P hodd σ ω i (fun j ↦ congrFun hi j)
  · exact ⟨by simpa using (MatchingOn.two hm.2.2.2.1).rotated σ⟩
  · exact ⟨by simpa using (MatchingOn.two hm.2.2.2.2).rotated σ⟩

/-- One full sample, with all tag permutations before the root and forbidden
set queries. This predicate is stronger than the old A-only switch event. -/
def AllRotatedSwitches (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3), EndpointFullProduct.FullAvailable (queryEmbedding hodd hn)
    (fun _ _ ↦ rotatedSwitchDemand σ) budget ω

def rotatedQueryEmbedding (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (r : Equiv.Perm (Fin 3) × RootQuery G) :
    Fin (Fintype.card G / 1000) × Fin 4 ↪ EndpointOriginalReservoir.OddOrbit G :=
  queryEmbedding hodd hn r.2

theorem fullAvailable_rotated_iff (hodd : Odd (Fintype.card G))
    (hn : 1000 ≤ Fintype.card G) (budget : ℕ) (ω : EndpointFullProduct.FullSample G) :
    EndpointFullProduct.FullAvailable (rotatedQueryEmbedding hodd hn)
      (fun r _ ↦ rotatedSwitchDemand r.1) budget ω ↔
      AllRotatedSwitches hodd hn budget ω := by
  constructor
  · intro h σ r F hF
    exact h (σ,r) F hF
  · intro h r F hF
    exact h r.1 r.2 F hF

/-- This concrete finite event includes every legal tag rotation before all
root and forbidden-set queries. All its candidates use the original ω. -/
theorem full_sample_rotated_switch_budget
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η α β : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α+β ≤ 1) (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*α) (hQ : (τ : ℝ) = rho q η*β) :
    (EndpointFullProduct.fullMeasure q η α β hq0 hq1 hη0 hη1 hα hβ hαβ).real
      {ω : EndpointFullProduct.FullSample G |
        ¬ AllRotatedSwitches hodd (by omega)
          (CorralFormalization.EndpointProof.RateBudget.selectorBudget p (Fintype.card G)) ω} ≤
      (6*(Fintype.card G : ℝ)^2) *
        Real.exp (-((p : ℝ)^8 / 32000) * (Fintype.card G : ℝ)) := by
  have hh := EndpointFullProduct.full_sample_four_orbit_budget hodd hn
    q η α β hq0 hq1 hη0 hη1 hα hβ hαβ p τ hp h hP hQ
    (rotatedQueryEmbedding hodd (by omega))
    (fun r _ ↦ rotatedSwitchDemand r.1)
    (by simp) (fun r _ ↦ (rotatedSwitchDemand_probability r.1 p τ).ge)
  have hcard : (Fintype.card (Equiv.Perm (Fin 3) × RootQuery G) : ℝ) ≤
      6*(Fintype.card G : ℝ)^2 := by
    have hc : (Fintype.card (RootQuery G) : ℝ) ≤ (Fintype.card G : ℝ)^2 := by
      exact_mod_cast (rootQuery_card_le (G := G))
    norm_num only [Fintype.card_prod,Fintype.card_perm,Fintype.card_fin,
      Nat.factorial, Nat.cast_mul,Nat.cast_ofNat, Nat.cast_one,mul_one,Nat.cast_succ]
    exact
      mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 6)
  have hh' := hh.trans (mul_le_mul_of_nonneg_right hcard (le_of_lt (Real.exp_pos _)))
  simpa only [fullAvailable_rotated_iff] using hh'

end
end EndpointSelector.Assembly
