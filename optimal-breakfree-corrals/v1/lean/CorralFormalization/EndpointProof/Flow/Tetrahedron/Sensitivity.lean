import CorralFormalization.EndpointProof.Flow.Tetrahedron.DeletionAndCounts
open scoped Classical BigOperators
namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
open EndpointFullProduct EndpointOriginalReservoir
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

def sectionCoordinates (i : Fin 6) (t : TetrahedronParameters G) : G × G :=
  ![(t.2.1,t.2.2),(t.1,t.2.2),(t.1,t.2.1),
    (t.1,t.2.2),(t.1,t.2.1),(t.1,t.2.1)] i

theorem sectionCoordinates_injective (i : Fin 6) (g : G) :
    Set.InjOn (sectionCoordinates i)
      (↑(Finset.univ.filter (fun t : TetrahedronParameters G => tetrahedronDirection i t = g)) :
        Set (TetrahedronParameters G)) := by
  intro t ht u hu he
  have ht' := (Finset.mem_filter.mp ht).2
  have hu' := (Finset.mem_filter.mp hu).2
  rcases t with ⟨a,b,c⟩
  rcases u with ⟨d,e,f⟩
  fin_cases i <;> simp [tetrahedronDirection, sectionCoordinates] at ht' hu' he
  all_goals rcases he with ⟨he₁,he₂⟩
  all_goals apply Prod.ext
  all_goals simp_all
  all_goals have h := ht'.trans hu'.symm
  all_goals first | exact add_left_cancel h | (simp only [sub_eq_add_neg] at h; exact neg_injective (add_left_cancel h))

theorem direction_section_card_le (i : Fin 6) (g : G) :
    (Finset.univ.filter (fun t : TetrahedronParameters G => tetrahedronDirection i t = g)).card ≤
      (Fintype.card G)^2 := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter
    (fun t : TetrahedronParameters G => tetrahedronDirection i t = g))
    (t := (Finset.univ : Finset (G × G))) (sectionCoordinates i)
    (by intro t ht; simp) (sectionCoordinates_injective i g)
  simpa [Fintype.card_prod, pow_two] using h

/-- Each affine representative has at most |G|² parameter triples in any
fixed numerical section, without a field or prime-order assumption. -/
theorem representative_section_card_le (r : TetrahedronRoots G) (i : Fin 12) (g : G) :
    (((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronRepresentative r i t = g)).card : ℝ) ≤
        (Fintype.card G : ℝ)^2 := by
  let f : G → G := fun x =>
    (if tetrahedronNegative i then -x else x) + tetrahedronOffset r i
  have hf : Function.Injective f := by
    intro x y hxy
    have h : (if tetrahedronNegative i then -x else x) =
        (if tetrahedronNegative i then -y else y) := add_right_cancel hxy
    split_ifs at h with hi
    · exact neg_injective h
    · exact h
  have hsection : ∀ g,
      (((Finset.univ : Finset (TetrahedronParameters G)).filter
        (fun t => tetrahedronDirection (tetrahedronDirectionIndex i) t = g)).card : ℝ) ≤
          (Fintype.card G : ℝ)^2 := by
    intro g
    exact_mod_cast direction_section_card_le (tetrahedronDirectionIndex i) g
  exact section_bound_of_injective (Finset.univ : Finset (TetrahedronParameters G))
    (tetrahedronDirection (tetrahedronDirectionIndex i)) f hf
    ((Fintype.card G : ℝ)^2) (by positivity) hsection g

/-- At most 24|G|² parameter triples involve any fixed inverse orbit. -/
theorem full_candidate_orbit_incidence (r : TetrahedronRoots G) (g : G) :
    (((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => g ∈ twelvePairSupport (tetrahedronRepresentative r) t)).card : ℝ) ≤
        24 * (Fintype.card G : ℝ)^2 := by
  exact twelve_pair_incidence (Finset.univ : Finset (TetrahedronParameters G))
    (tetrahedronRepresentative r) ((Fintype.card G : ℝ)^2) (by positivity)
    (representative_section_card_le r) g

/-- Changing one numerical inverse orbit can affect a candidate only if
one of its twelve representatives uses that orbit. -/
theorem candidate_mem_congr_off_orbit (Q Q' : Vertex G → Prop)
    (g : G) (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (hQeq : ∀ v, v.2 ≠ g → v.2 ≠ -g → (Q v ↔ Q' v))
    (hg : g ∉ twelvePairSupport (tetrahedronRepresentative r) t) :
    t ∈ goodCandidates Q r ↔ t ∈ goodCandidates Q' r := by
  have hg' : g ∉ support (added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) := by
    rw [concrete_support_eq_twelvePairSupport r t]
    exact hg
  have hvQ (v : Vertex G)
      (hv : v ∈ added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) : Q v ↔ Q' v := by
    apply hQeq
    · intro he
      apply hg'
      rw [← he]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    · intro he
      apply hg'
      have hneg : -v.2 = g := by rw [he, neg_neg]
      rw [← hneg]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  simp only [goodCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨hi, hQ, hfresh⟩ <;> refine ⟨hi, ?_, hfresh⟩
  · intro v hv
    exact (hvQ v hv).mp (hQ v hv)
  · intro v hv
    exact (hvQ v hv).mpr (hQ v hv)

def changedCandidates (Q Q' : Vertex G → Prop) (r : TetrahedronRoots G) :
    Finset (TetrahedronParameters G) :=
  (goodCandidates Q r \ goodCandidates Q' r) ∪ (goodCandidates Q' r \ goodCandidates Q r)

/-- Changing the label of one inverse orbit changes the actual Q-candidate
count by at most 24|G|². This is the deterministic bounded-difference
constant; no concentration inequality is asserted. -/
theorem goodCandidate_count_change_le (Q Q' : Vertex G → Prop)
    (g : G) (r : TetrahedronRoots G)
    (hQeq : ∀ v, v.2 ≠ g → v.2 ≠ -g → (Q v ↔ Q' v)) :
    |((goodCandidates Q r).card : ℝ) - ((goodCandidates Q' r).card : ℝ)| ≤
      24 * (Fintype.card G : ℝ)^2 := by
  let N := 24 * (Fintype.card G)^2
  have hchanged : (changedCandidates Q Q' r).card ≤ N := by
    have hsub : changedCandidates Q Q' r ⊆
        (Finset.univ : Finset (TetrahedronParameters G)).filter
          (fun t => g ∈ twelvePairSupport (tetrahedronRepresentative r) t) := by
      intro t ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hg
      have heq := candidate_mem_congr_off_orbit Q Q' g r t hQeq hg
      rcases Finset.mem_union.mp ht with ht | ht
      · exact (Finset.mem_sdiff.mp ht).2 (heq.mp (Finset.mem_sdiff.mp ht).1)
      · exact (Finset.mem_sdiff.mp ht).2 (heq.mpr (Finset.mem_sdiff.mp ht).1)
    have hinc := full_candidate_orbit_incidence r g
    have hn : (((Finset.univ : Finset (TetrahedronParameters G)).filter
        (fun t => g ∈ twelvePairSupport (tetrahedronRepresentative r) t)).card) ≤ N := by
      dsimp [N]
      exact_mod_cast hinc
    exact (Finset.card_le_card hsub).trans hn
  have hleft : (goodCandidates Q r).card ≤ (goodCandidates Q' r).card + N := by
    have h₁ := Finset.card_sdiff_add_card_inter (goodCandidates Q r) (goodCandidates Q' r)
    have h₂ := Finset.card_sdiff_add_card_inter (goodCandidates Q' r) (goodCandidates Q r)
    have hd := Finset.card_le_card (s := goodCandidates Q r \ goodCandidates Q' r)
      (t := changedCandidates Q Q' r) Finset.subset_union_left
    rw [Finset.inter_comm (goodCandidates Q' r) (goodCandidates Q r)] at h₂
    omega
  have hright : (goodCandidates Q' r).card ≤ (goodCandidates Q r).card + N := by
    have h₁ := Finset.card_sdiff_add_card_inter (goodCandidates Q r) (goodCandidates Q' r)
    have h₂ := Finset.card_sdiff_add_card_inter (goodCandidates Q' r) (goodCandidates Q r)
    have hd := Finset.card_le_card (s := goodCandidates Q' r \ goodCandidates Q r)
      (t := changedCandidates Q Q' r) Finset.subset_union_right
    rw [Finset.inter_comm (goodCandidates Q' r) (goodCandidates Q r)] at h₂
    omega
  have hl' : ((goodCandidates Q r).card : ℝ) ≤ ((goodCandidates Q' r).card : ℝ) +
      24 * (Fintype.card G : ℝ)^2 := by dsimp [N] at hleft; exact_mod_cast hleft
  have hr' : ((goodCandidates Q' r).card : ℝ) ≤ ((goodCandidates Q r).card : ℝ) +
      24 * (Fintype.card G : ℝ)^2 := by dsimp [N] at hright; exact_mod_cast hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Two augmented samples whose child labels agree away from one inverse
orbit induce the same tagged Q membership outside that orbit. -/
theorem sampled_reservoir_agrees_off_orbit (ω ω' : FullSample G) (o : OddOrbit G)
    (hchild : ∀ o' : OddOrbit G, o' ≠ o →
      childLabel ((regroup ω).1 o') = childLabel ((regroup ω').1 o')) :
    ∀ v : Vertex G, v.2 ≠ orbitPlace (o,false) →
      v.2 ≠ -orbitPlace (o,false) →
      (ReservoirVertex ω true v ↔ ReservoirVertex ω' true v) := by
  intro v hv hvneg
  constructor
  · rintro ⟨o',side,hcoord,hlabel⟩
    have hne : o' ≠ o := by
      intro he
      subst o'
      cases side with
      | false => exact hv hcoord.symm
      | true =>
        have hneg := orbitPlace_neg o false
        exact hvneg (hcoord.symm.trans (by simpa using hneg))
    refine ⟨o',side,hcoord,?_⟩
    rw [← hchild o' hne]
    exact hlabel
  · rintro ⟨o',side,hcoord,hlabel⟩
    have hne : o' ≠ o := by
      intro he
      subst o'
      cases side with
      | false => exact hv hcoord.symm
      | true =>
        have hneg := orbitPlace_neg o false
        exact hvneg (hcoord.symm.trans (by simpa using hneg))
    refine ⟨o',side,hcoord,?_⟩
    rw [hchild o' hne]
    exact hlabel

/-- The paper's 24 n² bounded-difference estimate for the actual sampled
successful tetrahedron count. The probabilistic tail remains separate. -/
theorem sampled_goodCandidate_count_change_le (ω ω' : FullSample G) (o : OddOrbit G)
    (hchild : ∀ o' : OddOrbit G, o' ≠ o →
      childLabel ((regroup ω).1 o') = childLabel ((regroup ω').1 o'))
    (r : TetrahedronRoots G) :
    |((goodCandidates (ReservoirVertex ω true) r).card : ℝ) -
      ((goodCandidates (ReservoirVertex ω' true) r).card : ℝ)| ≤
        24 * (Fintype.card G : ℝ)^2 :=
  goodCandidate_count_change_le (ReservoirVertex ω true) (ReservoirVertex ω' true)
    (orbitPlace (o,false)) r (sampled_reservoir_agrees_off_orbit ω ω' o hchild)

end
end EndpointMatching.Tetrahedron
