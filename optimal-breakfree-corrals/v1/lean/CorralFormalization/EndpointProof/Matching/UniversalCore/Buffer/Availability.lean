import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.Concentration
import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.Inventory
import CorralFormalization.EndpointProof.Matching.UniversalCore.QuadraticCapacityBudget
import CorralFormalization.EndpointProof.Flow.Tetrahedron.ConcentrationTails

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace EndpointMatching.UniversalCore.Buffer
open EndpointFlow.AbelianTransport
open EndpointFullProduct EndpointOriginalReservoir
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Successful parameter pairs whose inverse-orbit support meets F. -/
def forbiddenCandidates (Q : Vertex G → Prop) (F : Finset G) : Finset (Parameters G) :=
  (goodCandidates Q).filter (fun t => ∃ z ∈ F, z ∈ pairSupport t)

/-- A forbidden numerical coordinate meets at most six signed coordinate
sections. Their counts need not be disjoint. -/
theorem forbiddenCandidates_card_le (Q : Vertex G → Prop) (F : Finset G) (R : ℝ)
    (hsection : ∀ i : Fin 3, ∀ g : G,
      (((goodCandidates Q).filter (fun t => coordinate t i = g)).card : ℝ) ≤ R) :
    ((forbiddenCandidates Q F).card : ℝ) ≤ 6 * (F.card : ℝ) * R := by
  let D : Finset (G × (Fin 3 × Bool)) := F ×ˢ Finset.univ
  let hit (zib : G × (Fin 3 × Bool)) : Finset (Parameters G) :=
    (goodCandidates Q).filter (fun t =>
      (if zib.2.2 then -coordinate t zib.2.1 else coordinate t zib.2.1) = zib.1)
  have hhit : ∀ zib ∈ D, ((hit zib).card : ℝ) ≤ R := by
    rintro ⟨z,i,b⟩ _
    cases b with
    | false => exact hsection i z
    | true =>
      have heq : hit (z,i,true) =
          (goodCandidates Q).filter (fun t => coordinate t i = -z) := by
        ext t; simp only [hit, Finset.mem_filter, ↓reduceIte, neg_eq_iff_eq_neg]
      rw [heq]
      exact hsection i (-z)
  have hsub : forbiddenCandidates Q F ⊆ D.biUnion hit := by
    intro t ht
    obtain ⟨htgood,z,hzF,hzs⟩ := Finset.mem_filter.mp ht
    obtain ⟨ib,hib,hval⟩ := Finset.mem_image.mp hzs
    exact Finset.mem_biUnion.mpr ⟨(z,ib), Finset.mem_product.mpr ⟨hzF,Finset.mem_univ _⟩,
      Finset.mem_filter.mpr ⟨htgood,hval⟩⟩
  have hD : D.card = F.card * 6 := by simp [D,Fintype.card_prod]
  calc
    _ ≤ ((D.biUnion hit).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ zib ∈ D, ((hit zib).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := D) (t := hit))
    _ ≤ ∑ _zib ∈ D, R := Finset.sum_le_sum hhit
    _ = _ := by
      simp only [Finset.sum_const, hD, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- The paper's total and section count bounds leave a valid successful
buffer after every later forbidden F of size at most τn/96. -/
theorem exists_buffer_avoiding_of_counts (Q : Vertex G → Prop) (τ : ℝ) (F : Finset G)
    (hτ : 0 < τ)
    (htotal : τ^3 * (Fintype.card G : ℝ)^2 / 2 ≤ ((goodCandidates Q).card : ℝ))
    (hsection : ∀ i : Fin 3, ∀ g : G,
      (((goodCandidates Q).filter (fun t => coordinate t i = g)).card : ℝ) ≤
        2 * τ^2 * (Fintype.card G : ℝ))
    (hF : (F.card : ℝ) ≤ τ * (Fintype.card G : ℝ) / 96) :
    ∃ t ∈ goodCandidates Q, Disjoint (pairSupport t) F := by
  let n : ℝ := Fintype.card G
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hbad0 := forbiddenCandidates_card_le Q F (2 * τ^2 * n) hsection
  have hbad : ((forbiddenCandidates Q F).card : ℝ) ≤ 12 * τ^2 * n * (F.card : ℝ) := by
    nlinarith only [hbad0]
  have hprod := mul_le_mul_of_nonneg_left hF (show 0 ≤ 12 * τ^2 * n by positivity)
  have hpos : 0 < τ^3 * n^2 := by positivity
  have hlt : ((forbiddenCandidates Q F).card : ℝ) < ((goodCandidates Q).card : ℝ) := by
    nlinarith only [hbad,hprod,htotal,hpos]
  by_contra hnone
  have hsub : goodCandidates Q ⊆ forbiddenCandidates Q F := by
    intro t ht
    have hnd : ¬ Disjoint (pairSupport t) F := by
      intro hdis
      exact hnone ⟨t,ht,hdis⟩
    obtain ⟨z,hzS,hzF⟩ := Finset.not_disjoint_iff.mp hnd
    exact Finset.mem_filter.mpr ⟨ht,z,hzF,hzS⟩
  have hc := Finset.card_le_card hsub
  exact (not_le_of_gt hlt) (by exact_mod_cast hc)

theorem countEvent_buffer_avoids (τ : ℝ) (hτ : 0 < τ) (ω : FullSample G)
    (hcounts : CountEvent τ ω) (F : Finset G)
    (hF : (F.card : ℝ) ≤ τ * (Fintype.card G : ℝ) / 96) :
    ∃ t ∈ goodCandidates (ReservoirVertex ω true), Disjoint (pairSupport t) F :=
  exists_buffer_avoiding_of_counts (ReservoirVertex ω true) τ F hτ hcounts.1 hcounts.2 hF

omit [Fintype G] in
theorem pairSupport_card_le (t : Parameters G) : (pairSupport t).card ≤ 6 := by
  calc
    _ ≤ (Finset.univ : Finset (Fin 3 × Bool)).card := Finset.card_image_le
    _ = 6 := by simp [Fintype.card_prod]

omit [Fintype G] in
theorem familySupport_card_le (B : Finset (Parameters G)) :
    (B.biUnion pairSupport).card ≤ 6 * B.card := by
  calc
    _ ≤ ∑ t ∈ B, (pairSupport t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ B, 6 := Finset.sum_le_sum (fun t _ => pairSupport_card_le t)
    _ = _ := by simp [Nat.mul_comm]

/-- Deterministic greedy packing: if one can always find a successful
buffer outside the current numerical forbidden set, one can choose k
buffers with pairwise disjoint numerical inverse-orbit supports. -/
theorem exists_disjoint_candidate_family (Q : Vertex G → Prop) (U : Finset G) (k : ℕ)
    (havail : ∀ F : Finset G, F.card ≤ U.card + 6*k →
      ∃ t ∈ goodCandidates Q, Disjoint (pairSupport t) F) :
    ∃ B : Finset (Parameters G), B.card = k ∧
      (∀ t ∈ B, t ∈ goodCandidates Q ∧ Disjoint (pairSupport t) U) ∧
      (∀ t ∈ B, ∀ u ∈ B, t ≠ u → Disjoint (pairSupport t) (pairSupport u)) := by
  induction k with
  | zero =>
    exact ⟨∅,by simp,by simp,by simp⟩
  | succ k ih =>
    have havailk : ∀ F : Finset G, F.card ≤ U.card + 6*k →
        ∃ t ∈ goodCandidates Q, Disjoint (pairSupport t) F := by
      intro F hF
      apply havail F
      omega
    obtain ⟨B,hcard,hgood,hpair⟩ := ih havailk
    let F := U ∪ B.biUnion pairSupport
    have hF : F.card ≤ U.card + 6*(k+1) := by
      calc
        _ ≤ U.card + (B.biUnion pairSupport).card := Finset.card_union_le _ _
        _ ≤ U.card + 6 * B.card := Nat.add_le_add_left (familySupport_card_le B) _
        _ ≤ U.card + 6*(k+1) := by rw [hcard]; omega
    obtain ⟨t,htgood,htdis⟩ := havail F hF
    have htB : t ∉ B := by
      intro ht
      have hx : coordinate t 0 ∈ B.biUnion pairSupport :=
        Finset.mem_biUnion.mpr ⟨t,ht,positive_coordinate_mem_support t 0⟩
      exact Finset.disjoint_left.mp htdis (positive_coordinate_mem_support t 0)
        (Finset.mem_union_right U hx)
    have htU : Disjoint (pairSupport t) U := htdis.mono_right Finset.subset_union_left
    have htBdis : ∀ u ∈ B, Disjoint (pairSupport t) (pairSupport u) := by
      intro u hu
      apply htdis.mono_right
      intro x hx
      exact Finset.mem_union_right U (Finset.mem_biUnion.mpr ⟨u,hu,hx⟩)
    refine ⟨insert t B,by simp [htB,hcard], ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨htgood,htU⟩
      · exact hgood u hu
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxt | hxb
      · subst x
        rcases Finset.mem_insert.mp hy with hyt | hyb
        · subst y
          exact False.elim (hxy rfl)
        · exact htBdis y hyb
      · rcases Finset.mem_insert.mp hy with hyt | hyb
        · subst y
          exact (htBdis x hxb).symm
        · exact hpair x hxb y hyb hxy

/-- Under the single count event, every U with the displayed total budget
admits k genuine successful buffers with pairwise disjoint supports. -/
theorem countEvent_disjoint_buffers (τ : ℝ) (hτ : 0 < τ) (ω : FullSample G)
    (hcounts : CountEvent τ ω) (U : Finset G) (k : ℕ)
    (hbudget : (U.card : ℝ) + 6 * k ≤ τ * (Fintype.card G : ℝ) / 96) :
    ∃ B : Finset (Parameters G), B.card = k ∧
      (∀ t ∈ B, t ∈ goodCandidates (ReservoirVertex ω true) ∧
        Disjoint (pairSupport t) U) ∧
      (∀ t ∈ B, ∀ u ∈ B, t ≠ u → Disjoint (pairSupport t) (pairSupport u)) := by
  apply exists_disjoint_candidate_family (ReservoirVertex ω true) U k
  intro F hF
  apply countEvent_buffer_avoids τ hτ ω hcounts F
  have hcast : (F.card : ℝ) ≤ (U.card : ℝ) + 6*k := by exact_mod_cast hF
  exact hcast.trans hbudget

/-- The selected buffers satisfy the exact inventory, uniqueness and
matching hypotheses consumed by sampled_core_of_tetrahedron_counts. -/
theorem countEvent_buffer_inventory (τ : ℝ) (hτ : 0 < τ) (ω : FullSample G)
    (hodd : Odd (Fintype.card G)) (hcounts : CountEvent τ ω) (U : Finset G) (k : ℕ)
    (hbudget : (U.card : ℝ) + 6 * k ≤ τ * (Fintype.card G : ℝ) / 96) :
    ∃ B : Finset (Parameters G), B.card = k ∧
      (∀ t ∈ B, ∀ p, pick t p ∈ availablePairInventory (ReservoirVertex ω true) U p) ∧
      (∀ t ∈ B, ∀ u ∈ B, t ≠ u → ∀ p q, pick t p ≠ pick u q) ∧
      (∀ t ∈ B, Nonempty (Matching (Finset.univ.biUnion (pick t)))) := by
  obtain ⟨B,hcard,hgood,hdis⟩ := countEvent_disjoint_buffers τ hτ ω hcounts U k hbudget
  refine ⟨B,hcard,?_,?_,?_⟩
  · intro t ht p
    exact pick_mem_availablePairInventory (ReservoirVertex ω true) U t (hgood t ht).1
      (hgood t ht).2 p
  · intro t ht u hu hne p q
    exact disjoint_support_picks_ne t u (hdis t ht u hu hne) p q
  · intro t ht
    have hv : GeometricallyValid t :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp (hgood t ht).1).1).2
    exact matching_of_valid hodd t hv

/-- The written quadratic exclusion and padding-buffer floors satisfy the
stronger numerical deletion budget required by the buffer event. -/
theorem explicit_buffer_budget (τ : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3)
    (U : Finset G) (hU : U.card ≤ quadraticCoreCapacity τ (Fintype.card G)) :
    (U.card : ℝ) + 6 * paddingBufferCount τ (Fintype.card G) ≤
      τ * (Fintype.card G : ℝ) / 96 := by
  let n : ℝ := Fintype.card G
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hcap : (quadraticCoreCapacity τ (Fintype.card G) : ℝ) ≤
      (1 / 10^6 : ℝ) * τ^2 * n := by
    unfold quadraticCoreCapacity
    exact Nat.floor_le (by positivity)
  have hbuf : (paddingBufferCount τ (Fintype.card G) : ℝ) ≤ τ * n / 1000 := by
    unfold paddingBufferCount
    exact Nat.floor_le (by positivity)
  have hu : (U.card : ℝ) ≤ quadraticCoreCapacity τ (Fintype.card G) := by exact_mod_cast hU
  have ht : τ^2 * n ≤ τ * n / 3 := by
    have hx : 0 ≤ ((1 / 3 : ℝ) - τ) * τ * n := by positivity
    nlinarith
  nlinarith

/-- On the one count event, the written quadratic exclusion budget admits
the paper's full padding-buffer count, each in the actual Q inventory. -/
theorem countEvent_explicit_buffer_inventory (τ : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3)
    (ω : FullSample G) (hodd : Odd (Fintype.card G)) (hcounts : CountEvent τ ω)
    (U : Finset G) (hU : U.card ≤ quadraticCoreCapacity τ (Fintype.card G)) :
    ∃ B : Finset (Parameters G), B.card = paddingBufferCount τ (Fintype.card G) ∧
      (∀ t ∈ B, ∀ p, pick t p ∈ availablePairInventory (ReservoirVertex ω true) U p) ∧
      (∀ t ∈ B, ∀ u ∈ B, t ≠ u → ∀ p q, pick t p ≠ pick u q) ∧
      (∀ t ∈ B, Nonempty (Matching (Finset.univ.biUnion (pick t)))) :=
  countEvent_buffer_inventory τ hτ ω hodd hcounts U
    (paddingBufferCount τ (Fintype.card G)) (explicit_buffer_budget τ hτ hτmax U hU)

/-- The actual Q inventory provides enough matched, pairwise disjoint
padding buffers for every later exclusion in the quadratic range. -/
def CategoricalBuffers (τ : ℝ) (ω : FullSample G) : Prop :=
  ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
    ∃ B : Finset (Parameters G),
      3 * paddingQuota τ (Fintype.card G) ≤ B.card ∧
      (∀ t ∈ B, ∀ p, pick t p ∈ availablePairInventory (ReservoirVertex ω true) U p) ∧
      (∀ t ∈ B, ∀ u ∈ B, t ≠ u → ∀ p q, pick t p ≠ pick u q) ∧
      (∀ t ∈ B, Nonempty (Matching (Finset.univ.biUnion (pick t))))

theorem explicitBuffers_of_countEvent (τ : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3)
    (hodd : Odd (Fintype.card G)) (hnlarge : (4000 : ℝ) ≤ τ^2 * Fintype.card G)
    (ω : FullSample G) (hcounts : CountEvent τ ω) : CategoricalBuffers τ ω := by
  intro U hU
  obtain ⟨B,hcard,hmem,hunique,hmatch⟩ :=
    countEvent_explicit_buffer_inventory τ hτ hτmax ω hodd hcounts U hU
  have hcount := padding_buffer_floor_bound τ (Fintype.card G) hτ hτmax hnlarge
  refine ⟨B,?_,hmem,hunique,hmatch⟩
  rw [hcard]
  omega

/-- The original sample's one augmentation simultaneously supplies the
numerical-deletion tetrahedron parameters and the required padding
buffers for every later allowable numerical exclusion. -/
def CoreConstructionEvent (τ : ℝ) (ω : FullSample G) : Prop :=
  EndpointMatching.Tetrahedron.TetrahedronParametersAvailable (ReservoirVertex ω true)
    (quadraticCoverBudget τ (Fintype.card G)) ∧ CategoricalBuffers τ ω

theorem explicitQEvent_failure_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hτ : 0 < (τ : ℝ)) (hτmax : (τ : ℝ) ≤ 1 / 3)
    (hn : 1152 ≤ Fintype.card G)
    (hnlarge : (4000 : ℝ) ≤ (τ : ℝ)^2 * Fintype.card G) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ CoreConstructionEvent (τ : ℝ) ω} ≤
      (Fintype.card G : ℝ)^6 * Real.exp (-(τ : ℝ)^24 * (Fintype.card G : ℝ) / 2304) +
        6 * (Fintype.card G : ℝ)^7 * Real.exp (-(τ : ℝ)^20 * (Fintype.card G : ℝ) / 100) +
      Real.exp (-(τ : ℝ)^6 * (Fintype.card G : ℝ) / 144) +
        3 * (Fintype.card G : ℝ) * Real.exp (-(τ : ℝ)^4 * (Fintype.card G : ℝ) / 4) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  let A : Set (FullSample G) := {ω |
    ¬ EndpointMatching.Tetrahedron.TetrahedronParametersAvailable (ReservoirVertex ω true)
      (quadraticCoverBudget (τ : ℝ) (Fintype.card G))}
  let B : Set (FullSample G) := {ω | ¬ CountEvent (τ : ℝ) ω}
  have hsub : {ω | ¬ CoreConstructionEvent (τ : ℝ) ω} ⊆ A ∪ B := by
    intro ω hbad
    by_contra hnot
    have hp : EndpointMatching.Tetrahedron.TetrahedronParametersAvailable (ReservoirVertex ω true)
        (quadraticCoverBudget (τ : ℝ) (Fintype.card G)) := by
      by_contra hp
      exact hnot (Or.inl hp)
    have hc : CountEvent (τ : ℝ) ω := by
      by_contra hc
      exact hnot (Or.inr hc)
    exact hbad ⟨hp,explicitBuffers_of_countEvent (τ : ℝ) hτ hτmax hodd hnlarge ω hc⟩
  have hbudget : (quadraticCoverBudget (τ : ℝ) (Fintype.card G) : ℝ) ≤
      (τ : ℝ)^2 * (Fintype.card G : ℝ) / 192 :=
    (quadratic_capacity_budgets (τ : ℝ) (Fintype.card G) 0 hτ hτmax hnlarge (Nat.zero_le _)).2.2
  have hA := EndpointMatching.Tetrahedron.parameters_failure_probability_le hodd
    q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ hτ hn
    (quadraticCoverBudget (τ : ℝ) (Fintype.card G)) hbudget
  have hB := countEvent_failure_probability hodd q η a b hq0 hq1 hη0 hη1
    ha hb hab p τ h hP hQ (by omega : 24 ≤ Fintype.card G)
  have hbound := (measureReal_mono hsub (measure_ne_top μ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add hA hB))
  linarith

end
end EndpointMatching.UniversalCore.Buffer
