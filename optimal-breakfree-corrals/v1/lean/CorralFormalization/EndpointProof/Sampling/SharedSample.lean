import CorralFormalization.EndpointProof.Sampling.BlockAvailability

/-!
One orbit sample with query-dependent disjoint packings.

The imported block-availability module provides the fixed-block law.
No independence between different queries is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Classical

namespace EndpointSharedSample

open EndpointBlockAvailability

/-- One categorical label per actual (or abstract) inverse orbit. -/
noncomputable def orbitMeasure {O : Type*} [Fintype O]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) : Measure (O → Label) :=
  Measure.pi (fun _ ↦ labelMeasure p τ h)

instance orbitMeasure_isProbabilityMeasure {O : Type*} [Fintype O]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) :
    IsProbabilityMeasure (orbitMeasure (O := O) p τ h) := by
  unfold orbitMeasure
  infer_instance

/-- Each query has its own injection; the source sample is the same. -/
def project {O I J : Type*} (e : I × J ↪ O) (ω : O → Label) : I → J → Label :=
  fun i j ↦ ω (e (i, j))

/-- An arbitrary injection into the one orbit sample has exactly the old
block-sample law. -/
theorem project_measurePreserving {O I J : Type*}
    [Fintype O] [Fintype I] [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) (e : I × J ↪ O) :
    MeasurePreserving (project e) (orbitMeasure p τ h) (sampleMeasure p τ h) := by
  let ν := labelMeasure p τ h
  have hflat : (Measure.pi (fun _ : O ↦ ν)).map
      (fun ω (ij : I × J) ↦ ω (e ij)) = Measure.pi (fun _ : I × J ↦ ν) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : O ↦ ν) e.injective)
  have hcurry : (Measure.pi (fun _ : I × J ↦ ν)).map
      (MeasurableEquiv.curry I J Label) =
      Measure.pi (fun _ : I ↦ Measure.pi (fun _ : J ↦ ν)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : I) (_ : J) ↦ ν))
  refine ⟨by unfold project; fun_prop, ?_⟩
  change (Measure.pi (fun _ : O ↦ ν)).map
      ((MeasurableEquiv.curry I J Label) ∘ (fun ω (ij : I × J) ↦ ω (e ij))) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hflat, hcurry]
  rfl

/-- The support includes both numerical signs of every used inverse orbit.
An embedding into K permits actual group elements as coordinates. -/
def support {O I J K : Type*} [Fintype J] [DecidableEq K]
    (e : I × J ↪ O) (place : O × Bool ↪ K) (i : I) : Finset K :=
  Finset.univ.image (fun jb : J × Bool ↦ place (e (i, jb.1), jb.2))

theorem support_pairwise {O I J K : Type*} [Fintype J] [DecidableEq K]
    (e : I × J ↪ O) (place : O × Bool ↪ K) :
    Pairwise fun i j : I ↦ Disjoint (support e place i) (support e place j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hi hj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hj
  have he := place.injective (ha.trans hb.symm)
  have hp := e.injective (congrArg Prod.fst he)
  exact hij (congrArg Prod.fst hp)

/-- Per-query indicators are independent even when different queries overlap. -/
theorem query_independent_indicators {O I J : Type*}
    [Fintype O] [Fintype I] [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) (e : I × J ↪ O)
    (demand : I → J → Label) :
    iIndepFun (fun i ω ↦ successIndicator demand i (project e ω))
      (orbitMeasure p τ h) := by
  have hp := project_measurePreserving p τ h e
  have hX (i : I) : HasLaw (fun ω ↦ project e ω i) (blockMeasure p τ h)
      (orbitMeasure p τ h) := by
    refine ⟨((measurable_pi_apply i).comp hp.measurable).aemeasurable, ?_⟩
    change (orbitMeasure p τ h).map ((Function.eval i) ∘ project e) = _
    rw [← Measure.map_map (measurable_pi_apply i) hp.measurable, hp.map_eq]
    exact (measurePreserving_eval (fun _ : I ↦ blockMeasure p τ h) i).map_eq
  have hblocks : iIndepFun (fun i ω ↦ project e ω i) (orbitMeasure p τ h) :=
    (iIndepFun_iff_hasLaw_pi_pi hX).2 ⟨hp.aemeasurable, hp.map_eq⟩
  exact hblocks.comp (fun i x ↦ if x = demand i then (1 : ℝ) else 0)
    (fun _ ↦ by fun_prop)

/-- The synthetic concentration inequality transports to the shared sample. -/
theorem shared_lower_tail {O I J : Type*}
    [Fintype O] [Fintype I] [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) (e : I × J ↪ O)
    (demand : I → J → Label) (t : ℝ) (ht : 0 ≤ t) :
    (orbitMeasure p τ h).real
      {ω : O → Label |
        (∑ i, successIndicator demand i (project e ω)) ≤
          (∑ i, successProbability p τ (demand i)) - t} ≤
      Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by
  have heq := (project_measurePreserving p τ h e).measureReal_preimage
    (s := {w : I → J → Label | (∑ i, successIndicator demand i w) ≤
      (∑ i, successProbability p τ (demand i)) - t})
    (by measurability)
  have hh := categorical_lower_tail p τ h demand t ht
  rw [← heq] at hh
  exact hh

/-- One high-probability event, followed by arbitrary queries and forbidden sets.
The packings e q are deterministic inputs. There is no assumption about
disjointness, independence or consistency across different q. -/
theorem shared_universal_availability {Q O I J K : Type*}
    [Fintype Q] [Fintype O] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq K]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (e : Q → I × J ↪ O) (place : O × Bool ↪ K)
    (demand : Q → I → J → Label) (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ q, (budget : ℝ) ≤ (∑ i, successProbability p τ (demand q i)) - t) :
    (orbitMeasure p τ h).real
      {ω : O → Label |
        ¬ UniversallyAvailable (fun q ↦ support (e q) place)
          (fun q ω i ↦ project (e q) ω i = demand q i) budget ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by
  have htail (q : Q) :
      (orbitMeasure p τ h).real
        {ω : O → Label |
          (Finset.univ.filter fun i ↦ project (e q) ω i = demand q i).card ≤ budget} ≤
      Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by
    apply le_trans (measureReal_mono ?_)
      (shared_lower_tail p τ h (e q) (demand q) t ht)
    intro ω hω
    change (∑ i, successIndicator (demand q) i (project (e q) ω)) ≤ _
    rw [sum_successIndicator_eq_card]
    exact le_trans (by exact_mod_cast hω) (hmean q)
  have hh := finite_query_failure_bound (orbitMeasure p τ h)
    (fun q ↦ support (e q) place)
    (fun q ω i ↦ project (e q) ω i = demand q i)
    (fun q ↦ support_pairwise (e q) place) budget
    (fun _ ↦ Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))))
    (fun q ↦ by
      convert htail q using 1
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      apply Iff.of_eq
      apply congrArg (fun s : Finset I ↦ s.card ≤ budget)
      ext i
      simp only [Finset.mem_filter])
  simpa using hh

/-- A concrete single sample exists when the explicit finite error is < 1. -/
theorem exists_shared_universally_available {Q O I J K : Type*}
    [Fintype Q] [Fintype O] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq K]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (e : Q → I × J ↪ O) (place : O × Bool ↪ K)
    (demand : Q → I → J → Label) (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ q, (budget : ℝ) ≤ (∑ i, successProbability p τ (demand q i)) - t)
    (hsmall : (Fintype.card Q : ℝ) *
        Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) < 1) :
    ∃ ω : O → Label,
      ∀ q (F : Finset K), F.card ≤ budget →
        ∃ i, project (e q) ω i = demand q i ∧ Disjoint (support (e q) place i) F := by
  by_contra hn
  have hbad : {ω : O → Label |
        ¬ UniversallyAvailable (fun q ↦ support (e q) place)
          (fun q ω i ↦ project (e q) ω i = demand q i) budget ω} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro hh
    exact hn ⟨ω, hh⟩
  have hh := shared_universal_availability p τ h e place demand budget t ht hmean
  rw [hbad] at hh
  have hh' : (1 : ℝ) ≤ (Fintype.card Q : ℝ) *
      Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by simpa using hh
  linarith

end EndpointSharedSample
