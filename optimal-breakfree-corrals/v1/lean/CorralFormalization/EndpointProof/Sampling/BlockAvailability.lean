import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
Availability estimates for finite families of disjoint candidate blocks.

The deterministic theorem handles arbitrary later forbidden coordinate sets.
The probability model below concerns already packed, equal-sized orbit blocks.
Neither the affine packing nor the original-q thinning construction is assumed
to have been proved by this file.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Classical

namespace EndpointBlockAvailability

/-- Each forbidden coordinate can hit at most one member of a disjoint family. -/
theorem exists_disjoint_of_card_lt
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (S : Finset I) (support : I → Finset K)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (support i) (support j))
    (F : Finset K) (hcard : F.card < S.card) :
    ∃ i ∈ S, Disjoint (support i) F := by
  classical
  by_contra hn
  have hhit : ∀ i : S, ∃ x : F, (x : K) ∈ support i := by
    intro i
    have hi : ¬ Disjoint (support i) F := by
      intro hd
      exact hn ⟨i, i.2, hd⟩
    rw [Finset.not_disjoint_iff] at hi
    obtain ⟨x, hx, hF⟩ := hi
    exact ⟨⟨x, hF⟩, hx⟩
  choose f hf using hhit
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hd := hdisj i i.2 j j.2 hne
    have hxj : ((f i : F) : K) ∈ support j := by simpa [hij] using hf j
    exact Finset.disjoint_left.mp hd (hf i) hxj
  have hle := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe] at hle
  omega

/-- Success is fixed before the universal quantifier over forbidden sets. -/
def CountGood {Q I Ω : Type*} [Fintype I]
    (success : Q → Ω → I → Prop) (budget : ℕ) (ω : Ω) : Prop :=
  ∀ q, budget < (Finset.univ.filter (success q ω)).card

/-- The target contract permits both the query and the forbidden set to be later. -/
def UniversallyAvailable {Q I K Ω : Type*} [DecidableEq K]
    (support : Q → I → Finset K) (success : Q → Ω → I → Prop)
    (budget : ℕ) (ω : Ω) : Prop :=
  ∀ q (F : Finset K), F.card ≤ budget →
    ∃ i, success q ω i ∧ Disjoint (support q i) F

/-- One count event supplies all later queries and all later small forbidden sets. -/
theorem countGood_implies_universallyAvailable
    {Q I K Ω : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (support : Q → I → Finset K) (success : Q → Ω → I → Prop)
    (hdisj : ∀ q, Pairwise fun i j ↦ Disjoint (support q i) (support q j))
    (budget : ℕ) (ω : Ω) (hgood : CountGood success budget ω) :
    UniversallyAvailable support success budget ω := by
  intro q F hF
  obtain ⟨i, hi, hd⟩ := exists_disjoint_of_card_lt
    (Finset.univ.filter (success q ω)) (support q)
    (fun _ _ _ _ hij ↦ hdisj q hij) F (lt_of_le_of_lt hF (hgood q))
  exact ⟨i, (Finset.mem_filter.mp hi).2, hd⟩

/-- The seven post-reservoir labels: three P parts, three Q parts, neither. -/
abbrev Label := Fin 7

/-- Their probabilities use the actual p,p,p,tau,tau,tau,residual categorical law. -/
def labelWeights (p τ : ℝ≥0) : Label → ℝ≥0 :=
  ![p, p, p, τ, τ, τ, 1 - (3 * p + 3 * τ)]

theorem sum_labelWeights (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) :
    ∑ l, labelWeights p τ l = 1 := by
  simp only [labelWeights, Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  have he := tsub_add_cancel_of_le h
  linear_combination he

noncomputable def labelPMF (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) : PMF Label :=
  PMF.ofFintype (fun l ↦ (labelWeights p τ l : ℝ≥0∞))
    (by exact_mod_cast sum_labelWeights p τ h)

noncomputable def labelMeasure (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) :
    Measure Label := (labelPMF p τ h).toMeasure

instance labelMeasure_isProbabilityMeasure (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) :
    IsProbabilityMeasure (labelMeasure p τ h) := by
  unfold labelMeasure
  infer_instance

theorem labelMeasure_singleton (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) (l : Label) :
    labelMeasure p τ h {l} = (labelWeights p τ l : ℝ≥0∞) := by
  exact (labelPMF p τ h).toMeasure_apply_singleton l (measurableSet_singleton l)

/-- A block has one independent categorical label for every required inverse orbit. -/
noncomputable def blockMeasure {J : Type*} [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) : Measure (J → Label) :=
  Measure.pi (fun _ ↦ labelMeasure p τ h)

instance blockMeasure_isProbabilityMeasure {J : Type*} [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) :
    IsProbabilityMeasure (blockMeasure (J := J) p τ h) := by
  unfold blockMeasure
  infer_instance

/-- A sample consists of disjoint prepacked blocks, sampled before the query. -/
noncomputable def sampleMeasure {I J : Type*} [Fintype I] [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) : Measure (I → J → Label) :=
  Measure.pi (fun _ ↦ blockMeasure p τ h)

instance sampleMeasure_isProbabilityMeasure {I J : Type*} [Fintype I] [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) :
    IsProbabilityMeasure (sampleMeasure (I := I) (J := J) p τ h) := by
  unfold sampleMeasure
  infer_instance

theorem blockMeasure_singleton {J : Type*} [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1) (word : J → Label) :
    blockMeasure p τ h {word} = ∏ j, (labelWeights p τ (word j) : ℝ≥0∞) := by
  rw [blockMeasure, Measure.pi_singleton]
  simp only [labelMeasure_singleton]

noncomputable def successIndicator {I J : Type*} [Fintype J]
    (demand : I → J → Label) (i : I) (ω : I → J → Label) : ℝ :=
  if ω i = demand i then 1 else 0

/-- The candidate's success probability is computed from the categorical law. -/
noncomputable def successProbability {J : Type*} [Fintype J]
    (p τ : ℝ≥0) (word : J → Label) : ℝ :=
  ∏ j, (labelWeights p τ (word j) : ℝ)

theorem integral_successIndicator {I J : Type*} [Fintype I] [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (demand : I → J → Label) (i : I) :
    ∫ ω, successIndicator demand i ω ∂sampleMeasure p τ h =
      successProbability p τ (demand i) := by
  unfold sampleMeasure successIndicator
  rw [integral_comp_eval (i := i) (μ := fun _ : I ↦ blockMeasure p τ h)
    (f := fun x : J → Label ↦ if x = demand i then (1 : ℝ) else 0) (by fun_prop)]
  have hind : (fun x : J → Label ↦ if x = demand i then (1 : ℝ) else 0) =
      Set.indicator {demand i} 1 := by
    ext x
    simp [Set.indicator_apply]
  rw [hind, integral_indicator_one (measurableSet_singleton _), measureReal_def,
    blockMeasure_singleton, ENNReal.toReal_prod]
  simp [successProbability]

theorem successProbability_ge_pow {J : Type*} [Fintype J]
    (p τ v : ℝ≥0) (word : J → Label)
    (hmin : ∀ j, v ≤ labelWeights p τ (word j)) :
    (v : ℝ) ^ Fintype.card J ≤ successProbability p τ word := by
  calc
    (v : ℝ) ^ Fintype.card J = ∏ _ : J, (v : ℝ) := by simp
    _ ≤ ∏ j, (labelWeights p τ (word j) : ℝ) := by
      exact Finset.prod_le_prod (fun _ _ ↦ v.coe_nonneg)
        (fun j _ ↦ by exact_mod_cast hmin j)

/-- A genuine Hoeffding lower-tail bound in the finite categorical product model.
Its exponent is additive, rather than the sharper multiplicative Chernoff
exponent used in the written concentration argument. -/
theorem categorical_lower_tail {I J : Type*} [Fintype I] [Fintype J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (demand : I → J → Label) (t : ℝ) (ht : 0 ≤ t) :
    (sampleMeasure p τ h).real
      {ω : I → J → Label |
        (∑ i, successIndicator demand i ω) ≤
          (∑ i, successProbability p τ (demand i)) - t} ≤
      Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by
  let μ : Measure (I → J → Label) := sampleMeasure p τ h
  let Y : I → (I → J → Label) → ℝ := fun i ω ↦
    successProbability p τ (demand i) - successIndicator demand i ω
  have hindep : iIndepFun Y μ := by
    exact iIndepFun_pi (X := fun i x ↦ successProbability p τ (demand i) -
      if x = demand i then (1 : ℝ) else 0) (fun _ ↦ (by fun_prop))
  have hsub (i : I) : HasSubgaussianMGF (Y i) (1 / 4) μ := by
    have hb : ∀ᵐ ω ∂μ, successIndicator demand i ω ∈ Set.Icc (0 : ℝ) 1 := by
      exact ae_of_all _ fun ω ↦ by
        unfold successIndicator
        split_ifs <;> norm_num
    have hh := (hasSubgaussianMGF_of_mem_Icc
      (X := successIndicator demand i) (μ := μ) (by fun_prop) hb).neg
    have he : (∫ ω, successIndicator demand i ω ∂μ) =
        successProbability p τ (demand i) := integral_successIndicator p τ h demand i
    change HasSubgaussianMGF
      (fun ω ↦ -(successIndicator demand i ω - ∫ ω, successIndicator demand i ω ∂μ))
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ at hh
    convert hh using 1 <;> norm_num [Y, he, neg_sub]
  have hh := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
    (s := Finset.univ) (c := fun _ ↦ (1 / 4 : ℝ≥0)) (fun i _ ↦ hsub i) ht
  have hset : {ω | t ≤ ∑ i ∈ Finset.univ, Y i ω} =
      {ω : I → J → Label | (∑ i, successIndicator demand i ω) ≤
        (∑ i, successProbability p τ (demand i)) - t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Y, Finset.sum_sub_distrib]
    constructor <;> intro hi <;> linarith
  rw [hset] at hh
  simpa [μ, mul_assoc] using hh

theorem sum_successIndicator_eq_card {I J : Type*} [Fintype I] [Fintype J]
    (demand : I → J → Label) (ω : I → J → Label) :
    (∑ i, successIndicator demand i ω) =
      ((Finset.univ.filter fun i ↦ ω i = demand i).card : ℝ) := by
  simp [successIndicator, Finset.sum_boole]

/-- Finite query union. The concentration inputs are explicit hypotheses here;
no probability independence between different queries is required. -/
theorem finite_query_failure_bound
    {Q I K Ω : Type*} [Fintype Q] [Fintype I] [DecidableEq I] [DecidableEq K]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (support : Q → I → Finset K) (success : Q → Ω → I → Prop)
    (hdisj : ∀ q, Pairwise fun i j ↦ Disjoint (support q i) (support q j))
    (budget : ℕ) (failure : Q → ℝ)
    (htail : ∀ q, μ.real {ω | (Finset.univ.filter (success q ω)).card ≤ budget}
      ≤ failure q) :
    μ.real {ω | ¬ UniversallyAvailable support success budget ω} ≤ ∑ q, failure q := by
  have hsubset : {ω | ¬ UniversallyAvailable support success budget ω} ⊆
      ⋃ q, {ω | (Finset.univ.filter (success q ω)).card ≤ budget} := by
    intro ω hbad
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    by_contra hn
    apply hbad
    apply countGood_implies_universallyAvailable support success hdisj budget ω
    intro q
    have hq : ¬ (Finset.univ.filter (success q ω)).card ≤ budget := by
      intro hh
      exact hn ⟨q, hh⟩
    omega
  calc
    μ.real {ω | ¬ UniversallyAvailable support success budget ω}
      ≤ μ.real (⋃ q, {ω | (Finset.univ.filter (success q ω)).card ≤ budget}) :=
        measureReal_mono hsubset
    _ ≤ ∑ q, μ.real {ω | (Finset.univ.filter (success q ω)).card ≤ budget} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ q, failure q := Finset.sum_le_sum (fun q _ ↦ htail q)

/-- Both numerical members of each inverse orbit are included in its support.
The first index is the candidate; the second is its orbit slot. -/
def blockSupport {I J : Type*} [DecidableEq I] [DecidableEq J] [Fintype J]
    (i : I) : Finset ((I × J) × Bool) :=
  Finset.univ.image (fun jb : J × Bool ↦ ((i, jb.1), jb.2))

theorem blockSupport_pairwise {I J : Type*}
    [DecidableEq I] [DecidableEq J] [Fintype J] :
    Pairwise fun i j : I ↦ Disjoint (blockSupport (J := J) i) (blockSupport j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hi hj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hj
  have he : i = j := congrArg (fun x : (I × J) × Bool ↦ x.1.1) (ha.trans hb.symm)
  exact hij he

/-- An unconditional probability estimate for the limited fixed-block model.
Only the numerical mean/budget separation is a premise. The conclusion
contains every later query and every later numerical forbidden set. -/
theorem categorical_universal_availability
    {Q I J : Type*} [Fintype Q] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (demand : Q → I → J → Label) (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ q, (budget : ℝ) ≤ (∑ i, successProbability p τ (demand q i)) - t) :
    (sampleMeasure p τ h).real
      {ω : I → J → Label |
        ¬ UniversallyAvailable (fun _ : Q ↦ blockSupport (J := J))
          (fun q ω i ↦ ω i = demand q i) budget ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by
  have htail (q : Q) :
      (sampleMeasure p τ h).real
        {ω : I → J → Label | (Finset.univ.filter fun i ↦ ω i = demand q i).card ≤ budget}
      ≤ Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by
    apply le_trans (measureReal_mono ?_) (categorical_lower_tail p τ h (demand q) t ht)
    intro ω hω
    change (∑ i, successIndicator (demand q) i ω) ≤ _
    rw [sum_successIndicator_eq_card]
    exact le_trans (by exact_mod_cast hω) (hmean q)
  have hh := finite_query_failure_bound (sampleMeasure p τ h)
    (fun _ : Q ↦ blockSupport (J := J)) (fun q ω i ↦ ω i = demand q i)
    (fun _ ↦ blockSupport_pairwise) budget
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

/-- A nonvacuous existence consequence once the displayed finite error is < 1. -/
theorem exists_categorical_universally_available
    {Q I J : Type*} [Fintype Q] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (p τ : ℝ≥0) (h : 3 * p + 3 * τ ≤ 1)
    (demand : Q → I → J → Label) (budget : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ q, (budget : ℝ) ≤ (∑ i, successProbability p τ (demand q i)) - t)
    (hsmall : (Fintype.card Q : ℝ) *
        Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) < 1) :
    ∃ ω : I → J → Label,
      UniversallyAvailable (fun _ : Q ↦ blockSupport (J := J))
        (fun q ω i ↦ ω i = demand q i) budget ω := by
  by_contra hn
  have hbad : {ω : I → J → Label |
        ¬ UniversallyAvailable (fun _ : Q ↦ blockSupport (J := J))
          (fun q ω i ↦ ω i = demand q i) budget ω} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro hh
    exact hn ⟨ω, hh⟩
  have hh := categorical_universal_availability p τ h demand budget t ht hmean
  rw [hbad] at hh
  have hh' : (1 : ℝ) ≤ (Fintype.card Q : ℝ) *
      Real.exp (-t ^ 2 / (2 * (Fintype.card I : ℝ) * (1 / 4))) := by simpa using hh
  linarith

end EndpointBlockAvailability
