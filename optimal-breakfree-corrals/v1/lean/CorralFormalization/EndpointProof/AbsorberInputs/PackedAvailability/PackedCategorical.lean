import CorralFormalization.EndpointProof.AbsorberInputs.PackedAvailability.HeterogeneousChernoff
import CorralFormalization.EndpointProof.Sampling.SharedSample

/-!
The probabilistic part of general packed availability (packed-availability).

There is one categorical product sample, indexed by actual or abstract inverse
orbits O. Each query fixes an injection from its dependent collection of
candidate slots into O before sampling. Candidate sizes, demanded labels and
individual label probabilities may differ. A candidate asks for exactly one
specified categorical label at each of its slots. Different queries may reuse
arbitrary orbits; only the injection inside each query is required.

The event below precedes every query and every later numerical forbidden set.
Its avoidance conclusion uses the actual number of successes in that sample,
not an artificially smaller deterministic deletion budget.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace AbsorberInputs.PackedAvailability

noncomputable section

section OneQuery

variable {O I L K : Type*} [Fintype O] [Fintype I] [Fintype L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    {J : I → Type*} [∀ i, Fintype (J i)]

/-- One independent categorical label per orbit. The law may vary by orbit. -/
def categoricalMeasure (ν : O → Measure L) : Measure (O → L) := Measure.pi ν

instance categoricalMeasure_isProbabilityMeasure (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)] :
    IsProbabilityMeasure (categoricalMeasure ν) := by
  unfold categoricalMeasure
  infer_instance

/-- The actual demanded orbit labels, with no padding slots. -/
def project (e : (Sigma J) ↪ O) (ω : O → L) : (i : I) → J i → L :=
  fun i j => ω (e ⟨i,j⟩)

def candidateMeasure (ν : O → Measure L) (e : (Sigma J) ↪ O) (i : I) :
    Measure (J i → L) := Measure.pi (fun j => ν (e ⟨i,j⟩))

instance candidateMeasure_isProbabilityMeasure (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)] (e : (Sigma J) ↪ O) (i : I) :
    IsProbabilityMeasure (candidateMeasure ν e i) := by
  unfold candidateMeasure
  infer_instance

def packedMeasure (ν : O → Measure L) (e : (Sigma J) ↪ O) :
    Measure ((i : I) → J i → L) := Measure.pi (candidateMeasure ν e)

instance packedMeasure_isProbabilityMeasure (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)] (e : (Sigma J) ↪ O) :
    IsProbabilityMeasure (packedMeasure ν e) := by
  unfold packedMeasure
  infer_instance

omit [Fintype L] [MeasurableSingletonClass L] in
/-- A deterministic disjoint packing has the corresponding independent block
law under the one unchanged orbit sample. The block sizes may be different. -/
theorem project_measurePreserving (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)] (e : (Sigma J) ↪ O) :
    MeasurePreserving (project e) (categoricalMeasure ν) (packedMeasure ν e) := by
  have hflat : (Measure.pi ν).map (fun ω (ij : Sigma J) => ω (e ij)) =
      Measure.pi (fun ij : Sigma J => ν (e ij)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj (P := ν) e.injective)
  have hcurry : (Measure.pi (fun ij : Sigma J => ν (e ij))).map
      (MeasurableEquiv.piCurry (fun (_ : I) (_ : J _) => L)) =
      Measure.pi (fun i : I => Measure.pi (fun j : J i => ν (e ⟨i,j⟩))) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_piCurry (fun i j => ν (e ⟨i,j⟩)))
  refine ⟨by unfold project; fun_prop, ?_⟩
  change (Measure.pi ν).map
    ((MeasurableEquiv.piCurry (fun (_ : I) (_ : J _) => L)) ∘
      (fun ω (ij : Sigma J) => ω (e ij))) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hflat, hcurry]
  rfl

def indicator (demand : (i : I) → J i → L) (i : I)
    (w : (i : I) → J i → L) : ℝ := if w i = demand i then 1 else 0

/-- The actual product of the probabilities of the labels that are demanded. -/
def candidateProbability (ν : O → Measure L) (e : (Sigma J) ↪ O)
    (demand : (i : I) → J i → L) (i : I) : ℝ :=
  ∏ j, (ν (e ⟨i,j⟩)).real {demand i j}

omit [Fintype O] in
theorem integral_indicator (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)] (e : (Sigma J) ↪ O)
    (demand : (i : I) → J i → L) (i : I) :
    ∫ w, indicator demand i w ∂packedMeasure ν e =
      candidateProbability ν e demand i := by
  unfold packedMeasure indicator
  rw [integral_comp_eval (i := i) (μ := candidateMeasure ν e)
    (f := fun x : J i → L => if x = demand i then (1 : ℝ) else 0) (by fun_prop)]
  have hind : (fun x : J i → L => if x = demand i then (1 : ℝ) else 0) =
      Set.indicator {demand i} 1 := by
    ext x
    simp [Set.indicator_apply]
  rw [hind, integral_indicator_one (measurableSet_singleton _), measureReal_def]
  change (Measure.pi (fun j : J i => ν (e ⟨i,j⟩)) {demand i}).toReal = _
  rw [Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

omit [Fintype O] [Fintype I] [Fintype L] [MeasurableSingletonClass L] in
theorem candidateProbability_nonneg (ν : O → Measure L) (e : (Sigma J) ↪ O)
    (demand : (i : I) → J i → L) (i : I) :
    0 ≤ candidateProbability ν e demand i := by
  exact Finset.prod_nonneg fun j _ => measureReal_nonneg

omit [Fintype O] [Fintype I] [Fintype L] [MeasurableSingletonClass L] in
theorem candidateProbability_le_one (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)] (e : (Sigma J) ↪ O)
    (demand : (i : I) → J i → L) (i : I) :
    candidateProbability ν e demand i ≤ 1 := by
  exact Finset.prod_le_one (fun _ _ => measureReal_nonneg)
    (fun _ _ => measureReal_le_one)

omit [Fintype O] [Fintype I] [Fintype L] [MeasurableSingletonClass L] in
/-- The at-most-m calculation uses the actual slot count. Empty demands and
different slot counts are included. The density is explicitly at most one. -/
theorem candidateProbability_ge_pow (ν : O → Measure L) (e : (Sigma J) ↪ O)
    (demand : (i : I) → J i → L) (i : I) (m : ℕ) (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hsize : Fintype.card (J i) ≤ m)
    (hmin : ∀ j, v ≤ (ν (e ⟨i,j⟩)).real {demand i j}) :
    v^m ≤ candidateProbability ν e demand i := by
  calc
    v^m ≤ v^(Fintype.card (J i)) := pow_le_pow_of_le_one hv0 hv1 hsize
    _ = ∏ _ : J i, v := by simp
    _ ≤ candidateProbability ν e demand i :=
      Finset.prod_le_prod (fun _ _ => hv0) (fun j _ => hmin j)

omit [Fintype O] [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L] in
theorem count_eq_sum_indicator (e : (Sigma J) ↪ O)
    (demand : (i : I) → J i → L) (ω : O → L) :
    ((Finset.univ.filter fun i => project e ω i = demand i).card : ℝ) =
      ∑ i, indicator demand i (project e ω) := by
  simp [indicator, Finset.sum_boole]

/-- A lower-tail bound on one query with arbitrary actual slot counts and
arbitrary demanded labels, each of probability at least v. -/
theorem categorical_count_lower_tail (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)] (e : (Sigma J) ↪ O)
    (demand : (i : I) → J i → L) (m : ℕ) (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hsize : ∀ i, Fintype.card (J i) ≤ m)
    (hmin : ∀ i j, v ≤ (ν (e ⟨i,j⟩)).real {demand i j}) :
    (categoricalMeasure ν).real
      {ω | ((Finset.univ.filter fun i => project e ω i = demand i).card : ℝ) ≤
        (Fintype.card I : ℝ)*v^m/2} ≤
      Real.exp (-((Fintype.card I : ℝ)*v^m)/8) := by
  have hraw := lower_bound_half_mean_lower_tail (packedMeasure ν e)
    (indicator demand) (candidateProbability ν e demand)
    (candidateProbability_nonneg ν e demand) (candidateProbability_le_one ν e demand)
    (fun i w => by unfold indicator; split_ifs <;> simp)
    (integral_indicator ν e demand)
    (iIndepFun_pi (X := fun i x => if x = demand i then (1 : ℝ) else 0)
      (fun _ => by fun_prop))
    (v^m) (fun i => candidateProbability_ge_pow ν e demand i m v hv0 hv1
      (hsize i) (hmin i))
  rw [← (project_measurePreserving ν e).measureReal_preimage (by measurability)] at hraw
  simpa only [Set.preimage_ofPred_eq, count_eq_sum_indicator] using hraw

/-- Numerical support contains both members of every used inverse orbit. -/
def support [DecidableEq K] (e : (Sigma J) ↪ O) (place : O × Bool ↪ K) (i : I) :
    Finset K :=
  Finset.univ.image (fun jb : J i × Bool => place (e ⟨i,jb.1⟩,jb.2))

omit [Fintype O] [Fintype I] in
theorem support_pairwise [DecidableEq K] (e : (Sigma J) ↪ O)
    (place : O × Bool ↪ K) :
    Pairwise fun i j : I => Disjoint (support e place i) (support e place j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hi hj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hj
  have he := place.injective (ha.trans hb.symm)
  have hp := e.injective (congrArg Prod.fst he)
  exact hij (congrArg Sigma.fst hp)

omit [Fintype O] [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- On every sample, each numerical forbidden coordinate can destroy at most
one successful candidate. F is chosen after the whole sample is known. -/
theorem adaptive_avoidance [DecidableEq K] (e : (Sigma J) ↪ O)
    (place : O × Bool ↪ K) (demand : (i : I) → J i → L) (ω : O → L)
    (F : Finset K)
    (hF : F.card < (Finset.univ.filter fun i => project e ω i = demand i).card) :
    ∃ i, project e ω i = demand i ∧ Disjoint (support e place i) F := by
  obtain ⟨i, hi, hd⟩ := EndpointBlockAvailability.exists_disjoint_of_card_lt
    (Finset.univ.filter fun i => project e ω i = demand i) (support e place)
    (fun i _ j _ hij => support_pairwise e place hij) F hF
  exact ⟨i, (Finset.mem_filter.mp hi).2, hd⟩

end OneQuery

section Queries

variable {Q O L K : Type*} [Fintype Q] [Fintype O] [Fintype L]
    [MeasurableSpace L] [MeasurableSingletonClass L] [DecidableEq K]
    {I : Q → Type*} [∀ q, Fintype (I q)]
    {J : (q : Q) → I q → Type*} [∀ q i, Fintype (J q i)]

/-- The whole geometric support may include additional orbits on which no
label is requested. Sampling uses J; numerical avoidance uses fullSupport. -/
def FullSupportEvent (e : (q : Q) → (Sigma (J q)) ↪ O)
    (fullSupport : (q : Q) → I q → Finset K)
    (demand : (q : Q) → (i : I q) → J q i → L)
    (threshold : Q → ℝ) (ω : O → L) : Prop :=
  ∀ q, threshold q ≤
      ((Finset.univ.filter fun i => project (e q) ω i = demand q i).card : ℝ) ∧
    ∀ F : Finset K,
      F.card < (Finset.univ.filter fun i => project (e q) ω i = demand q i).card →
      ∃ i, project (e q) ω i = demand q i ∧ Disjoint (fullSupport q i) F

omit [Fintype Q] [Fintype O] [Fintype L]
    [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- Numerical deletion is controlled by the disjointness of the entire
candidate supports, including orbits that carry no label requirement. -/
theorem full_support_adaptive_avoidance
    (e : (q : Q) → (Sigma (J q)) ↪ O)
    (fullSupport : (q : Q) → I q → Finset K)
    (hdisj : ∀ q, Pairwise fun i j => Disjoint (fullSupport q i) (fullSupport q j))
    (demand : (q : Q) → (i : I q) → J q i → L)
    (ω : O → L) (q : Q) (F : Finset K)
    (hF : F.card < (Finset.univ.filter fun i => project (e q) ω i = demand q i).card) :
    ∃ i, project (e q) ω i = demand q i ∧ Disjoint (fullSupport q i) F := by
  obtain ⟨i, hi, hd⟩ := EndpointBlockAvailability.exists_disjoint_of_card_lt
    (Finset.univ.filter fun i => project (e q) ω i = demand q i) (fullSupport q)
    (fun i _ j _ hij => hdisj q hij) F hF
  exact ⟨i, (Finset.mem_filter.mp hi).2, hd⟩

/-- General common-event theorem. Slot counts and label probabilities may
vary; the deterministic whole supports are pairwise disjoint inside a query.
There is no assumption between different queries and no good-event premise. -/
theorem categorical_full_support_event_tail (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)]
    (e : (q : Q) → (Sigma (J q)) ↪ O)
    (fullSupport : (q : Q) → I q → Finset K)
    (hdisj : ∀ q, Pairwise fun i j => Disjoint (fullSupport q i) (fullSupport q j))
    (demand : (q : Q) → (i : I q) → J q i → L)
    (m : ℕ) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hsize : ∀ q i, Fintype.card (J q i) ≤ m)
    (hmin : ∀ q i j, v ≤ (ν (e q ⟨i,j⟩)).real {demand q i j})
    (threshold : Q → ℝ)
    (hthreshold : ∀ q, threshold q ≤ (Fintype.card (I q) : ℝ)*v^m/2) :
    (categoricalMeasure ν).real
      {ω | ¬ FullSupportEvent e fullSupport demand threshold ω} ≤
      ∑ q, Real.exp (-((Fintype.card (I q) : ℝ)*v^m)/8) := by
  have htail (q : Q) : (categoricalMeasure ν).real
      {ω | ((Finset.univ.filter fun i => project (e q) ω i = demand q i).card : ℝ) <
        threshold q} ≤ Real.exp (-((Fintype.card (I q) : ℝ)*v^m)/8) := by
    apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
      (categorical_count_lower_tail ν (e q) (demand q) m v hv0 hv1 (hsize q) (hmin q))
    intro ω hω
    exact hω.le.trans (hthreshold q)
  have hsub : {ω | ¬ FullSupportEvent e fullSupport demand threshold ω} ⊆
      ⋃ q : Q,
        {ω | ((Finset.univ.filter fun i => project (e q) ω i = demand q i).card : ℝ) <
          threshold q} := by
    intro ω hω
    by_contra hn
    apply hω
    intro q
    constructor
    · by_contra hq
      exact hn (Set.mem_iUnion.mpr ⟨q, lt_of_not_ge hq⟩)
    · exact fun F hF => full_support_adaptive_avoidance e fullSupport hdisj demand ω q F hF
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_iUnion_fintype_le _).trans
      (Finset.sum_le_sum fun q _ => htail q))

/-- Every query has linearly many successful candidates, and every later F
smaller than its actual successful count is avoided by an entire candidate. -/
theorem categorical_full_support_linear_event_tail (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)]
    (e : (q : Q) → (Sigma (J q)) ↪ O)
    (fullSupport : (q : Q) → I q → Finset K)
    (hdisj : ∀ q, Pairwise fun i j => Disjoint (fullSupport q i) (fullSupport q j))
    (demand : (q : Q) → (i : I q) → J q i → L)
    (m : ℕ) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hsize : ∀ q i, Fintype.card (J q i) ≤ m)
    (hmin : ∀ q i j, v ≤ (ν (e q ⟨i,j⟩)).real {demand q i j})
    (n : ℕ) (α : ℝ) (hlinear : ∀ q, α*n ≤ (Fintype.card (I q) : ℝ)) :
    (categoricalMeasure ν).real
      {ω | ¬ FullSupportEvent e fullSupport demand (fun _ => α*n*v^m/2) ω} ≤
      (Fintype.card Q : ℝ)*Real.exp (-(α*n*v^m)/8) := by
  apply (categorical_full_support_event_tail ν e fullSupport hdisj demand m v
    hv0 hv1 hsize hmin (fun _ => α*n*v^m/2)
    (fun q => by nlinarith [mul_le_mul_of_nonneg_right (hlinear q) (pow_nonneg hv0 m)])).trans
  calc
    _ ≤ ∑ _q : Q, Real.exp (-(α*n*v^m)/8) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (hlinear q) (pow_nonneg hv0 m)]
    _ = _ := by simp

/-- If only a positive lower bound v is supplied, clipping it at one makes
the statement valid even for entirely empty demand sets. For a genuine
probability density v≤1 this is exactly the preceding theorem. -/
theorem categorical_full_support_linear_event_tail_clipped (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)]
    (e : (q : Q) → (Sigma (J q)) ↪ O)
    (fullSupport : (q : Q) → I q → Finset K)
    (hdisj : ∀ q, Pairwise fun i j => Disjoint (fullSupport q i) (fullSupport q j))
    (demand : (q : Q) → (i : I q) → J q i → L)
    (m : ℕ) (v : ℝ) (hv : 0 ≤ v)
    (hsize : ∀ q i, Fintype.card (J q i) ≤ m)
    (hmin : ∀ q i j, v ≤ (ν (e q ⟨i,j⟩)).real {demand q i j})
    (n : ℕ) (α : ℝ) (hlinear : ∀ q, α*n ≤ (Fintype.card (I q) : ℝ)) :
    (categoricalMeasure ν).real
      {ω | ¬ FullSupportEvent e fullSupport demand (fun _ => α*n*(min v 1)^m/2) ω} ≤
      (Fintype.card Q : ℝ)*Real.exp (-(α*n*(min v 1)^m)/8) := by
  exact categorical_full_support_linear_event_tail ν e fullSupport hdisj demand m
    (min v 1) (le_min hv (by norm_num)) (min_le_right _ _) hsize
    (fun q i j => (min_le_left _ _).trans (hmin q i j)) n α hlinear

/-- One event, followed by every query, followed by every forbidden numerical
set smaller than the actual successful count for that query. -/
def SimultaneousEvent (e : (q : Q) → (Sigma (J q)) ↪ O)
    (place : O × Bool ↪ K) (demand : (q : Q) → (i : I q) → J q i → L)
    (threshold : Q → ℝ) (ω : O → L) : Prop :=
  ∀ q, threshold q ≤
      ((Finset.univ.filter fun i => project (e q) ω i = demand q i).card : ℝ) ∧
    ∀ F : Finset K,
      F.card < (Finset.univ.filter fun i => project (e q) ω i = demand q i).card →
      ∃ i, project (e q) ω i = demand q i ∧ Disjoint (support (e q) place i) F

/-- Finite union over queries, with no independence or disjointness required
between different queries. The conclusion is a property of the common sample. -/
theorem categorical_simultaneous_event_tail (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)]
    (e : (q : Q) → (Sigma (J q)) ↪ O) (place : O × Bool ↪ K)
    (demand : (q : Q) → (i : I q) → J q i → L)
    (m : ℕ) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hsize : ∀ q i, Fintype.card (J q i) ≤ m)
    (hmin : ∀ q i j, v ≤ (ν (e q ⟨i,j⟩)).real {demand q i j})
    (threshold : Q → ℝ)
    (hthreshold : ∀ q, threshold q ≤ (Fintype.card (I q) : ℝ)*v^m/2) :
    (categoricalMeasure ν).real
      {ω | ¬ SimultaneousEvent e place demand threshold ω} ≤
      ∑ q, Real.exp (-((Fintype.card (I q) : ℝ)*v^m)/8) := by
  have htail (q : Q) : (categoricalMeasure ν).real
      {ω | ((Finset.univ.filter fun i => project (e q) ω i = demand q i).card : ℝ) <
        threshold q} ≤ Real.exp (-((Fintype.card (I q) : ℝ)*v^m)/8) := by
    apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
      (categorical_count_lower_tail ν (e q) (demand q) m v hv0 hv1 (hsize q) (hmin q))
    intro ω hω
    exact hω.le.trans (hthreshold q)
  have hsub : {ω | ¬ SimultaneousEvent e place demand threshold ω} ⊆
      ⋃ q : Q,
        {ω | ((Finset.univ.filter fun i => project (e q) ω i = demand q i).card : ℝ) <
          threshold q} := by
    intro ω hω
    by_contra hn
    apply hω
    intro q
    constructor
    · by_contra hq
      exact hn (Set.mem_iUnion.mpr ⟨q, lt_of_not_ge hq⟩)
    · exact fun F hF => adaptive_avoidance (e q) place (demand q) ω F hF
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_iUnion_fintype_le _).trans
      (Finset.sum_le_sum fun q _ => htail q))

/-- Linear candidate families give a common linear-success event with an
explicit exponentially small error, before every later adaptive F. -/
theorem categorical_linear_event_tail (ν : O → Measure L)
    [∀ o, IsProbabilityMeasure (ν o)]
    (e : (q : Q) → (Sigma (J q)) ↪ O) (place : O × Bool ↪ K)
    (demand : (q : Q) → (i : I q) → J q i → L)
    (m : ℕ) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hsize : ∀ q i, Fintype.card (J q i) ≤ m)
    (hmin : ∀ q i j, v ≤ (ν (e q ⟨i,j⟩)).real {demand q i j})
    (n : ℕ) (α : ℝ) (hlinear : ∀ q, α*n ≤ (Fintype.card (I q) : ℝ)) :
    (categoricalMeasure ν).real
      {ω | ¬ SimultaneousEvent e place demand (fun _ => α*n*v^m/2) ω} ≤
      (Fintype.card Q : ℝ)*Real.exp (-(α*n*v^m)/8) := by
  apply (categorical_simultaneous_event_tail ν e place demand m v hv0 hv1 hsize hmin
    (fun _ => α*n*v^m/2)
    (fun q => by nlinarith [mul_le_mul_of_nonneg_right (hlinear q) (pow_nonneg hv0 m)])).trans
  calc
    _ ≤ ∑ _q : Q, Real.exp (-(α*n*v^m)/8) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (hlinear q) (pow_nonneg hv0 m)]
    _ = _ := by simp

end Queries

end
end AbsorberInputs.PackedAvailability
