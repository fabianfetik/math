import CorralFormalization.EndpointProof.Flow.Tetrahedron.SectionExpectation
import CorralFormalization.EndpointProof.Matching.UniversalCore.BufferMatching

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace EndpointMatching.UniversalCore.Buffer
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointFullProduct EndpointOriginalReservoir
open EndpointBlockAvailability EndpointSharedSample EndpointReservoirAvailability
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G]

abbrev Parameters (G : Type*) := G × G

/-- The three representatives of a zero-sum paired buffer. -/
def coordinate (t : Parameters G) : Fin 3 → G :=
  ![t.1, t.2, -t.1-t.2]

/-- Six linear forms whose nonvanishing guarantees distinct nonzero
inverse orbits for the three representatives. -/
def forbiddenForm (i : Fin 6) (t : Parameters G) : G :=
  ![t.1,t.2,t.1+t.2,t.1-t.2,t.1+t.1+t.2,t.1+t.2+t.2] i

def freeCoordinate (i : Fin 6) (t : Parameters G) : G :=
  ![t.2,t.1,t.1,t.1,t.1,t.2] i

def recover (i : Fin 6) (h w : G) : Parameters G :=
  ![(h,w),(w,h),(w,h-w),(w,w-h),(w,h-w-w),(h-w-w,w)] i

omit [Fintype G] in
theorem recover_correct (i : Fin 6) (t : Parameters G) :
    recover i (forbiddenForm i t) (freeCoordinate i t) = t := by
  rcases t with ⟨u,v⟩
  fin_cases i <;> simp [recover, forbiddenForm, freeCoordinate]
  all_goals abel

theorem freeCoordinate_injOn (i : Fin 6) (g : G) :
    Set.InjOn (freeCoordinate i)
      (↑((Finset.univ : Finset (Parameters G)).filter (fun t => forbiddenForm i t = g)) :
        Set (Parameters G)) := by
  intro t ht u hu he
  have ht' := (Finset.mem_filter.mp ht).2
  have hu' := (Finset.mem_filter.mp hu).2
  calc
    t = recover i (forbiddenForm i t) (freeCoordinate i t) := (recover_correct i t).symm
    _ = recover i (forbiddenForm i u) (freeCoordinate i u) := by rw [ht',hu',he]
    _ = u := recover_correct i u

theorem forbiddenForm_fiber_card_le (i : Fin 6) (g : G) :
    ((Finset.univ : Finset (Parameters G)).filter (fun t => forbiddenForm i t = g)).card ≤
      Fintype.card G := by
  have hc := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Parameters G)).filter (fun t => forbiddenForm i t = g))
    (t := (Finset.univ : Finset G)) (freeCoordinate i)
    (by intro t ht; simp) (freeCoordinate_injOn i g)
  simpa using hc

def GeometricallyValid (t : Parameters G) : Prop :=
  (∀ i : Fin 3, coordinate t i ≠ 0) ∧
  (∀ i j : Fin 3, i < j → coordinate t i ≠ coordinate t j ∧
    coordinate t i ≠ -coordinate t j)

omit [Fintype G] in
theorem valid_of_forbiddenForms_nonzero (t : Parameters G)
    (h : ∀ i : Fin 6, forbiddenForm i t ≠ 0) : GeometricallyValid t := by
  rcases t with ⟨u,v⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp only [forbiddenForm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue] at h0 h1 h2 h3 h4 h5
  have hc : -u-v ≠ 0 := by
    intro he
    apply h2
    calc
      u+v = -(-u-v) := by abel
      _ = 0 := by rw [he, neg_zero]
  have huv : u ≠ v := sub_ne_zero.mp h3
  have hunv : u ≠ -v := by
    intro he
    apply h2
    calc
      u+v = u-(-v) := by abel
      _ = 0 := sub_eq_zero.mpr he
  have huc : u ≠ -u-v := by
    intro he
    apply h4
    calc
      u+u+v = u-(-u-v) := by abel
      _ = 0 := sub_eq_zero.mpr he
  have hunc : u ≠ -(-u-v) := by
    intro he
    apply h1
    calc
      v = -(-u-v)-u := by abel
      _ = 0 := sub_eq_zero.mpr he.symm
  have hvc : v ≠ -u-v := by
    intro he
    apply h5
    calc
      u+v+v = v-(-u-v) := by abel
      _ = 0 := sub_eq_zero.mpr he
  have hvnc : v ≠ -(-u-v) := by
    intro he
    apply h0
    calc
      u = -(-u-v)-v := by abel
      _ = 0 := sub_eq_zero.mpr he.symm
  constructor
  · intro i
    fin_cases i <;> simp_all [coordinate]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [coordinate]

def invalidParameters : Finset (Parameters G) :=
  Finset.univ.biUnion (fun i : Fin 6 => Finset.univ.filter (fun t => forbiddenForm i t = 0))

theorem invalidParameters_card_le :
    (invalidParameters (G := G)).card ≤ 6 * Fintype.card G := by
  calc
    _ ≤ ∑ i : Fin 6,
        ((Finset.univ : Finset (Parameters G)).filter (fun t => forbiddenForm i t = 0)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 6, Fintype.card G :=
      Finset.sum_le_sum (fun i _ => forbiddenForm_fiber_card_le i 0)
    _ = _ := by simp

def validParameters : Finset (Parameters G) := Finset.univ.filter GeometricallyValid

theorem validParameters_card_lower :
    (Fintype.card G)^2 - 6 * Fintype.card G ≤ (validParameters (G := G)).card := by
  have hsub : (Finset.univ : Finset (Parameters G)) \ invalidParameters ⊆ validParameters := by
    intro t ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, valid_of_forbiddenForms_nonzero t ?_⟩
    intro i hi
    have hbad : t ∈ invalidParameters := Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    exact (Finset.mem_sdiff.mp ht).2 hbad
  have hsplit := Finset.card_sdiff_add_card_inter
    (Finset.univ : Finset (Parameters G)) (invalidParameters (G := G))
  have hbad := invalidParameters_card_le (G := G)
  have hle := Finset.card_le_card hsub
  have huniv : (Finset.univ : Finset (Parameters G)).card = (Fintype.card G)^2 := by
    simp [Parameters, Fintype.card_prod, pow_two]
  have hinter : ((Finset.univ : Finset (Parameters G)) ∩ invalidParameters).card =
      (invalidParameters (G := G)).card := by simp
  rw [huniv,hinter] at hsplit
  omega

omit [Fintype G] in
theorem valid_pair (t : Parameters G) (h : GeometricallyValid t)
    (i j : Fin 3) (hij : i ≠ j) :
    coordinate t i ≠ coordinate t j ∧ coordinate t i ≠ -coordinate t j := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact h.2 i j hlt
  · have hp := h.2 j i hgt
    constructor
    · exact hp.1.symm
    · intro he
      apply hp.2
      simpa using (congrArg Neg.neg he).symm

def orbitPoint (hodd : Odd (Fintype.card G))
    (t : Parameters G) (hv : GeometricallyValid t) (i : Fin 3) : OddOrbit G × Bool :=
  Classical.choose (orbitPlace_covers_nonzero hodd (hv.1 i))

theorem orbitPoint_spec (hodd : Odd (Fintype.card G))
    (t : Parameters G) (hv : GeometricallyValid t) (i : Fin 3) :
    orbitPlace (orbitPoint hodd t hv i) = coordinate t i :=
  Classical.choose_spec (orbitPlace_covers_nonzero hodd (hv.1 i))

theorem orbitPoint_injective (hodd : Odd (Fintype.card G))
    (t : Parameters G) (hv : GeometricallyValid t) :
    Function.Injective (fun i => (orbitPoint hodd t hv i).1) := by
  intro i j he
  by_contra hij
  have hp := valid_pair t hv i j hij
  have hi := orbitPoint_spec hodd t hv i
  have hj := orbitPoint_spec hodd t hv j
  let oi := orbitPoint hodd t hv i
  let oj := orbitPoint hodd t hv j
  have he' : oi.1 = oj.1 := he
  have hsign : orbitPlace oi = orbitPlace oj ∨ orbitPlace oi = -orbitPlace oj := by
    rcases oi with ⟨o,b⟩
    rcases oj with ⟨o',c⟩
    dsimp at he'
    subst o'
    exact EndpointMatching.Tetrahedron.same_orbit_coordinates o b c
  rcases hsign with hs | hs
  · exact hp.1 (hi.symm.trans (hs.trans hj))
  · exact hp.2 (hi.symm.trans (hs.trans (congrArg Neg.neg hj)))

def orbitEmbedding (hodd : Odd (Fintype.card G))
    (t : Parameters G) (hv : GeometricallyValid t) : Unit × Fin 3 ↪ OddOrbit G where
  toFun := fun k => (orbitPoint hodd t hv k.2).1
  inj' := by
    intro x y he
    have hxy := orbitPoint_injective hodd t hv he
    cases x with | mk x i =>
      cases y with | mk y j =>
        cases x; cases y
        simp_all

def demand (_ : Unit) (i : Fin 3) : Label := encodeChild (some (i,true))

theorem demand_probability (p τ : ℝ≥0) :
    successProbability p τ (demand ()) = (τ : ℝ)^3 := by
  norm_num [successProbability, demand, encodeChild, labelWeights, Fin.prod_univ_succ]
  ring

theorem coordinate_Q_iff_encoded (hodd : Odd (Fintype.card G))
    (t : Parameters G) (hv : GeometricallyValid t) (ω : FullSample G) (i : Fin 3) :
    ReservoirVertex ω true (i, coordinate t i) ↔
      fullLabels ω ((orbitPoint hodd t hv i).1) = demand () i := by
  let op := orbitPoint hodd t hv i
  have hcoord : orbitPlace op = coordinate t i := orbitPoint_spec hodd t hv i
  have hlabel : fullLabels ω op.1 = demand () i ↔
      childLabel ((regroup ω).1 op.1) = some (i,true) := by
    change encodeChild (childLabel ((regroup ω).1 op.1)) = encodeChild (some (i,true)) ↔ _
    exact encodeChild_bijective.injective.eq_iff
  rw [hlabel]
  constructor
  · rintro ⟨o,side,ho,hl⟩
    have he : (o,side) = op := orbitPlace.injective (ho.trans hcoord.symm)
    have hfirst : o = op.1 := congrArg Prod.fst he
    simpa [hfirst] using hl
  · intro hl
    exact ⟨op.1,op.2,hcoord,hl⟩

theorem three_labels_probability (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) :
    (sampleMeasure (I := Unit) (J := Fin 3) p τ h).real
      {w | w () = demand ()} = (τ : ℝ)^3 := by
  have hI := integral_successIndicator (I := Unit) (J := Fin 3) p τ h demand ()
  have hfun : successIndicator demand () =
      Set.indicator {w : Unit → Fin 3 → Label | w () = demand ()} 1 := by
    funext w
    simp [successIndicator, Set.indicator_apply]
  rw [hfun, integral_indicator_one (by measurability)] at hI
  exact hI.trans (demand_probability p τ)

/-- In the actual shared augmentation, a geometrically valid buffer obtains
the prescribed Q labels on its three distinct inverse orbits with probability τ³. -/
theorem valid_buffer_probability (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (t : Parameters G) (hv : GeometricallyValid t) :
    (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ∀ i : Fin 3, ReservoirVertex ω true (i, coordinate t i)} = (τ : ℝ)^3 := by
  let e := orbitEmbedding hodd t hv
  let ev : Set (Unit → Fin 3 → Label) := {w | w () = demand ()}
  have hevent : {ω : FullSample G | ∀ i : Fin 3, ReservoirVertex ω true (i, coordinate t i)} =
      (fun ω => project e (fullLabels ω)) ⁻¹' ev := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro hlabels
      funext i
      change fullLabels ω ((orbitPoint hodd t hv i).1) = demand () i
      exact (coordinate_Q_iff_encoded hodd t hv ω i).mp (hlabels i)
    · intro hlabels i
      apply (coordinate_Q_iff_encoded hodd t hv ω i).mpr
      have hi := congrFun hlabels i
      change fullLabels ω ((orbitPoint hodd t hv i).1) = demand () i at hi
      exact hi
  have hp := (project_measurePreserving (I := Unit) (J := Fin 3) p τ h e).comp
    (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
  rw [hevent]
  change (fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab).real
    ((project e ∘ fullLabels) ⁻¹' ev) = (τ : ℝ)^3
  rw [hp.measureReal_preimage (by measurability)]
  exact three_labels_probability p τ h

/-- Successful valid parameter pairs in the one actual Q reservoir. -/
def goodCandidates (Q : Vertex G → Prop) : Finset (Parameters G) :=
  validParameters.filter (fun t => ∀ i : Fin 3, Q (i,coordinate t i))

def candidateIndicator (t : Parameters G) (ω : FullSample G) : ℝ :=
  if ∀ i : Fin 3, ReservoirVertex ω true (i,coordinate t i) then 1 else 0

theorem goodCandidates_card_sum (ω : FullSample G) :
    ((goodCandidates (ReservoirVertex ω true)).card : ℝ) =
      ∑ t ∈ (validParameters : Finset (Parameters G)), candidateIndicator t ω := by
  exact (Finset.sum_boole (R := ℝ)
    (fun t => ∀ i : Fin 3, ReservoirVertex ω true (i,coordinate t i)) validParameters).symm

/-- Exact total-buffer expectation in the original common augmentation.
Success events for different parameter pairs need not be independent. -/
theorem goodCandidates_expectation (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b) :
    (∫ ω : FullSample G, ((goodCandidates (ReservoirVertex ω true)).card : ℝ)
      ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab)) =
      ((validParameters (G := G)).card : ℝ) * (τ : ℝ)^3 := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hfun (t : Parameters G) : candidateIndicator t =
      Set.indicator {ω : FullSample G |
        ∀ i : Fin 3, ReservoirVertex ω true (i,coordinate t i)} 1 := by
    funext ω
    simp [candidateIndicator, Set.indicator_apply]
  have hint (t : Parameters G) : Integrable (candidateIndicator t) μ := by
    rw [hfun]
    exact (integrable_const 1).indicator (by measurability)
  calc
    _ = ∫ ω : FullSample G, ∑ t ∈ (validParameters : Finset (Parameters G)),
        candidateIndicator t ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ goodCandidates_card_sum
    _ = ∑ t ∈ (validParameters : Finset (Parameters G)), ∫ ω, candidateIndicator t ω ∂μ :=
      integral_finsetSum _ (fun t _ => hint t)
    _ = ∑ _t ∈ (validParameters : Finset (Parameters G)), (τ : ℝ)^3 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hv : GeometricallyValid t := (Finset.mem_filter.mp ht).2
      rw [hfun, integral_indicator_one (by measurability)]
      exact valid_buffer_probability hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ t hv
    _ = _ := by simp

theorem validParameters_half (hn : 12 ≤ Fintype.card G) :
    (Fintype.card G)^2 ≤ 2 * (validParameters (G := G)).card := by
  let n := Fintype.card G
  have hn' : 12 ≤ n := hn
  have hle : 6 * n ≤ n^2 := by nlinarith
  have hsum := Nat.sub_add_cancel hle
  have hvalid : n^2 - 6*n ≤ (validParameters (G := G)).card := validParameters_card_lower
  nlinarith

theorem validParameters_three_quarters (hn : 24 ≤ Fintype.card G) :
    3 * (Fintype.card G)^2 ≤ 4 * (validParameters (G := G)).card := by
  let n := Fintype.card G
  have hn' : 24 ≤ n := hn
  have hle : 6 * n ≤ n^2 := by nlinarith
  have hsum := Nat.sub_add_cancel hle
  have hvalid : n^2 - 6*n ≤ (validParameters (G := G)).card := validParameters_card_lower
  nlinarith

/-- For n≥12 the expected successful buffer count is at least
τ³ n²/2; this uses only independence within each individual buffer. -/
theorem goodCandidates_expectation_lower (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hn : 12 ≤ Fintype.card G) :
    (1 / 2 : ℝ) * (τ : ℝ)^3 * (Fintype.card G : ℝ)^2 ≤
      ∫ ω : FullSample G, ((goodCandidates (ReservoirVertex ω true)).card : ℝ)
        ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  rw [goodCandidates_expectation hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ]
  have hhalf : (Fintype.card G : ℝ)^2 ≤ 2 * ((validParameters (G := G)).card : ℝ) := by
    exact_mod_cast validParameters_half (G := G) hn
  have hprod := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ (τ : ℝ)^3 by positivity)
  nlinarith

theorem goodCandidates_expectation_three_quarters (hodd : Odd (Fintype.card G))
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = rho q η*a) (hQ : (τ : ℝ) = rho q η*b)
    (hn : 24 ≤ Fintype.card G) :
    (3 / 4 : ℝ) * (τ : ℝ)^3 * (Fintype.card G : ℝ)^2 ≤
      ∫ ω : FullSample G, ((goodCandidates (ReservoirVertex ω true)).card : ℝ)
        ∂(fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab) := by
  rw [goodCandidates_expectation hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ]
  have hvalid : (3 : ℝ) * (Fintype.card G : ℝ)^2 ≤
      4 * ((validParameters (G := G)).card : ℝ) := by
    exact_mod_cast validParameters_three_quarters (G := G) hn
  have hprod := mul_le_mul_of_nonneg_right hvalid (show 0 ≤ (τ : ℝ)^3 by positivity)
  nlinarith

theorem coordinate_fiber_card_le (i : Fin 3) (g : G) :
    ((Finset.univ : Finset (Parameters G)).filter (fun t => coordinate t i = g)).card ≤
      Fintype.card G := by
  fin_cases i
  · change ((Finset.univ : Finset (Parameters G)).filter (fun t => t.1 = g)).card ≤ _
    have h := forbiddenForm_fiber_card_le (G := G) 0 g
    change ((Finset.univ : Finset (Parameters G)).filter (fun t => t.1 = g)).card ≤ _ at h
    exact h
  · change ((Finset.univ : Finset (Parameters G)).filter (fun t => t.2 = g)).card ≤ _
    have h := forbiddenForm_fiber_card_le (G := G) 1 g
    change ((Finset.univ : Finset (Parameters G)).filter (fun t => t.2 = g)).card ≤ _ at h
    exact h
  · change ((Finset.univ : Finset (Parameters G)).filter (fun t => coordinate t 2 = g)).card ≤ _
    have heq : (Finset.univ : Finset (Parameters G)).filter
        (fun t => coordinate t 2 = g) = Finset.univ.filter (fun t => forbiddenForm 2 t = -g) := by
      ext ⟨u,v⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change -u-v = g ↔ u+v = -g
      have he : -u-v = -(u+v) := by abel
      rw [he, neg_eq_iff_eq_neg]
    rw [heq]
    exact forbiddenForm_fiber_card_le 2 (-g)

def pairSupport (t : Parameters G) : Finset G :=
  (Finset.univ : Finset (Fin 3 × Bool)).image (fun ib =>
    if ib.2 then -coordinate t ib.1 else coordinate t ib.1)

/-- At most 6n parameter pairs use a given inverse orbit. -/
theorem orbit_incidence (z : G) :
    (((Finset.univ : Finset (Parameters G)).filter (fun t => z ∈ pairSupport t)).card : ℝ) ≤
      6 * (Fintype.card G : ℝ) := by
  let D : Finset (Fin 3 × Bool) := Finset.univ
  let hit (ib : Fin 3 × Bool) : Finset (Parameters G) :=
    Finset.univ.filter (fun t =>
      (if ib.2 then -coordinate t ib.1 else coordinate t ib.1) = z)
  have hhit : ∀ ib ∈ D, ((hit ib).card : ℝ) ≤ (Fintype.card G : ℝ) := by
    rintro ⟨i,b⟩ _
    cases b with
    | false =>
      have h := coordinate_fiber_card_le i z
      exact_mod_cast h
    | true =>
      have heq : hit (i,true) = Finset.univ.filter (fun t => coordinate t i = -z) := by
        ext t
        simp only [hit, Finset.mem_filter, ↓reduceIte, neg_eq_iff_eq_neg]
      rw [heq]
      have h := coordinate_fiber_card_le i (-z)
      exact_mod_cast h
  have hsub : (Finset.univ : Finset (Parameters G)).filter (fun t => z ∈ pairSupport t) ⊆
      D.biUnion hit := by
    intro t ht
    have hsupp := (Finset.mem_filter.mp ht).2
    obtain ⟨ib,hib,hval⟩ := Finset.mem_image.mp hsupp
    exact Finset.mem_biUnion.mpr ⟨ib,hib,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hval⟩⟩
  have hD : D.card = 6 := by simp [D, Fintype.card_prod]
  calc
    _ ≤ ((D.biUnion hit).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ ib ∈ D, ((hit ib).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := D) (t := hit))
    _ ≤ ∑ _ib ∈ D, (Fintype.card G : ℝ) := Finset.sum_le_sum hhit
    _ = _ := by simp [hD]

theorem goodCandidates_mem_congr_off_orbit (Q Q' : Vertex G → Prop)
    (z : G) (t : Parameters G)
    (hQeq : ∀ v, v.2 ≠ z → v.2 ≠ -z → (Q v ↔ Q' v))
    (hz : z ∉ pairSupport t) :
    t ∈ goodCandidates Q ↔ t ∈ goodCandidates Q' := by
  have hvQ (i : Fin 3) : Q (i,coordinate t i) ↔ Q' (i,coordinate t i) := by
    apply hQeq
    · intro he
      apply hz
      apply Finset.mem_image.mpr
      exact ⟨(i,false),Finset.mem_univ _,by simpa using he⟩
    · intro he
      apply hz
      apply Finset.mem_image.mpr
      change coordinate t i = -z at he
      exact ⟨(i,true),Finset.mem_univ _,by simp [he]⟩
  have hall : (∀ i : Fin 3, Q (i,coordinate t i)) ↔
      (∀ i : Fin 3, Q' (i,coordinate t i)) := by
    constructor <;> intro h i
    · exact (hvQ i).mp (h i)
    · exact (hvQ i).mpr (h i)
  simp only [goodCandidates, Finset.mem_filter, hall]

def changedCandidates (Q Q' : Vertex G → Prop) : Finset (Parameters G) :=
  (goodCandidates Q \ goodCandidates Q') ∪ (goodCandidates Q' \ goodCandidates Q)

/-- One inverse-orbit change changes the successful buffer count by at
most 6n, as required by the written bounded-differences calculation. -/
theorem goodCandidates_count_change_le (Q Q' : Vertex G → Prop) (z : G)
    (hQeq : ∀ v, v.2 ≠ z → v.2 ≠ -z → (Q v ↔ Q' v)) :
    |((goodCandidates Q).card : ℝ) - ((goodCandidates Q').card : ℝ)| ≤
      6 * (Fintype.card G : ℝ) := by
  let A := goodCandidates Q
  let B := goodCandidates Q'
  let N := 6 * Fintype.card G
  have hchanged : (changedCandidates Q Q').card ≤ N := by
    have hsub : changedCandidates Q Q' ⊆
        (Finset.univ : Finset (Parameters G)).filter (fun t => z ∈ pairSupport t) := by
      intro t ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hz
      have heq := goodCandidates_mem_congr_off_orbit Q Q' z t hQeq hz
      rcases Finset.mem_union.mp ht with ht | ht
      · exact (Finset.mem_sdiff.mp ht).2 (heq.mp (Finset.mem_sdiff.mp ht).1)
      · exact (Finset.mem_sdiff.mp ht).2 (heq.mpr (Finset.mem_sdiff.mp ht).1)
    have hinc := orbit_incidence (G := G) z
    have hn : (((Finset.univ : Finset (Parameters G)).filter
        (fun t => z ∈ pairSupport t)).card) ≤ N := by
      dsimp [N]
      exact_mod_cast hinc
    exact (Finset.card_le_card hsub).trans hn
  have hleft : A.card ≤ B.card + N := by
    have h₁ := Finset.card_sdiff_add_card_inter A B
    have h₂ := Finset.card_sdiff_add_card_inter B A
    have hd := Finset.card_le_card (s := A \ B) (t := changedCandidates Q Q')
      Finset.subset_union_left
    rw [Finset.inter_comm B A] at h₂
    omega
  have hright : B.card ≤ A.card + N := by
    have h₁ := Finset.card_sdiff_add_card_inter A B
    have h₂ := Finset.card_sdiff_add_card_inter B A
    have hd := Finset.card_le_card (s := B \ A) (t := changedCandidates Q Q')
      Finset.subset_union_right
    rw [Finset.inter_comm B A] at h₂
    omega
  have hl' : (A.card : ℝ) ≤ (B.card : ℝ) + 6 * (Fintype.card G : ℝ) := by
    dsimp [N] at hleft; exact_mod_cast hleft
  have hr' : (B.card : ℝ) ≤ (A.card : ℝ) + 6 * (Fintype.card G : ℝ) := by
    dsimp [N] at hright; exact_mod_cast hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem sampled_goodCandidates_count_change_le
    (ω ω' : FullSample G) (o : OddOrbit G)
    (hchild : ∀ o' : OddOrbit G, o' ≠ o →
      childLabel ((regroup ω).1 o') = childLabel ((regroup ω').1 o')) :
    |((goodCandidates (ReservoirVertex ω true)).card : ℝ) -
      ((goodCandidates (ReservoirVertex ω' true)).card : ℝ)| ≤
        6 * (Fintype.card G : ℝ) :=
  goodCandidates_count_change_le (ReservoirVertex ω true) (ReservoirVertex ω' true)
    (orbitPlace (o,false))
    (EndpointMatching.Tetrahedron.sampled_reservoir_agrees_off_orbit ω ω' o hchild)

end
end EndpointMatching.UniversalCore.Buffer
