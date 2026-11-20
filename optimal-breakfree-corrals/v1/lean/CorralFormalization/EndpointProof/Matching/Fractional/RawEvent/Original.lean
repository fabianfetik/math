import CorralFormalization.EndpointProof.Sampling.OriginalLaw
import CorralFormalization.EndpointProof.Probability.FiniteProductConcentration
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Probability.Independence.Integration

/-!
The fractional supplier's raw quantities on the literal original categorical
endpoint and independent colour sample. Regrouping the two existing channels
at each site is a measure-preserving equivalence, not a replacement sample.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ComplexConjugate NNReal

namespace EndpointFractionalRawEvent
open EndpointOriginalReservoir EndpointFullProduct
noncomputable section

abbrev Site := Part × Bool
abbrev SiteSample (G : Type*) := G → Site

def selected (i : Fin 3) (a : Site) : Prop :=
  if i = 0 then a.1 = 0 else if i = 1 then a.1 = 1 else a.2 = true

def bit (i : Fin 3) (a : Site) : ℝ := if selected i a then 1 else 0

theorem bit_nonneg (i : Fin 3) (a : Site) : 0 ≤ bit i a := by unfold bit; split_ifs <;> norm_num
theorem bit_le_one (i : Fin 3) (a : Site) : bit i a ≤ 1 := by unfold bit; split_ifs <;> norm_num
theorem bit_abs_sub_le_one (i : Fin 3) (a b : Site) : |bit i a-bit i b| ≤ 1 := by
  exact abs_le.mpr ⟨by linarith [bit_nonneg i a,bit_le_one i b],
    by linarith [bit_nonneg i b,bit_le_one i a]⟩

def sites {G : Type*} (s : OriginalSample G) : SiteSample G := fun g => (s.1 g,s.2 g)
def unsites {G : Type*} (w : SiteSample G) : OriginalSample G :=
  (fun g => (w g).1, fun g => (w g).2)

@[simp] theorem unsites_sites {G : Type*} (s : OriginalSample G) : unsites (sites s) = s := by
  cases s; rfl
@[simp] theorem sites_unsites {G : Type*} (w : SiteSample G) : sites (unsites w) = w := by
  funext g; exact Prod.eta _

def siteLaw (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) : FiniteLaw Site :=
  (vertexLaw q hq0 hq1).prod (coinLaw q hq0 (by linarith))

variable {G : Type*} [Fintype G] [AddCommGroup G]

def siteMeasure (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) : Measure (SiteSample G) :=
  Measure.pi (fun _ : G => (siteLaw q hq0 hq1).measure)

instance siteMeasure_probability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) :
    IsProbabilityMeasure (siteMeasure (G := G) q hq0 hq1) := by
  unfold siteMeasure; infer_instance

/-- Exact transport from the original categorical process and independent
colour process, including the coordinate zero. -/
theorem sites_measurePreserving (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) :
    MeasurePreserving sites (originalMeasure (G := G) q hq0 hq1)
      (siteMeasure q hq0 hq1) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Part Bool G
  have hp := measurePreserving_arrowProdEquivProdArrow Part Bool G
    (fun _ : G => (vertexLaw q hq0 hq1).measure)
    (fun _ : G => (coinLaw q hq0 (by linarith)).measure)
  have hm := hp.symm e
  unfold siteMeasure siteLaw
  rw [finiteLaw_measure_prod]
  exact hm


/-- The three physical raw sets; endpoint roles are disjoint by construction. -/
def rawSet (s : OriginalSample G) (i : Fin 3) : Finset G :=
  Finset.univ.filter (fun g => selected i (sites s g))

def rawBit (s : OriginalSample G) (i : Fin 3) (g : G) : ℝ := bit i (sites s g)

theorem rawBit_eq (s : OriginalSample G) (i : Fin 3) (g : G) :
    rawBit s i g = if g ∈ rawSet s i then 1 else 0 := by simp [rawBit,rawSet,bit]

/-- Unnormalised Fourier error, with precisely the manuscript convention. -/
def fourierError (q : ℝ) (s : OriginalSample G) (i : Fin 3) (χ : AddChar G ℂ) : ℂ :=
  ∑ g, ((rawBit s i g-q : ℝ) : ℂ) * conj (χ g)

/-- Raw degree at any numerical root, without requiring that root selected.
For a colour root only the nonzero roots will be used. -/
def rawDegree (s : OriginalSample G) (i : Fin 3) (v : G) : ℝ :=
  if i = 0 then ∑ y, rawBit s 1 y * rawBit s 2 (y-v)
  else if i = 1 then ∑ x, rawBit s 0 x * rawBit s 2 (v-x)
  else ∑ x, rawBit s 0 x * rawBit s 1 (x+v)

def siteProductCount (i j : Fin 3) (a b : G → G) (w : SiteSample G) : ℝ :=
  ∑ g, bit i (w (a g)) * bit j (w (b g))

def weightedCenteredSum (q : ℝ) (i : Fin 3) (a : G → ℝ) (w : SiteSample G) : ℝ :=
  ∑ g, (bit i (w g)-q) * a g

private theorem integral_bit_site (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) (i : Fin 3) :
    (∫ a, bit i a ∂(siteLaw q hq0 hq1).measure) = q := by
  have hfun : bit i = Set.indicator {a | selected i a} 1 := by
    funext a; simp [bit,Set.indicator_apply]
  rw [hfun,integral_indicator_one (by measurability),FiniteLaw.real_event]
  fin_cases i <;> simp [siteLaw,FiniteLaw.prod,eventMass,productWeight,
    vertexLaw,vertexWeight,coinLaw,coinWeight,selected,Fintype.sum_prod_type,
    Fin.sum_univ_succ] <;> ring

/-- Each role has Bernoulli-q marginal; this makes no statement about
independence of the different roles. -/
theorem integral_bit_eval (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) (i : Fin 3) (g : G) :
    (∫ w : SiteSample G, bit i (w g) ∂siteMeasure q hq0 hq1) = q := by
  have hp := measurePreserving_eval (fun _ : G => (siteLaw q hq0 hq1).measure) g
  have he : (∫ w : SiteSample G, bit i (w g) ∂siteMeasure q hq0 hq1) =
      ∫ a, bit i a ∂(siteLaw q hq0 hq1).measure := by
    change (∫ w, bit i (w g) ∂Measure.pi (fun _ : G => (siteLaw q hq0 hq1).measure)) = _
    have h := integral_map (μ := siteMeasure q hq0 hq1) hp.measurable.aemeasurable (measurable_of_countable (bit i)).aestronglyMeasurable
    simp only [siteMeasure] at h
    rw [hp.map_eq] at h
    exact h.symm
  exact he.trans (integral_bit_site q hq0 hq1 i)

theorem weightedCenteredSum_expectation (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (i : Fin 3) (a : G → ℝ) :
    (∫ w : SiteSample G, weightedCenteredSum q i a w ∂siteMeasure q hq0 hq1) = 0 := by
  unfold weightedCenteredSum
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_mul_const,integral_sub Integrable.of_finite Integrable.of_finite,
    integral_bit_eval]
  simp

/-- Two distinct original sites are independent, even though endpoint labels
at a single site are categorical. -/
theorem integral_bit_mul_distinct (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (i j : Fin 3) (a b : G) (hab : a ≠ b) :
    (∫ w : SiteSample G, bit i (w a)*bit j (w b) ∂siteMeasure q hq0 hq1) = q^2 := by
  have hi := iIndepFun_pi (μ := fun _ : G => (siteLaw q hq0 hq1).measure)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hij := (hi.indepFun hab).comp (measurable_of_countable (bit i))
    (measurable_of_countable (bit j))
  have h := hij.integral_fun_mul_eq_mul_integral ((measurable_of_countable _).aestronglyMeasurable)
    ((measurable_of_countable _).aestronglyMeasurable)
  change (∫ w, bit i (w a)*bit j (w b) ∂siteMeasure q hq0 hq1) =
    (∫ w, bit i (w a) ∂siteMeasure q hq0 hq1)*(∫ w, bit j (w b) ∂siteMeasure q hq0 hq1) at h
  rw [h]
  rw [integral_bit_eval,integral_bit_eval,pow_two]

/-- At the same site, either endpoint indicator is independent of colour. -/
theorem integral_bit_mul_colour (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (i : Fin 3) (hi : i = 0 ∨ i = 1) (a b : G) :
    (∫ w : SiteSample G, bit i (w a)*bit 2 (w b) ∂siteMeasure q hq0 hq1) = q^2 := by
  by_cases hab : a = b
  · subst b
    have hp := measurePreserving_eval (fun _ : G => (siteLaw q hq0 hq1).measure) a
    have he : (∫ w : SiteSample G, bit i (w a)*bit 2 (w a) ∂siteMeasure q hq0 hq1) =
        ∫ z, bit i z*bit 2 z ∂(siteLaw q hq0 hq1).measure := by
      change (∫ w, bit i (w a)*bit 2 (w a) ∂Measure.pi (fun _ : G => (siteLaw q hq0 hq1).measure)) = _
      have h := integral_map (μ := siteMeasure q hq0 hq1) hp.measurable.aemeasurable
        (measurable_of_countable (fun z => bit i z*bit 2 z)).aestronglyMeasurable
      simp only [siteMeasure] at h
      rw [hp.map_eq] at h
      exact h.symm
    rw [he]
    have hfun : (fun z => bit i z*bit 2 z) =
        Set.indicator {z | selected i z ∧ selected 2 z} (1 : Site → ℝ) := by
      funext z; simp only [bit,Set.indicator_apply]; split_ifs <;> simp_all
    rw [hfun,integral_indicator_one (by measurability),FiniteLaw.real_event]
    rcases hi with rfl | rfl <;> simp [siteLaw,FiniteLaw.prod,eventMass,productWeight,
      vertexLaw,vertexWeight,coinLaw,coinWeight,selected,Fintype.sum_prod_type,
      Fin.sum_univ_succ] <;> ring
  · exact integral_bit_mul_distinct q hq0 hq1 i 2 a b hab

/-- Exact q²n center for all raw endpoint roots and every nonzero colour.
The omission of colour zero is necessary for the categorical endpoint law. -/
theorem rawDegree_expectation (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (i : Fin 3) (v : G) (hv : i = 2 → v ≠ 0) :
    (∫ s : OriginalSample G, rawDegree s i v ∂originalMeasure q hq0 hq1) =
      q^2 * (Fintype.card G : ℝ) := by
  have hp := sites_measurePreserving (G := G) q hq0 hq1
  have hint : (∫ s : OriginalSample G, rawDegree s i v ∂originalMeasure q hq0 hq1) =
      ∫ w : SiteSample G, rawDegree (unsites w) i v ∂siteMeasure q hq0 hq1 := by
    have he : (∫ s : OriginalSample G, rawDegree (unsites (sites s)) i v ∂originalMeasure q hq0 hq1) =
        ∫ w : SiteSample G, rawDegree (unsites w) i v ∂siteMeasure q hq0 hq1 := by
      have h := integral_map (μ := originalMeasure q hq0 hq1) hp.measurable.aemeasurable
        (measurable_of_countable (fun w => rawDegree (unsites w) i v)).aestronglyMeasurable
      rw [hp.map_eq] at h
      exact h.symm
    simpa using he
  rw [hint]
  fin_cases i
  · simp [rawDegree,rawBit]
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    simp_rw [integral_bit_mul_colour q hq0 hq1 1 (Or.inr rfl)]
    simp [mul_comm]
  · simp [rawDegree,rawBit]
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    simp_rw [integral_bit_mul_colour q hq0 hq1 0 (Or.inl rfl)]
    simp [mul_comm]
  · simp [rawDegree,rawBit]
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    have hg (g : G) : g ≠ g+v := by
      intro he; exact hv rfl (add_left_cancel (he.symm.trans (add_zero g).symm))
    simp_rw [integral_bit_mul_distinct q hq0 hq1 0 1 _ _ (hg _)]
    simp [mul_comm]

end
end EndpointFractionalRawEvent
