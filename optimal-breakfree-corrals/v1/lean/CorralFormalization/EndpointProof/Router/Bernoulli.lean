import CorralFormalization.EndpointProof.Sampling.OriginalReservoir
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Bernoulli reservoir laws and a multiplicative lower tail

This module uses the actual finite Bernoulli product law.  The lower-tail
exponent is proportional to the mean, rather than its square.
-/
namespace EndpointRouter
namespace Bernoulli

open MeasureTheory ProbabilityTheory
open EndpointOriginalReservoir
open scoped BigOperators Classical
noncomputable section

/-- A finite alphabet and index allow all integrability/measurability
conditions below to be discharged from the actual sample space. -/
theorem half_mean_lower_tail {Ω I : Type*} [Fintype Ω] [Fintype I]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbool : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = p) (hindep : iIndepFun X μ) :
    μ.real {ω | (∑ i, X i ω) ≤ (Fintype.card I : ℝ)*p/2} ≤
      Real.exp (-((Fintype.card I : ℝ)*p)/8) := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 2 ≤ (3/4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have he : Real.exp (-Real.log 2) = (1/2 : ℝ) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hmgf (i : I) : mgf (X i) μ (-Real.log 2) = 1-p/2 := by
    have hpoint : (fun ω => Real.exp (-Real.log 2 * X i ω)) =
        (fun ω => 1-X i ω/2) := by
      funext ω
      rcases hbool i ω with h | h <;> norm_num [h,he]
    rw [mgf,hpoint,integral_sub Integrable.of_finite Integrable.of_finite,
      integral_div, hmean]
    simp
  have hsum : mgf (fun ω => ∑ i, X i ω) μ (-Real.log 2) ≤
      Real.exp (-((Fintype.card I : ℝ)*p)/2) := by
    have hfun : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by ext ω; simp
    rw [← hfun,hindep.mgf_sum (fun i => measurable_of_countable (X i)) Finset.univ]
    simp_rw [hmgf]
    calc
      (∏ _i : I, (1-p/2)) ≤ ∏ _i : I, Real.exp (-p/2) := by
        apply Finset.prod_le_prod
        · intro i hi; linarith
        · intro i hi
          have hh := Real.add_one_le_exp (-p/2)
          linarith
      _ = Real.exp (-((Fintype.card I : ℝ)*p)/2) := by
        simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]
        congr 1
        ring
  have htail := measure_le_le_exp_mul_mgf
    (μ := μ) (X := fun ω => ∑ i, X i ω)
    (t := -Real.log 2) ((Fintype.card I : ℝ)*p/2) (by linarith) Integrable.of_finite
  calc
    _ ≤ Real.exp (-(-Real.log 2) * ((Fintype.card I : ℝ)*p/2)) *
        mgf (fun ω => ∑ i, X i ω) μ (-Real.log 2) := htail
    _ ≤ Real.exp (-(-Real.log 2) * ((Fintype.card I : ℝ)*p/2)) *
        Real.exp (-((Fintype.card I : ℝ)*p)/2) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm : 0 ≤ (Fintype.card I : ℝ)*p := mul_nonneg (Nat.cast_nonneg _) hp0
      nlinarith [mul_le_mul_of_nonneg_right hlog hm]

/-- One Bernoulli-u coordinate per label. -/
def measure {O : Type*} [Fintype O] (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Measure (O → Bool) := Measure.pi (fun _ => (coinLaw u hu0 hu1).measure)

instance measure_probability {O : Type*} [Fintype O]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    IsProbabilityMeasure (measure (O := O) u hu0 hu1) := by
  unfold measure
  infer_instance

def blockMeasure {J : Type*} [Fintype J] (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Measure (J → Bool) := measure u hu0 hu1

instance blockMeasure_probability {J : Type*} [Fintype J]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    IsProbabilityMeasure (blockMeasure (J := J) u hu0 hu1) := by
  unfold blockMeasure
  infer_instance

def sampleMeasure {I J : Type*} [Fintype I] [Fintype J]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : Measure (I → J → Bool) :=
  Measure.pi (fun _ => blockMeasure u hu0 hu1)

instance sampleMeasure_probability {I J : Type*} [Fintype I] [Fintype J]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    IsProbabilityMeasure (sampleMeasure (I := I) (J := J) u hu0 hu1) := by
  unfold sampleMeasure blockMeasure
  infer_instance

def project {O I J : Type*} (e : I × J ↪ O) (ω : O → Bool) : I → J → Bool :=
  fun i j => ω (e (i,j))

/-- A deterministic embedding of disjoint candidate requests has exactly
an independent block law under the one source reservoir sample. -/
theorem project_measurePreserving {O I J : Type*}
    [Fintype O] [Fintype I] [Fintype J]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (e : I × J ↪ O) :
    MeasurePreserving (project e) (measure u hu0 hu1) (sampleMeasure u hu0 hu1) := by
  let ν := (coinLaw u hu0 hu1).measure
  have hflat : (Measure.pi (fun _ : O => ν)).map
      (fun ω (ij : I × J) => ω (e ij)) = Measure.pi (fun _ : I × J => ν) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : O => ν) e.injective)
  have hcurry : (Measure.pi (fun _ : I × J => ν)).map
      (MeasurableEquiv.curry I J Bool) = Measure.pi (fun _ : I => Measure.pi (fun _ : J => ν)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : I) (_ : J) => ν))
  refine ⟨by unfold project; fun_prop, ?_⟩
  change (Measure.pi (fun _ : O => ν)).map
    ((MeasurableEquiv.curry I J Bool) ∘ (fun ω (ij : I × J) => ω (e ij))) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),hflat,hcurry]
  rfl

theorem true_singleton (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (coinLaw u hu0 hu1).measure.real {true} = u := by
  simpa [coinLaw,coinWeight,eventMass] using
    (FiniteLaw.real_event (coinLaw u hu0 hu1) (fun b => b = true))

theorem block_true_probability {J : Type*} [Fintype J]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (blockMeasure (J := J) u hu0 hu1).real {fun _ => true} = u^(Fintype.card J) := by
  rw [measureReal_def]
  change (Measure.pi (fun _ : J => (coinLaw u hu0 hu1).measure) {fun _ => true}).toReal = _
  rw [Measure.pi_singleton,ENNReal.toReal_prod]
  simp only [← measureReal_def,true_singleton,Finset.prod_const,Finset.card_univ]

/-- The indicator of all required request bits being true. -/
def indicator {I J : Type*} [Fintype J] (i : I) (ω : I → J → Bool) : ℝ :=
  if ω i = (fun _ => true) then 1 else 0

theorem indicator_mean {I J : Type*} [Fintype I] [Fintype J]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (i : I) :
    ∫ ω : I → J → Bool, indicator i ω ∂sampleMeasure u hu0 hu1 = u^(Fintype.card J) := by
  unfold sampleMeasure indicator
  rw [integral_comp_eval (i := i) (μ := fun _ : I => blockMeasure u hu0 hu1)
    (f := fun x : J → Bool => if x = (fun _ => true) then (1 : ℝ) else 0) (by fun_prop)]
  have hind : (fun x : J → Bool => if x = (fun _ => true) then (1 : ℝ) else 0) =
      Set.indicator {(fun _ : J => true)} (fun _ : J → Bool => (1 : ℝ)) := by
        ext x; simp [Set.indicator_apply]
  rw [hind]
  have hh := integral_indicator_const (μ := blockMeasure (J := J) u hu0 hu1)
    (s := {(fun _ : J => true)}) (1 : ℝ) (measurableSet_singleton _)
  simpa only [smul_eq_mul,mul_one,block_true_probability] using hh

theorem block_half_tail {I J : Type*} [Fintype I] [Fintype J]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (sampleMeasure (I := I) (J := J) u hu0 hu1).real
      {ω | (∑ i, indicator i ω) ≤ (Fintype.card I : ℝ)*u^(Fintype.card J)/2} ≤
      Real.exp (-((Fintype.card I : ℝ)*u^(Fintype.card J))/8) := by
  apply half_mean_lower_tail _ _ _ (pow_nonneg hu0 _) (pow_le_one₀ hu0 hu1)
  · intro i ω
    unfold indicator
    split_ifs <;> simp
  · exact indicator_mean u hu0 hu1
  · exact iIndepFun_pi (X := fun _i x => if x = (fun _ : J => true) then (1 : ℝ) else 0)
      (fun _ => by fun_prop)

/-- The sharp mean-scale Chernoff bound transported to one actual source
sample.  Different query embeddings may overlap arbitrarily. -/
theorem shared_half_tail {O I J : Type*} [Fintype O] [Fintype I] [Fintype J]
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (e : I × J ↪ O) :
    (measure u hu0 hu1).real
      {ω | (∑ i, indicator i (project e ω)) ≤ (Fintype.card I : ℝ)*u^(Fintype.card J)/2} ≤
      Real.exp (-((Fintype.card I : ℝ)*u^(Fintype.card J))/8) := by
  have heq := (project_measurePreserving u hu0 hu1 e).measureReal_preimage
    (s := {w : I → J → Bool | (∑ i, indicator i w) ≤
      (Fintype.card I : ℝ)*u^(Fintype.card J)/2}) (by measurability)
  have ht := block_half_tail (I := I) (J := J) u hu0 hu1
  rw [← heq] at ht
  exact ht

end
end Bernoulli
end EndpointRouter
