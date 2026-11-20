import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
Finite-product bounded differences, proved by integrating out one coordinate
at a time. The factors may have different laws. No independence of events
indexed by points of the product is required.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace EndpointFiniteProductConcentration

noncomputable section

/-- Hoeffding's lemma in the form needed for a single finite coordinate.
The hypothesis is a diameter, so the interval need not be supplied. -/
theorem hasSubgaussianMGF_of_diameter
    {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : A → ℝ) (c : ℝ≥0) (hc : ∀ a b, |f a - f b| ≤ c) :
    HasSubgaussianMGF (fun a => f a - ∫ a, f a ∂μ) ((c / 2)^2) μ := by
  classical
  let W := Finset.univ.image f
  have hW : W.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  let a := W.min' hW
  obtain ⟨a₀, _, ha₀⟩ := Finset.mem_image.mp (Finset.min'_mem W hW)
  have hbound (x : A) : f x ∈ Set.Icc a (a+c) := by
    have hlo : a ≤ f x := Finset.min'_le W (f x) (Finset.mem_image.mpr
      ⟨x,Finset.mem_univ _,rfl⟩)
    have hhi := (abs_le.mp (hc x a₀)).2
    rw [ha₀] at hhi
    exact ⟨hlo,by linarith⟩
  have h := hasSubgaussianMGF_of_mem_Icc (μ := μ)
    ((measurable_of_countable f).aemeasurable) (ae_of_all μ hbound)
  convert h using 1
  simp [Real.nnnorm_of_nonneg c.coe_nonneg]

/-- Tensorization step: a uniformly sub-Gaussian centered first-coordinate
fiber adds its variance proxy to that of its averaged remaining function. -/
theorem tensorization_step
    {A B : Type*} [Finite A] [Finite B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (c d : ℝ≥0)
    (hfiber : ∀ b, HasSubgaussianMGF
      (fun a => f (a,b) - ∫ a, f (a,b) ∂μ) c μ)
    (hmean : HasSubgaussianMGF
      (fun b => (∫ a, f (a,b) ∂μ) - ∫ b, ∫ a, f (a,b) ∂μ ∂ν) d ν) :
    HasSubgaussianMGF
      (fun w => f w - ∫ w, f w ∂(μ.prod ν)) (c+d) (μ.prod ν) := by
  have hm : (∫ w, f w ∂(μ.prod ν)) = ∫ b, ∫ a, f (a,b) ∂μ ∂ν :=
    integral_prod_symm f Integrable.of_finite
  constructor
  · intro t
    exact Integrable.of_finite
  · intro t
    simp only [mgf, hm]
    rw [integral_prod_symm _ Integrable.of_finite]
    let g : B → ℝ := fun b => ∫ a, f (a,b) ∂μ
    let m := ∫ b, g b ∂ν
    have hfactor (b : B) :
        (∫ a, Real.exp (t * (f (a,b) - m)) ∂μ) =
          Real.exp (t * (g b-m)) *
            (∫ a, Real.exp (t * (f (a,b)-g b)) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all μ (fun a => by dsimp only; rw [← Real.exp_add]; congr 1; ring)
    change (∫ b, ∫ a, Real.exp (t * (f (a,b)-m)) ∂μ ∂ν) ≤ _
    simp_rw [hfactor]
    calc
      _ ≤ ∫ b, Real.exp (t * (g b-m)) * Real.exp (c * t^2 / 2) ∂ν := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro b
        exact mul_le_mul_of_nonneg_left ((hfiber b).mgf_le t) (Real.exp_nonneg _)
      _ = (∫ b, Real.exp (t * (g b-m)) ∂ν) * Real.exp (c * t^2 / 2) :=
        integral_mul_const _ _
      _ ≤ Real.exp (d * t^2 / 2) * Real.exp (c * t^2 / 2) := by
        exact mul_le_mul_of_nonneg_right (hmean.mgf_le t) (Real.exp_nonneg _)
      _ = Real.exp ((↑(c+d)) * t^2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

/-- The coordinate oscillation hypothesis, stated symmetrically for any two
points agreeing away from one coordinate. -/
def CoordinateBoundedDifferences {ι A : Type*} (f : (ι → A) → ℝ) (c : ι → ℝ≥0) : Prop :=
  ∀ (i : ι) (x y : ι → A), (∀ j, j ≠ i → x j = y j) → |f x-f y| ≤ c i

/-- McDiarmid's MGF estimate for an arbitrary finite alphabet and a finite
number of independent coordinates, with possibly different factor laws. -/
theorem fin_hasSubgaussianMGF
    {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (n : ℕ) :
    ∀ (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
      (c : Fin n → ℝ≥0) (f : (Fin n → A) → ℝ),
      CoordinateBoundedDifferences f c →
      HasSubgaussianMGF (fun x => f x - ∫ x, f x ∂(Measure.pi μ))
        (∑ i, (c i / 2)^2) (Measure.pi μ) := by
  classical
  induction n with
  | zero =>
    intro μ hμ c f hd
    have hf (x : Fin 0 → A) : f x = f (fun i => Fin.elim0 i) :=
      congrArg f (funext (fun i => Fin.elim0 i))
    simp_rw [hf]
    simp
  | succ n ih =>
    intro μ hμ c f hd
    let ν : Measure (Fin n → A) := Measure.pi (fun i => μ i.succ)
    let F : A × (Fin n → A) → ℝ := fun w => f (Fin.cons w.1 w.2)
    let g : (Fin n → A) → ℝ := fun w => ∫ a, F (a,w) ∂μ 0
    have hfiber (w : Fin n → A) : HasSubgaussianMGF
        (fun a => F (a,w) - ∫ a, F (a,w) ∂μ 0) ((c 0 / 2)^2) (μ 0) := by
      apply hasSubgaussianMGF_of_diameter
      intro a b
      apply hd 0 (Fin.cons a w) (Fin.cons b w)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hj; exact False.elim (hj rfl)
      · intro _; simp
    have hgd : CoordinateBoundedDifferences g (fun i => c i.succ) := by
      intro i x y hxy
      have hab (a : A) : |F (a,x) - F (a,y)| ≤ c i.succ := by
        apply hd i.succ (Fin.cons a x) (Fin.cons a y)
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _; simp
        · intro hj
          simp only [Fin.cons_succ]
          exact hxy j (fun he => hj (congrArg Fin.succ he))
      calc
        |g x-g y| = |∫ a, (F (a,x)-F (a,y)) ∂μ 0| := by
          rw [integral_sub Integrable.of_finite Integrable.of_finite]
        _ ≤ ∫ a, |F (a,x)-F (a,y)| ∂μ 0 := abs_integral_le_integral_abs
        _ ≤ ∫ _a : A, (c i.succ : ℝ) ∂μ 0 :=
          integral_mono Integrable.of_finite Integrable.of_finite hab
        _ = c i.succ := by simp
    have hg := ih (fun i => μ i.succ) (fun i => c i.succ) g hgd
    have hF := tensorization_step (μ 0) ν F ((c 0/2)^2)
      (∑ i : Fin n, (c i.succ/2)^2) hfiber hg
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0
    have he : MeasurePreserving e (Measure.pi μ) ((μ 0).prod ν) := by
      simpa [e, ν, Fin.zero_succAbove] using measurePreserving_piFinSuccAbove μ 0
    have hmap := HasSubgaussianMGF.of_map he.measurable.aemeasurable
      (he.map_eq.symm ▸ hF)
    rw [he.map_eq] at hmap
    have hFe : F ∘ e = f := by
      funext x
      simp [F, e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    have hint : (∫ w, F w ∂((μ 0).prod ν)) = ∫ x, f x ∂(Measure.pi μ) := by
      rw [← he.integral_comp' F]
      exact integral_congr_ae (ae_of_all _ (congrFun hFe))
    have hpt (x : Fin (n+1) → A) : F (e x) = f x := congrFun hFe x
    simpa only [Function.comp_def, hpt, hint, Fin.sum_univ_succ] using hmap

/-- The finite-product bounded-differences estimate, with arbitrary finite
coordinate index. All mathematical premises are the factor probability
laws and the displayed deterministic oscillation bounds. -/
theorem hasSubgaussianMGF
    {ι A : Type*} [Fintype ι] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (c : ι → ℝ≥0) (f : (ι → A) → ℝ) (hd : CoordinateBoundedDifferences f c) :
    HasSubgaussianMGF (fun x => f x - ∫ x, f x ∂(Measure.pi μ))
      (∑ i, (c i / 2)^2) (Measure.pi μ) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => A) e
  have he : MeasurePreserving E (Measure.pi (fun i => μ (e i))) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ e
  have hdF : CoordinateBoundedDifferences (f ∘ E) (fun i => c (e i)) := by
    intro i x y hxy
    apply hd (e i) (E x) (E y)
    intro j hj
    obtain ⟨k,rfl⟩ := e.surjective j
    simp only [E, MeasurableEquiv.piCongrLeft_apply_apply]
    exact hxy k (fun hki => hj (congrArg e hki))
  have hF := fin_hasSubgaussianMGF (Fintype.card ι) (fun i => μ (e i))
    (fun i => c (e i)) (f ∘ E) hdF
  have hint : (∫ x, (f ∘ E) x ∂(Measure.pi (fun i => μ (e i)))) =
      ∫ x, f x ∂(Measure.pi μ) := he.integral_comp' f
  rw [hint] at hF
  have hEs := he.symm E
  have hmap := HasSubgaussianMGF.of_map hEs.measurable.aemeasurable
    (hEs.map_eq.symm ▸ hF)
  simpa only [Function.comp_def, E.apply_symm_apply,
    e.sum_comp (fun i => (c i/2)^2)] using hmap

/-- McDiarmid upper tail for a real nonnegative deviation. The zero-proxy
case uses Mathlib's totalized real division and is still a valid bound. -/
theorem upper_tail
    {ι A : Type*} [Fintype ι] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (c : ι → ℝ≥0) (f : (ι → A) → ℝ) (hd : CoordinateBoundedDifferences f c)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | t ≤ f x - ∫ x, f x ∂(Measure.pi μ)} ≤
      Real.exp (-t^2 / (2 * (∑ i, ((c i / 2)^2 : ℝ≥0) : ℝ))) := by
  simpa only [NNReal.coe_sum] using (hasSubgaussianMGF μ c f hd).measure_ge_le ht

/-- The corresponding lower tail. -/
theorem lower_tail
    {ι A : Type*} [Fintype ι] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (c : ι → ℝ≥0) (f : (ι → A) → ℝ) (hd : CoordinateBoundedDifferences f c)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | t ≤ (∫ x, f x ∂(Measure.pi μ)) - f x} ≤
      Real.exp (-t^2 / (2 * (∑ i, ((c i / 2)^2 : ℝ≥0) : ℝ))) := by
  have h := (hasSubgaussianMGF μ c f hd).neg.measure_ge_le ht
  simpa only [Pi.neg_apply, neg_sub, NNReal.coe_sum] using h

/-- A larger nonnegative variance proxy preserves a sub-Gaussian bound. -/
theorem proxy_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {c d : ℝ≥0} (h : HasSubgaussianMGF f c μ) (hcd : c ≤ d) :
    HasSubgaussianMGF f d μ := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  gcongr

/-- Transport the product estimate to any source whose coordinate-label
map has exactly that product law. This is a law hypothesis, not an
independence assertion about the function's summands. -/
theorem hasSubgaussianMGF_of_measurePreserving
    {ι A Ω : Type*} [Fintype ι] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace Ω]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure Ω) (labels : Ω → ι → A)
    (hlaw : MeasurePreserving labels ν (Measure.pi μ))
    (c : ι → ℝ≥0) (f : (ι → A) → ℝ) (hd : CoordinateBoundedDifferences f c) :
    HasSubgaussianMGF
      (fun ω => f (labels ω) - ∫ ω, f (labels ω) ∂ν)
      (∑ i, (c i/2)^2) ν := by
  have hint : (∫ ω, f (labels ω) ∂ν) = ∫ x, f x ∂(Measure.pi μ) := by
    rw [← hlaw.map_eq]
    exact (integral_map hlaw.measurable.aemeasurable
      (measurable_of_countable f).aestronglyMeasurable).symm
  have h := hasSubgaussianMGF μ c f hd
  rw [← hlaw.map_eq] at h
  have hm := HasSubgaussianMGF.of_map hlaw.measurable.aemeasurable h
  rw [hlaw.map_eq] at hm
  simpa only [Function.comp_def, hint] using hm

end
end EndpointFiniteProductConcentration
