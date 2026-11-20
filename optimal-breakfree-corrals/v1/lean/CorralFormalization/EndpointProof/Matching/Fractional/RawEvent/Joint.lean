import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Concentration

/-!
One simultaneous Fourier/degree event on the original sample, with a finite
union bound and no independence between role events, root events or Fourier
events. Sizes follow from the trivial character on this same event.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ComplexConjugate NNReal

namespace EndpointFractionalRawEvent
open EndpointOriginalReservoir EndpointFullProduct
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]

def GoodFourier (q ε : ℝ) (s : OriginalSample G) : Prop :=
  ∀ (i : Fin 3) (χ : AddChar G ℂ), ‖fourierError q s i χ‖ ≤ ε*(Fintype.card G : ℝ)

def GoodDegrees (q ρ : ℝ) (s : OriginalSample G) : Prop :=
  ∀ (i : Fin 3) (v : G), (i=2 → v ≠ 0) →
    |rawDegree s i v-q^2*(Fintype.card G : ℝ)| ≤ ρ*(Fintype.card G : ℝ)

def GoodRawEvent (q ρ ε : ℝ) (s : OriginalSample G) : Prop :=
  GoodFourier q ε s ∧ GoodDegrees q ρ s

def rho (q : ℝ) : ℝ := q^2/10000
def epsilon (q : ℝ) : ℝ := q^4/100000
def beta (q : ℝ) : ℝ := q^2/2000

/-- Numerical constants used by the fractional supplier. -/
theorem epsilon_le_rho (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) : epsilon q ≤ rho q := by
  have hq : q^2 ≤ 1 := by nlinarith [sq_nonneg q]
  unfold epsilon rho
  nlinarith [sq_nonneg (q^2),mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hq)]

theorem epsilon_add_rho_le_half_q (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) :
    epsilon q+rho q ≤ q/2 := by
  have he := epsilon_le_rho q hq0 hq1
  have hq : q^2 ≤ q := by nlinarith [mul_nonneg hq0 (by linarith : 0 ≤ 1-q)]
  have hr : rho q ≤ q/4 := by unfold rho; nlinarith
  linarith

theorem q_mul_epsilon_add_rho_le_rho (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) :
    q*(epsilon q+rho q) ≤ rho q := by
  have he := epsilon_le_rho q hq0 hq1
  have hr : 0 ≤ rho q := by unfold rho; positivity
  have hb := mul_le_mul_of_nonneg_left (add_le_add_right he (rho q)) hq0
  nlinarith [mul_nonneg hr (show 0 ≤ 1/2-q by linarith)]

def fractionalRawEvent (q : ℝ) (s : OriginalSample G) : Prop :=
  GoodRawEvent q (rho q) (epsilon q) s

theorem fourierError_re (q : ℝ) (s : OriginalSample G) (i : Fin 3) (χ : AddChar G ℂ) :
    (fourierError q s i χ).re = weightedCenteredSum q i (fun g => (conj (χ g)).re) (sites s) := by
  simp [fourierError,weightedCenteredSum,rawBit,Complex.mul_re]

theorem fourierError_im (q : ℝ) (s : OriginalSample G) (i : Fin 3) (χ : AddChar G ℂ) :
    (fourierError q s i χ).im = weightedCenteredSum q i (fun g => (conj (χ g)).im) (sites s) := by
  simp [fourierError,weightedCenteredSum,rawBit,Complex.mul_im]

/-- The advertised four-tail bound for one unnormalised Fourier coefficient,
including the trivial character. -/
theorem fourierError_tail (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (i : Fin 3) (χ : AddChar G ℂ) :
    (originalMeasure (G := G) q hq0 hq1).real
      {s | ε*(Fintype.card G : ℝ) < ‖fourierError q s i χ‖} ≤
      4*Real.exp (-ε^2*(Fintype.card G : ℝ)/4) := by
  let μ := originalMeasure (G := G) q hq0 hq1
  let t := ε*(Fintype.card G : ℝ)/2
  have hR := weightedCenteredSum_twoSided_tail q hq0 hq1 ε hε i
    (fun g => (conj (χ g)).re) (fun g => by simpa using Complex.abs_re_le_norm (conj (χ g)))
  have hI := weightedCenteredSum_twoSided_tail q hq0 hq1 ε hε i
    (fun g => (conj (χ g)).im) (fun g => by simpa using Complex.abs_im_le_norm (conj (χ g)))
  simp only [← fourierError_re] at hR
  simp only [← fourierError_im] at hI
  have hsub : {s : OriginalSample G | ε*(Fintype.card G : ℝ) < ‖fourierError q s i χ‖} ⊆
      {s | t < |(fourierError q s i χ).re|} ∪ {s | t < |(fourierError q s i χ).im|} := by
    intro s hs
    by_contra hc
    simp only [Set.mem_union,Set.mem_setOf_eq,not_or,not_lt] at hc
    have hn := Complex.norm_le_abs_re_add_abs_im (fourierError q s i χ)
    change ε*(Fintype.card G : ℝ) < ‖fourierError q s i χ‖ at hs
    dsimp [t] at hc
    linarith
  calc
    _ ≤ μ.real ({s | t < |(fourierError q s i χ).re|} ∪ {s | t < |(fourierError q s i χ).im|}) :=
      measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real {s | t < |(fourierError q s i χ).re|}+μ.real {s | t < |(fourierError q s i χ).im|} :=
      measureReal_union_le _ _
    _ ≤ 4*Real.exp (-ε^2*(Fintype.card G : ℝ)/4) := by dsimp [μ,t]; linarith

/-- All three roles and all n characters on the original categorical sample.
No independence between these 3n events is used. -/
theorem goodFourier_failure_probability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (originalMeasure (G := G) q hq0 hq1).real {s | ¬ GoodFourier q ε s} ≤
      12*(Fintype.card G : ℝ)*Real.exp (-ε^2*(Fintype.card G : ℝ)/4) := by
  let μ := originalMeasure (G := G) q hq0 hq1
  let bad : Fin 3 × AddChar G ℂ → Set (OriginalSample G) := fun k =>
    {s | ε*(Fintype.card G : ℝ) < ‖fourierError q s k.1 k.2‖}
  have he : {s : OriginalSample G | ¬ GoodFourier q ε s} = ⋃ k, bad k := by
    ext s; simp [GoodFourier,bad,not_le]
  rw [he]
  calc
    μ.real (⋃ k, bad k) ≤ ∑ k, μ.real (bad k) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin 3 × AddChar G ℂ, 4*Real.exp (-ε^2*(Fintype.card G : ℝ)/4) := by
      apply Finset.sum_le_sum
      intro k _; exact fourierError_tail q hq0 hq1 ε hε k.1 k.2
    _ = 12*(Fintype.card G : ℝ)*Real.exp (-ε^2*(Fintype.card G : ℝ)/4) := by
      simp [Fintype.card_prod,AddChar.card_eq]
      ring

/-- Every numerical endpoint root and every nonzero numerical colour root,
whether selected or not, simultaneously on the original sample. -/
theorem goodDegrees_failure_probability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (originalMeasure (G := G) q hq0 hq1).real {s | ¬ GoodDegrees q ρ s} ≤
      6*(Fintype.card G : ℝ)*Real.exp (-ρ^2*(Fintype.card G : ℝ)/4) := by
  let μ := originalMeasure (G := G) q hq0 hq1
  let bad : Fin 3 × G → Set (OriginalSample G) := fun k =>
    {s | (k.1=2 → k.2 ≠ 0) ∧ ρ*(Fintype.card G : ℝ) <
      |rawDegree s k.1 k.2-q^2*(Fintype.card G : ℝ)|}
  have he : {s : OriginalSample G | ¬ GoodDegrees q ρ s} = ⋃ k, bad k := by
    ext s; simp [GoodDegrees,bad,not_le]
  have hb (k : Fin 3 × G) : μ.real (bad k) ≤ 2*Real.exp (-ρ^2*(Fintype.card G : ℝ)/4) := by
    by_cases hv : k.1=2 → k.2 ≠ 0
    · exact (measureReal_mono (fun _ hs => hs.2) (measure_ne_top μ _)).trans
        (rawDegree_twoSided_tail q hq0 hq1 ρ hρ k.1 k.2 hv)
    · simp [bad,hv,Real.exp_nonneg]
  rw [he]
  calc
    μ.real (⋃ k, bad k) ≤ ∑ k, μ.real (bad k) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin 3 × G, 2*Real.exp (-ρ^2*(Fintype.card G : ℝ)/4) := by
      exact Finset.sum_le_sum (fun k _ => hb k)
    _ = 6*(Fintype.card G : ℝ)*Real.exp (-ρ^2*(Fintype.card G : ℝ)/4) := by
      simp [Fintype.card_prod]
      ring

/-- One joint raw Fourier and degree event; this uses a union bound only. -/
theorem goodRawEvent_failure_probability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) :
    (originalMeasure (G := G) q hq0 hq1).real {s | ¬ GoodRawEvent q ρ ε s} ≤
      12*(Fintype.card G : ℝ)*Real.exp (-ε^2*(Fintype.card G : ℝ)/4)+
      6*(Fintype.card G : ℝ)*Real.exp (-ρ^2*(Fintype.card G : ℝ)/4) := by
  have he : {s : OriginalSample G | ¬ GoodRawEvent q ρ ε s} =
      {s | ¬ GoodFourier q ε s} ∪ {s | ¬ GoodDegrees q ρ s} := by
    ext s
    change ¬ (GoodFourier q ε s ∧ GoodDegrees q ρ s) ↔ ¬ GoodFourier q ε s ∨ ¬ GoodDegrees q ρ s
    tauto
  rw [he]
  exact (measureReal_union_le _ _).trans (add_le_add
    (goodFourier_failure_probability q hq0 hq1 ε hε)
    (goodDegrees_failure_probability q hq0 hq1 ρ hρ))

/-- The paper-shaped common tail. The law requires no odd-order condition. -/
theorem goodRawEvent_common_failure_probability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hερ : ε ≤ ρ) :
    (originalMeasure (G := G) q hq0 hq1).real {s | ¬ GoodRawEvent q ρ ε s} ≤
      18*(Fintype.card G : ℝ)*Real.exp (-ε^2*(Fintype.card G : ℝ)/4) := by
  have h := goodRawEvent_failure_probability (G := G) q hq0 hq1 ρ ε hρ hε
  have he : Real.exp (-ρ^2*(Fintype.card G : ℝ)/4) ≤
      Real.exp (-ε^2*(Fintype.card G : ℝ)/4) := by
    apply Real.exp_le_exp.mpr
    have hs : ε^2 ≤ ρ^2 := (sq_le_sq₀ hε hρ).mpr hερ
    have hn : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hn]
  have hn : (0 : ℝ) ≤ 6*(Fintype.card G : ℝ) := by positivity
  have hb := mul_le_mul_of_nonneg_left he hn
  linarith

/-- For 0<q≤1/2, the exact 18n exp(-q^8 n/(4·10^10)) raw-event bound. -/
theorem fractionalRawEvent_failure_probability (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    (originalMeasure (G := G) q hq0.le hq1).real {s | ¬ fractionalRawEvent q s} ≤
      18*(Fintype.card G : ℝ)*Real.exp (-q^8*(Fintype.card G : ℝ)/(4*10^10)) := by
  have hερ := epsilon_le_rho q hq0.le hq1
  have h := goodRawEvent_common_failure_probability (G := G) q hq0.le hq1
    (rho q) (epsilon q) (by unfold rho; positivity) (by unfold epsilon; positivity) hερ
  have he : -(epsilon q)^2*(Fintype.card G : ℝ)/4 =
      -q^8*(Fintype.card G : ℝ)/(4*10^10) := by unfold epsilon; ring
  simpa only [fractionalRawEvent,he] using h

/-- The trivial Fourier character controls all three raw sizes on this very
same event, with no separate size union bound. -/
theorem GoodFourier.rawSize {q ε : ℝ} {s : OriginalSample G} (h : GoodFourier q ε s)
    (i : Fin 3) : |((rawSet s i).card : ℝ)-q*(Fintype.card G : ℝ)| ≤
      ε*(Fintype.card G : ℝ) := by
  have hre : (fourierError q s i 0).re = ((rawSet s i).card : ℝ)-q*(Fintype.card G : ℝ) := by
    simp [fourierError,rawBit_eq,Finset.sum_sub_distrib,mul_comm]
  rw [← hre]
  exact (Complex.abs_re_le_norm _).trans (h i 0)

end
end EndpointFractionalRawEvent
