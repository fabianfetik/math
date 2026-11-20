import CorralFormalization.EndpointProof.Probability.LayeredSample.Asymptotic

/-!
Fourier Hoeffding on every role of the actual categorical layer sample.
Each role is centered at its own point mass; generic vertex and colour
roles therefore have centers `a` and `c`, never the special density `q`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ComplexConjugate NNReal

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointOriginalReservoir EndpointFullProduct EndpointFiniteProductConcentration

noncomputable section

def weightedRoleError {G A : Type*} [Fintype G]
    (p : ℝ) (role : A) (a : G → ℝ) (w : G → A) : ℝ :=
  ∑ g, ((if w g = role then (1 : ℝ) else 0) - p) * a g

theorem weightedRoleError_boundedDifferences {G A : Type*} [Fintype G]
    (p : ℝ) (role : A) (a : G → ℝ) (ha : ∀ g, |a g| ≤ 1) :
    CoordinateBoundedDifferences (weightedRoleError p role a) (fun _ : G => 1) := by
  intro k w w' hw
  have he : weightedRoleError p role a w - weightedRoleError p role a w' =
      ((if w k = role then (1 : ℝ) else 0) - (if w' k = role then 1 else 0)) * a k := by
    unfold weightedRoleError
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · ring
    · intro g _ hg; rw [hw g hg]; ring
    · simp
  rw [he, abs_mul]
  have hbit : |(if w k = role then (1 : ℝ) else 0) -
      (if w' k = role then 1 else 0)| ≤ 1 := by split_ifs <;> norm_num
  exact mul_le_one₀ hbit (abs_nonneg _) (ha k)

theorem weightedRoleError_expectation {G A : Type*} [Fintype G] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (role : A) (a : G → ℝ) :
    (∫ w : G → A, weightedRoleError (L.weight role) role a w
      ∂Measure.pi (fun _ : G => L.measure)) = 0 := by
  have hone (g : G) :
      (∫ w : G → A, if w g = role then (1 : ℝ) else 0
        ∂Measure.pi (fun _ : G => L.measure)) = L.weight role := by
    simpa only [eventCount, Finset.sum_singleton, eventMass_eq, Finset.card_singleton,
      Nat.cast_one, one_mul] using
      eventCount_expectation L {g} (fun x => x = role)
  unfold weightedRoleError
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_mul_const, integral_sub Integrable.of_finite Integrable.of_finite,
    hone]
  simp

theorem weightedRoleError_hasSubgaussianMGF {G A : Type*} [Fintype G] [Fintype A]
    [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (role : A) (a : G → ℝ) (ha : ∀ g, |a g| ≤ 1) :
    HasSubgaussianMGF (weightedRoleError (L.weight role) role a)
      ((Fintype.card G : ℝ≥0) / 4) (Measure.pi (fun _ : G => L.measure)) := by
  have hs := EndpointFiniteProductConcentration.hasSubgaussianMGF
    (fun _ : G => L.measure) (fun _ : G => 1)
    (weightedRoleError (L.weight role) role a)
    (weightedRoleError_boundedDifferences (L.weight role) role a ha)
  rw [weightedRoleError_expectation] at hs
  norm_num [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] at hs ⊢
  exact hs

theorem weightedRoleError_twoSided_tail {G A : Type*} [Fintype G] [Nonempty G]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (role : A) (ε : ℝ) (hε : 0 ≤ ε)
    (a : G → ℝ) (ha : ∀ g, |a g| ≤ 1) :
    (Measure.pi (fun _ : G => L.measure)).real
      {w | ε * (Fintype.card G : ℝ) / 2 <
        |weightedRoleError (L.weight role) role a w|} ≤
      2 * Real.exp (-ε^2 * (Fintype.card G : ℝ) / 4) := by
  have hs := weightedRoleError_hasSubgaussianMGF L role a ha
  have h := EndpointFractionalRawEvent.twoSided_tail _ _ _ hs
    (ε * (Fintype.card G : ℝ) / 2) (by positivity)
  have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have he : -(ε * (Fintype.card G : ℝ) / 2)^2 /
      (2 * ((Fintype.card G : ℝ) / 4)) = -ε^2 * (Fintype.card G : ℝ) / 2 := by
    field_simp
    <;> ring
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat] at h
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ε])) (by norm_num))

def categoricalFourier {G A : Type*} [Fintype G] [AddCommGroup G]
    (p : ℝ) (role : A) (w : G → A) (χ : AddChar G ℂ) : ℂ :=
  ∑ g, (((if w g = role then (1 : ℝ) else 0) - p : ℝ) : ℂ) * conj (χ g)

theorem categoricalFourier_re {G A : Type*} [Fintype G] [AddCommGroup G]
    (p : ℝ) (role : A) (w : G → A) (χ : AddChar G ℂ) :
    (categoricalFourier p role w χ).re =
      weightedRoleError p role (fun g => (conj (χ g)).re) w := by
  simp [categoricalFourier, weightedRoleError, Complex.mul_re]

theorem categoricalFourier_im {G A : Type*} [Fintype G] [AddCommGroup G]
    (p : ℝ) (role : A) (w : G → A) (χ : AddChar G ℂ) :
    (categoricalFourier p role w χ).im =
      weightedRoleError p role (fun g => (conj (χ g)).im) w := by
  simp [categoricalFourier, weightedRoleError, Complex.mul_im]

/-- Negating a numerical role mask only inverts the character. -/
theorem categoricalFourier_neg {G A : Type*} [Fintype G] [AddCommGroup G]
    (p : ℝ) (role : A) (w : G → A) (χ : AddChar G ℂ) :
    categoricalFourier p role (fun g => w (-g)) χ =
      categoricalFourier p role w χ⁻¹ := by
  have h := Equiv.sum_comp (Equiv.neg G) (fun g : G =>
    (((if w (-g) = role then (1 : ℝ) else 0) - p : ℝ) : ℂ) * conj (χ g))
  simpa [categoricalFourier] using h.symm

theorem categoricalFourier_tail {G A : Type*} [Fintype G] [AddCommGroup G]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (L : FiniteLaw A) (role : A) (ε : ℝ) (hε : 0 ≤ ε) (χ : AddChar G ℂ) :
    (Measure.pi (fun _ : G => L.measure)).real
      {w | ε * (Fintype.card G : ℝ) < ‖categoricalFourier (L.weight role) role w χ‖} ≤
      4 * Real.exp (-ε^2 * (Fintype.card G : ℝ) / 4) := by
  let μ := Measure.pi (fun _ : G => L.measure)
  let t := ε * (Fintype.card G : ℝ) / 2
  have hR := weightedRoleError_twoSided_tail L role ε hε
    (fun g => (conj (χ g)).re)
    (fun g => by simpa using Complex.abs_re_le_norm (conj (χ g)))
  have hI := weightedRoleError_twoSided_tail L role ε hε
    (fun g => (conj (χ g)).im)
    (fun g => by simpa using Complex.abs_im_le_norm (conj (χ g)))
  simp only [← categoricalFourier_re] at hR
  simp only [← categoricalFourier_im] at hI
  have hsub : {w : G → A | ε * (Fintype.card G : ℝ) <
      ‖categoricalFourier (L.weight role) role w χ‖} ⊆
      {w | t < |(categoricalFourier (L.weight role) role w χ).re|} ∪
      {w | t < |(categoricalFourier (L.weight role) role w χ).im|} := by
    intro w hw
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
    have hnorm := Complex.norm_le_abs_re_add_abs_im
      (categoricalFourier (L.weight role) role w χ)
    change ε * (Fintype.card G : ℝ) < ‖categoricalFourier (L.weight role) role w χ‖ at hw
    dsimp [t] at hc
    linarith
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    ((measureReal_union_le _ _).trans (by dsimp [μ, t]; linarith))

abbrev RawRole (m : ℕ) := VertexRole m ⊕ ColourRole m

def roleDensity {m : ℕ} (d : Densities m) : RawRole m → ℝ
  | Sum.inl v => vertexWeight d v
  | Sum.inr c => colourWeight d c

def roleFourierError {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (s : Sample G m) (role : RawRole m) (χ : AddChar G ℂ) : ℂ :=
  match role with
  | Sum.inl v => categoricalFourier (vertexWeight d v) v s.1 χ
  | Sum.inr c => categoricalFourier (colourWeight d c) c s.2 χ

/-- All raw roles and every character at the actual role-specific density.
This stronger event includes every ordinary layer triple and all reserves. -/
def FourierEvent {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (ε : ℝ) (s : Sample G m) : Prop :=
  ∀ (role : RawRole m) (χ : AddChar G ℂ),
    ‖roleFourierError d s role χ‖ ≤ ε * (Fintype.card G : ℝ)

theorem FourierEvent.signedVertex {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {d : Densities m} {ε : ℝ} {s : Sample G m} (h : FourierEvent d ε s)
    (v : VertexRole m) (negative : Bool) (χ : AddChar G ℂ) :
    ‖categoricalFourier (vertexWeight d v) v
      (fun g => s.1 (if negative then -g else g)) χ‖ ≤ ε * (Fintype.card G : ℝ) := by
  cases negative
  · exact h (Sum.inl v) χ
  · simpa only [Bool.true_eq_false, ↓reduceIte, categoricalFourier_neg, roleFourierError] using
      h (Sum.inl v) χ⁻¹

theorem FourierEvent.signedColour {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {d : Densities m} {ε : ℝ} {s : Sample G m} (h : FourierEvent d ε s)
    (c : ColourRole m) (negative : Bool) (χ : AddChar G ℂ) :
    ‖categoricalFourier (colourWeight d c) c
      (fun g => s.2 (if negative then -g else g)) χ‖ ≤ ε * (Fintype.card G : ℝ) := by
  cases negative
  · exact h (Sum.inr c) χ
  · simpa only [Bool.true_eq_false, ↓reduceIte, categoricalFourier_neg, roleFourierError] using
      h (Sum.inr c) χ⁻¹

/-- Generic vertex masks are centered at `a`, with either manuscript sign. -/
theorem FourierEvent.genericVertex {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {d : Densities m} {ε : ℝ} {s : Sample G m} (h : FourierEvent d ε s)
    (v : Fin m) (negative : Bool) (χ : AddChar G ℂ) :
    ‖categoricalFourier d.a (Sum.inr v)
      (fun g => s.1 (if negative then -g else g)) χ‖ ≤ ε * (Fintype.card G : ℝ) :=
  h.signedVertex (Sum.inr v) negative χ

/-- Ordinary colour masks are centered at `c`, with either manuscript sign. -/
theorem FourierEvent.genericColour {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {d : Densities m} {ε : ℝ} {s : Sample G m} (h : FourierEvent d ε s)
    (c : Fin (m + 1)) (negative : Bool) (χ : AddChar G ℂ) :
    ‖categoricalFourier d.c (Sum.inr c)
      (fun g => s.2 (if negative then -g else g)) χ‖ ≤ ε * (Fintype.card G : ℝ) :=
  h.signedColour (Sum.inr c) negative χ

theorem roleFourierError_tail {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (ε : ℝ) (hε : 0 ≤ ε) (role : RawRole m) (χ : AddChar G ℂ) :
    (sampleMeasure (G := G) d).real
      {s | ε * (Fintype.card G : ℝ) < ‖roleFourierError d s role χ‖} ≤
      4 * Real.exp (-ε^2 * (Fintype.card G : ℝ) / 4) := by
  rcases role with v | c
  · have hp : MeasurePreserving (Prod.fst : Sample G m → G → VertexRole m)
        (sampleMeasure d) (Measure.pi fun _ : G => (vertexLaw d).measure) :=
      measurePreserving_fst
    have h := categoricalFourier_tail (vertexLaw d) v ε hε χ
    rw [← hp.measureReal_preimage (by measurability)] at h
    exact h
  · have hp : MeasurePreserving (Prod.snd : Sample G m → G → ColourRole m)
        (sampleMeasure d) (Measure.pi fun _ : G => (colourLaw d).measure) :=
      measurePreserving_snd
    have h := categoricalFourier_tail (colourLaw d) c ε hε χ
    rw [← hp.measureReal_preimage (by measurability)] at h
    exact h

/-- Only the fixed `(role, character)` labels enter the union bound.
Different categorical roles and different Fourier events need not be
independent. -/
theorem fourierEvent_failure_probability {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (ε : ℝ) (hε : 0 ≤ ε) :
    (sampleMeasure (G := G) d).real {s | ¬ FourierEvent d ε s} ≤
      (4 * (2 * m + 7 : ℕ) : ℝ) * (Fintype.card G : ℝ) *
        Real.exp (-ε^2 * (Fintype.card G : ℝ) / 4) := by
  let bad : RawRole m × AddChar G ℂ → Set (Sample G m) := fun k =>
    {s | ε * (Fintype.card G : ℝ) < ‖roleFourierError d s k.1 k.2‖}
  have heq : {s : Sample G m | ¬ FourierEvent d ε s} = ⋃ k, bad k := by
    ext s
    simp only [FourierEvent, not_forall, not_le, bad, Set.mem_iUnion,
      Set.mem_ofPred_eq, Prod.exists]
  rw [heq]
  calc
    (sampleMeasure d).real (⋃ k, bad k) ≤
        ∑ k, (sampleMeasure d).real (bad k) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : RawRole m × AddChar G ℂ,
        4 * Real.exp (-ε^2 * (Fintype.card G : ℝ) / 4) :=
      Finset.sum_le_sum (fun k _ => roleFourierError_tail d ε hε k.1 k.2)
    _ = _ := by simp [RawRole, VertexRole, ColourRole, AddChar.card_eq]; ring

/-- exact-matching, pair supply, all raw sizes and all raw Fourier coefficients on
the same categorical sample. -/
theorem goodSample_and_fourier_failure_probability
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (tol B ε : ℝ) (hε : 0 ≤ ε)
    (hgood : (sampleMeasure (G := G) d).real {s | ¬ GoodSample d tol s} ≤ B) :
    (sampleMeasure (G := G) d).real {s | ¬ (GoodSample d tol s ∧ FourierEvent d ε s)} ≤
      B + (4 * (2 * m + 7 : ℕ) : ℝ) * (Fintype.card G : ℝ) *
        Real.exp (-ε^2 * (Fintype.card G : ℝ) / 4) := by
  have heq : {s : Sample G m | ¬ (GoodSample d tol s ∧ FourierEvent d ε s)} =
      {s | ¬ GoodSample d tol s} ∪ {s | ¬ FourierEvent d ε s} := by
    ext s; simp only [not_and_or, Set.mem_union, Set.mem_ofPred_eq]
  rw [heq]
  exact (measureReal_union_le _ _).trans
    (add_le_add hgood (fourierEvent_failure_probability d ε hε))

end
end EndpointLayeredSample
