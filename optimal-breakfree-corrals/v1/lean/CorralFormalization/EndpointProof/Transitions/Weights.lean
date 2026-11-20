import CorralFormalization.EndpointProof.Transitions.OneSided

/-!
# Explicit ordinary-transition weights and their ideal weighted degrees

The coefficients are the displayed J3 coefficients, with actual unequal
raw densities in `[0.9q,q]`.  These are explicit algebraic weights, rather
than a supplied fractional-matching existence certificate.
-/

open scoped Classical BigOperators

namespace EndpointTransitions

noncomputable section

def alpha (q a b c : ℝ) : ℝ := q-(q-a)-(q-b)-(q-c)
def coreWeight (q a b c : ℝ) : ℝ := q^2*alpha q a b c/(2*a*b*c)
def rootWeight (q b c : ℝ) : ℝ := q^2/(2*b*c)

def DensityWindow (q a : ℝ) : Prop := 9*q/10 ≤ a ∧ a ≤ q

theorem DensityWindow.pos {q a : ℝ} (hq : 0 < q) (ha : DensityWindow q a) : 0 < a := by
  dsimp [DensityWindow] at ha
  linarith

theorem alpha_bounds {q a b c : ℝ} (hq : 0 < q)
    (ha : DensityWindow q a) (hb : DensityWindow q b) (hc : DensityWindow q c) :
    7*q/10 ≤ alpha q a b c ∧ alpha q a b c ≤ q := by
  dsimp [DensityWindow] at ha hb hc
  unfold alpha
  constructor <;> linarith

theorem rootWeight_bounds {q b c : ℝ} (hq : 0 < q)
    (hb : DensityWindow q b) (hc : DensityWindow q c) :
    0 < rootWeight q b c ∧ rootWeight q b c ≤ 1 := by
  have hbpos := hb.pos hq
  have hcpos := hc.pos hq
  have hbc : (9*q/10)*(9*q/10) ≤ b*c :=
    mul_le_mul hb.1 hc.1 (by positivity) hbpos.le
  have hden : 0 < 2*b*c := by positivity
  constructor
  · exact div_pos (sq_pos_of_pos hq) hden
  · apply (div_le_one hden).mpr
    nlinarith [sq_nonneg q]

theorem coreWeight_bounds {q a b c : ℝ} (hq : 0 < q)
    (ha : DensityWindow q a) (hb : DensityWindow q b) (hc : DensityWindow q c) :
    0 < coreWeight q a b c ∧ coreWeight q a b c ≤ 1 := by
  have hapos := ha.pos hq
  have hbpos := hb.pos hq
  have hcpos := hc.pos hq
  have hα := alpha_bounds hq ha hb hc
  have hαpos : 0 < alpha q a b c := by linarith
  have hab : (9*q/10)*(9*q/10) ≤ a*b :=
    mul_le_mul ha.1 hb.1 (by positivity) hapos.le
  have habc : ((9*q/10)*(9*q/10))*(9*q/10) ≤ a*b*c :=
    mul_le_mul hab hc.1 (by positivity) (mul_nonneg hapos.le hbpos.le)
  have hden : 0 < 2*a*b*c := by positivity
  constructor
  · exact div_pos (mul_pos (sq_pos_of_pos hq) hαpos) hden
  · apply (div_le_one hden).mpr
    have hnum : q^2*alpha q a b c ≤ q^2*q :=
      mul_le_mul_of_nonneg_left hα.2 (sq_nonneg q)
    nlinarith [pow_pos hq 3]

theorem ideal_root_degree (q b c n : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    rootWeight q b c*(b*c*n) = q^2*n/2 := by
  unfold rootWeight
  field_simp
  <;> ring

theorem ideal_core_degree (q a b c n : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    coreWeight q a b c*(b*c*n)+
      rootWeight q a c*((q-b)*c*n)+rootWeight q a b*((q-c)*b*n) = q^2*n/2 := by
  unfold coreWeight rootWeight alpha
  field_simp
  <;> ring

/-- All three coefficient errors add with their actual coefficients bounded
by one.  The ideal values and the actual counts remain explicit. -/
theorem weighted_three_error (w₀ w₁ w₂ x₀ x₁ x₂ y₀ y₁ y₂ e₀ e₁ e₂ : ℝ)
    (hw₀ : 0 ≤ w₀ ∧ w₀ ≤ 1) (hw₁ : 0 ≤ w₁ ∧ w₁ ≤ 1)
    (hw₂ : 0 ≤ w₂ ∧ w₂ ≤ 1)
    (h₀ : |x₀-y₀| ≤ e₀) (h₁ : |x₁-y₁| ≤ e₁) (h₂ : |x₂-y₂| ≤ e₂) :
    |(w₀*x₀+w₁*x₁+w₂*x₂)-(w₀*y₀+w₁*y₁+w₂*y₂)| ≤ e₀+e₁+e₂ := by
  have hterm (w x y e : ℝ) (hw : 0 ≤ w ∧ w ≤ 1) (h : |x-y| ≤ e) :
      |w*(x-y)| ≤ e := by
    rw [abs_mul, abs_of_nonneg hw.1]
    exact (mul_le_mul_of_nonneg_left h hw.1).trans
      (by nlinarith [le_trans (abs_nonneg (x-y)) h])
  calc
    _ = |w₀*(x₀-y₀)+w₁*(x₁-y₁)+w₂*(x₂-y₂)| := by congr 1; ring
    _ ≤ |w₀*(x₀-y₀)+w₁*(x₁-y₁)|+|w₂*(x₂-y₂)| := abs_add_le _ _
    _ ≤ (|w₀*(x₀-y₀)|+|w₁*(x₁-y₁)|)+|w₂*(x₂-y₂)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ e₀+e₁+e₂ := add_le_add
      (add_le_add (hterm _ _ _ _ hw₀ h₀) (hterm _ _ _ _ hw₁ h₁))
      (hterm _ _ _ _ hw₂ h₂)

/-- Actual convolution estimates `4ηn,5ηn,5ηn` imply the weighted core
degree estimate `14ηn`. -/
theorem core_degree_error {q a b c n η c₀ c₁ c₂ : ℝ}
    (hq : 0 < q) (ha : DensityWindow q a) (hb : DensityWindow q b) (hc : DensityWindow q c)
    (h₀ : |c₀-b*c*n| ≤ 4*η*n)
    (h₁ : |c₁-(q-b)*c*n| ≤ 5*η*n)
    (h₂ : |c₂-(q-c)*b*n| ≤ 5*η*n) :
    |(coreWeight q a b c*c₀+rootWeight q a c*c₁+rootWeight q a b*c₂)-q^2*n/2| ≤
      14*η*n := by
  have h := weighted_three_error
    (coreWeight q a b c) (rootWeight q a c) (rootWeight q a b)
    c₀ c₁ c₂ (b*c*n) ((q-b)*c*n) ((q-c)*b*n) (4*η*n) (5*η*n) (5*η*n)
    ⟨(coreWeight_bounds hq ha hb hc).1.le,(coreWeight_bounds hq ha hb hc).2⟩
    ⟨(rootWeight_bounds hq ha hc).1.le,(rootWeight_bounds hq ha hc).2⟩
    ⟨(rootWeight_bounds hq ha hb).1.le,(rootWeight_bounds hq ha hb).2⟩ h₀ h₁ h₂
  rw [ideal_core_degree q a b c n (ne_of_gt (ha.pos hq))
    (ne_of_gt (hb.pos hq)) (ne_of_gt (hc.pos hq))] at h
  convert h using 1 <;> ring

end
end EndpointTransitions
