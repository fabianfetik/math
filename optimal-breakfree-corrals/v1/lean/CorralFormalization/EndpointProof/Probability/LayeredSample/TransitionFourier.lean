import CorralFormalization.EndpointProof.Probability.LayeredSample.FourierJoint
import CorralFormalization.EndpointProof.Transitions.FourierExceptional

/-! The actual layer sample supplies the literal ordinary-transition Fourier hypotheses. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointTransitions EndpointMatching.Fractional.Fourier EndpointFractionalRawEvent
open EndpointMatching.Fractional.Rounding

noncomputable section
universe u

def signedVertexSet {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (s : Sample G m) (v : VertexRole m) (negative : Bool) : Finset G :=
  Finset.univ.filter (fun g => s.1 (if negative then -g else g) = v)

def signedColourSet {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (s : Sample G m) (c : ColourRole m) (negative : Bool) : Finset G :=
  Finset.univ.filter (fun g => s.2 (if negative then -g else g) = c)

theorem FourierEvent.vertexFourierGood {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {d : Densities m} {η : ℝ} {s : Sample G m} (h : FourierEvent d (η^2) s)
    (v : VertexRole m) (negative : Bool) :
    FourierGood (signedVertexSet s v negative) (vertexWeight d v) η := by
  intro χ
  have hc := h.signedVertex v negative χ
  have heq : coefficient (fun g =>
      ((setBit (signedVertexSet s v negative) g - vertexWeight d v : ℝ) : ℂ)) χ =
      categoricalFourier (vertexWeight d v) v
        (fun g => s.1 (if negative then -g else g)) χ := by
    unfold coefficient categoricalFourier
    apply Finset.sum_congr rfl
    intro g _
    simp only [setBit, signedVertexSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hg : s.1 (if negative then -g else g) = v <;> simp [hg]
  rw [heq]
  exact hc

theorem FourierEvent.colourFourierGood {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {d : Densities m} {η : ℝ} {s : Sample G m} (h : FourierEvent d (η^2) s)
    (c : ColourRole m) (negative : Bool) :
    FourierGood (signedColourSet s c negative) (colourWeight d c) η := by
  intro χ
  have hc := h.signedColour c negative χ
  have heq : coefficient (fun g =>
      ((setBit (signedColourSet s c negative) g - colourWeight d c : ℝ) : ℂ)) χ =
      categoricalFourier (colourWeight d c) c
        (fun g => s.2 (if negative then -g else g)) χ := by
    unfold coefficient categoricalFourier
    apply Finset.sum_congr rfl
    intro g _
    simp only [setBit, signedColourSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hg : s.2 (if negative then -g else g) = c <;> simp [hg]
  rw [heq]
  exact hc

/-- The literal ordinary-transition Fourier hypotheses for every possible ordinary role
triple, at both signs.  This stronger fixed event requires no choice of a
later partner set, endpoint target, or edited layer. -/
def TransitionFourierEvent {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (η : ℝ) (s : Sample G m) : Prop :=
  (∀ (v : VertexRole m) (negative : Bool),
    FourierGood (signedVertexSet s v negative) (vertexWeight d v) η) ∧
  (∀ (c : ColourRole m) (negative : Bool),
    FourierGood (signedColourSet s c negative) (colourWeight d c) η)

theorem transitionFourierEvent_of_fourierEvent
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {d : Densities m} {η : ℝ} {s : Sample G m} (h : FourierEvent d (η^2) s) :
    TransitionFourierEvent d η s :=
  ⟨h.vertexFourierGood, h.colourFourierGood⟩

theorem transitionFourierEvent_failure_probability
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (η : ℝ) :
    (sampleMeasure (G := G) d).real {s | ¬ TransitionFourierEvent d η s} ≤
      (4 * (2 * m + 7 : ℕ) : ℝ) * (Fintype.card G : ℝ) *
        Real.exp (-η^4 * (Fintype.card G : ℝ) / 4) := by
  have hsub : {s : Sample G m | ¬ TransitionFourierEvent d η s} ⊆
      {s | ¬ FourierEvent d (η^2) s} := by
    intro s hbad hgood
    exact hbad (transitionFourierEvent_of_fourierEvent hgood)
  have h := (measureReal_mono hsub (measure_ne_top (sampleMeasure d) _)).trans
    (fourierEvent_failure_probability d (η^2) (sq_nonneg _))
  simpa only [← pow_mul, show 2*2=4 from rfl] using h

/-- A sample fixed before every later query satisfies exact-matching, every actual
pair bank, all raw size estimates and ordinary transition lemma's actual Fourier hypotheses for
all ordinary transitions with their proper signs and individual means. -/
theorem exists_goodSample_and_transitionFourier
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    {m : ℕ} (d : Densities m) (hq0 : 0 < d.q) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      ∃ s : Sample G m,
        GoodSample d (explicitSizeTolerance (Fintype.card G)) s ∧
          TransitionFourierEvent d η s := by
  obtain ⟨N, hN⟩ := exists_goodSample_and_fourier_explicitTolerance
    hAKS d hq0 (η^2) (sq_pos_of_pos hη)
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  obtain ⟨s, hs, hf⟩ := hN G hodd hn
  exact ⟨s, hs, transitionFourierEvent_of_fourierEvent hf⟩

end
end EndpointLayeredSample
