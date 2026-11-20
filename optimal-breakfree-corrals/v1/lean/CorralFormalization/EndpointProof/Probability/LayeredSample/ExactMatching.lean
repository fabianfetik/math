import CorralFormalization.EndpointProof.Probability.LayeredSample.Model
import CorralFormalization.EndpointProof.Matching.UniformExactMatching

/-! exact-matching on the actual categorical layer sample, with its original quantifiers. -/

open MeasureTheory
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointFullProduct EndpointMatching.UniversalCore
open EndpointMatching.Fractional.Rounding
open EndpointMatching.AbsorptionAssembly
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section
universe u

@[simp] theorem project_tailSet {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (s : Sample G m) :
    originalTailSet (project s) = vertexSet s (lastVertex m) := by
  ext g; simp [originalTailSet, project, vertexSet]

@[simp] theorem project_headSet {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (s : Sample G m) :
    originalHeadSet (project s) = vertexSet s (firstVertex m) := by
  ext g; simp [originalHeadSet, project, vertexSet]

@[simp] theorem project_colourSet {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (s : Sample G m) :
    originalColourSet (project s) = colourSet s (specialColour m) := by
  ext g; simp [originalColourSet, project, colourSet]

/-- exact-matching is an event of the one layer sample, uniformly over every later
nearby balanced triple.  Zero remains allowed in both endpoint roles;
the later colour target is explicitly required to avoid zero. -/
def ExactMatchingEvent {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} (d : Densities m) (s : Sample G m) : Prop :=
  PhysicalExactEvent d.q (project s)

/-- The failure bound is transported by equality of laws, rather than a
union over any of the uniform exact-matching theorem's later adaptive target triples.  The published AKS
input is kept explicit, exactly as in the imported exact-matching theorem. -/
theorem exactMatchingEvent_failure_probability
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    {m : ℕ} (d : Densities m) (hq0 : 0 < d.q) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (sampleMeasure (G := G) d).real {s | ¬ ExactMatchingEvent d s} ≤
        Real.exp (-((xi d.q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ := original_exact_matching_probability hAKS d.q hq0 d.q_le_half
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  have hp := project_measurePreserving (G := G) d
  have heq := hp.measureReal_preimage
    (s := {s : OriginalSample G | ¬ PhysicalExactEvent d.q s}) (by measurability)
  change (sampleMeasure d).real
    (project ⁻¹' {s : OriginalSample G | ¬ PhysicalExactEvent d.q s}) ≤ _
  rw [heq]
  exact hN G hodd hn

/-- The concrete physical conclusion on any good layer sample.  All
target quantifiers are after the fixed sample. -/
theorem exactMatchingEvent_apply {G : Type*} [Fintype G] [AddCommGroup G]
    {m : ℕ} {d : Densities m} {s : Sample G m}
    (h : ExactMatchingEvent d s) (X Y C : Finset G)
    (hdisjoint : Disjoint X Y) (hzero : (0 : G) ∉ C)
    (hXY : X.card = Y.card) (hXC : X.card = C.card)
    (hsum : (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x)
    (hedit : (physicalEditDistance (vertexSet s (lastVertex m))
      (vertexSet s (firstVertex m)) (colourSet s (specialColour m)) X Y C : ℝ) ≤
        (1 / 10^6 : ℝ) * kappa d.q * (Fintype.card G : ℝ)) :
    Nonempty (EndpointMatching.AbsorptionAssembly.PhysicalDifferenceMatching X Y C) := by
  apply h X Y C hdisjoint hzero hXY hXC hsum
  simpa using hedit

end
end EndpointLayeredSample
