import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.BiteTrace
import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.StoppingBounds
/-!
# An actual matching with the AKS rate, conditional on a source-shaped trace

The conclusion is in the same finite-set matching/uncovered convention as
`AKSSetFamilyInput`. Existence of the trace and the external bite theorem
remain explicit obligations; this file proves neither of them.
-/

open scoped Classical BigOperators
open EndpointMatching.Fractional.Rounding
open AKSSourceBite

namespace AKSBiteTraceRate
noncomputable section
universe u

/-- Given actual bite sets and the numerical source estimates on a finite
trace, their union is an original-edge matching with the explicit AKS rate.
There is no positive lower bound on the final degree. -/
theorem matching_with_source_trace_rate
    {V : Type u} [Fintype V]
    (U : ℕ → Finset V) (H M : ℕ → Finset (Finset V)) (W : ℕ → Finset V)
    (d err u : ℕ → ℝ) (m : ℕ) (θ a C L K : ℝ)
    (hU0 : U 0 = Finset.univ)
    (hU : ∀ i, U (i+1) = remaining (U i) (M i) (W i))
    (hH : ∀ i, H (i+1) = induced (H i) (U (i+1)))
    (hMH : ∀ i, M i ⊆ H i)
    (hinside : ∀ i e, e ∈ M i → e ⊆ U i)
    (hmatching : ∀ i, IsMatching id (M i))
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hK : 0 ≤ K)
    (hstart : Real.exp 1 ≤ d 0) (hdend : 0 ≤ d m) (hstop : d m ≤ L)
    (hu : ∀ i < m, 0 ≤ u i)
    (hstep : ∀ i < m, d (i+1) ≤ θ*d i) (hbefore : ∀ i < m, L ≤ d i)
    (herr : ∀ i < m, u i ≤ C/(d i)^a)
    (hbudget : (C/L^a)/(1-θ^a) ≤ 1/2)
    (hsource : ∀ i < m,
      d (i+1)*(U i).card^2 = d i*(U (i+1)).card^2*(1+err i))
    (herrabs : ∀ i < m, |err i| ≤ u i)
    (hw : ∀ i < m, ((W i).card : ℝ) ≤
      K*((U i).card/Real.sqrt (d i))*Real.sqrt (Real.log (d i))) :
    ∃ P : Finset (Finset V), P ⊆ H 0 ∧ IsMatching id P ∧
      ((uncovered id P).card : ℝ) ≤
        (2*(K*(1+1/(-Real.log θ))+Real.sqrt L)) * (Fintype.card V : ℝ) * aksRate (d 0) := by
  obtain ⟨P,hP,hmatchingP,huncovered⟩ :=
    AKSBiteTrace.matching_of_finite_trace U H M W hU0 hU hH hMH hinside hmatching m
  refine ⟨P,hP,hmatchingP,?_⟩
  have hn : ∀ i ≤ m, 0 ≤ ((U i).card : ℝ) := by intro i hi; positivity
  have hnum := AKSStoppingBounds.source_total_without_terminal_lower
    d (fun i => ((U i).card : ℝ)) (fun i => ((W i).card : ℝ)) err u m θ a C L K
    hθ0 hθ1 ha hC hL hK hstart hdend hstop hn hu hstep hbefore herr hbudget
    hsource herrabs hw
  have hcard : ((uncovered id P).card : ℝ) ≤
      ((U m).card : ℝ) + ∑ i ∈ Finset.range m, ((W i).card : ℝ) := by
    exact_mod_cast huncovered
  have hUcard : ((U 0).card : ℝ) = (Fintype.card V : ℝ) := by simp [hU0]
  rw [hUcard] at hnum
  calc
    ((uncovered id P).card : ℝ) ≤
        ((U m).card : ℝ) + ∑ i ∈ Finset.range m, ((W i).card : ℝ) := hcard
    _ = (∑ i ∈ Finset.range m, ((W i).card : ℝ)) + ((U m).card : ℝ) := by ring
    _ ≤ (2*((Fintype.card V : ℝ)/Real.sqrt (d 0))) *
          (K*(1+1/(-Real.log θ))+Real.sqrt L) *
          (Real.log (d 0)*Real.sqrt (Real.log (d 0))) := hnum
    _ = _ := by unfold aksRate; ring

end
end AKSBiteTraceRate
