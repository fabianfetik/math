import CorralFormalization.EndpointProof.AbsorberInputs.PackedAvailability.PackedCategorical

/-!
Adapters from general packed-availability probability to the maintained seven-label reservoir
law and to the existing constant-slot shared-sample interface.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

namespace AbsorberInputs.PackedAvailability

noncomputable section

open EndpointBlockAvailability

theorem labelMeasure_real_singleton (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (l : Label) :
    (labelMeasure p τ h).real {l} = (labelWeights p τ l : ℝ) := by
  rw [measureReal_def, labelMeasure_singleton]
  simp

theorem categoricalMeasure_eq_orbitMeasure {O : Type*} [Fintype O]
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) :
    categoricalMeasure (fun _ : O => labelMeasure p τ h) =
      EndpointSharedSample.orbitMeasure p τ h := rfl

/-- The old product-shaped orbit embedding is a special case of the
dependent-slot embedding. No labels or sampled outcomes are changed. -/
def sigmaEmbedding {O I J : Type*} (e : I × J ↪ O) : (Sigma (fun _ : I => J)) ↪ O :=
  (Equiv.sigmaEquivProd I J).toEmbedding.trans e

theorem project_sigmaEmbedding {O I J L : Type*} (e : I × J ↪ O) (ω : O → L) :
    project (sigmaEmbedding e) ω = (fun i j => ω (e (i,j))) := rfl

theorem support_sigmaEmbedding {O I J K : Type*} [Fintype J] [DecidableEq K]
    (e : I × J ↪ O) (place : O × Bool ↪ K) (i : I) :
    support (sigmaEmbedding e) place i = EndpointSharedSample.support e place i := rfl

/-- The general theorem uses the unchanged categorical P/Q orbit law.
The required labels may differ, and the actual number of labels may vary
from candidate to candidate. Unrequested geometric orbits remain part of
the full supports used in the adaptive deletion conclusion. -/
theorem seven_label_full_support_linear_event_tail
    {Q O K : Type*} [Fintype Q] [Fintype O] [DecidableEq K]
    {I : Q → Type*} [∀ q, Fintype (I q)]
    {J : (q : Q) → I q → Type*} [∀ q i, Fintype (J q i)]
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1)
    (e : (q : Q) → (Sigma (J q)) ↪ O)
    (fullSupport : (q : Q) → I q → Finset K)
    (hdisj : ∀ q, Pairwise fun i j => Disjoint (fullSupport q i) (fullSupport q j))
    (demand : (q : Q) → (i : I q) → J q i → Label)
    (m : ℕ) (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hsize : ∀ q i, Fintype.card (J q i) ≤ m)
    (hmin : ∀ q i j, v ≤ (labelWeights p τ (demand q i j) : ℝ))
    (n : ℕ) (α : ℝ) (hlinear : ∀ q, α*n ≤ (Fintype.card (I q) : ℝ)) :
    (EndpointSharedSample.orbitMeasure p τ h).real
      {ω | ¬ FullSupportEvent e fullSupport demand (fun _ => α*n*v^m/2) ω} ≤
      (Fintype.card Q : ℝ)*Real.exp (-(α*n*v^m)/8) := by
  rw [← categoricalMeasure_eq_orbitMeasure]
  apply categorical_full_support_linear_event_tail
    (fun _ => labelMeasure p τ h) e fullSupport hdisj demand m v hv0 hv1 hsize
    (fun q i j => ?_) n α hlinear
  simpa only [labelMeasure_real_singleton] using hmin _ _ _

end
end AbsorberInputs.PackedAvailability
