import CorralFormalization.EndpointProof.Sampling.FullAvailability
import CorralFormalization.EndpointProof.Probability.SelectorBudget

/-!
Instantiate the common-event theorem with the numerical budget for
four-orbit P candidates. The actual orbit injections and label demands
remain explicit inputs; no selector packing is constructed in this file.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFullProduct

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointReservoirAvailability
open CorralFormalization.EndpointProof.RateBudget

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Actual full-sample bound for any concrete family of `floor(n/1000)`
packed candidates per query whose required labels have success probability
at least `p⁴`. The deterministic injections and this success bound are
explicit; the mean/budget separation is proved using uniform exact-matching theorem's actual `C_{P,0}`.
-/
theorem full_sample_four_orbit_budget {Q I J : Type*}
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (p τ : ℝ≥0) (hp : 0 < (p : ℝ))
    (h : 3 * p + 3 * τ ≤ 1)
    (hP : (p : ℝ) = rho q η * a) (hQ : (τ : ℝ) = rho q η * b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (hcard : Fintype.card I = Fintype.card G / 1000)
    (hprob : ∀ u i, (p : ℝ)^4 ≤ successProbability p τ (demand u i)) :
    (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω : FullSample G | ¬ FullAvailable e demand
        (selectorBudget p (Fintype.card G)) ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-((p : ℝ)^8 / 32000) * (Fintype.card G : ℝ)) := by
  let t : ℝ := (Fintype.card I : ℝ) * (p : ℝ)^4 / 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hnum := selector_mean_and_exponent (p : ℝ) (Fintype.card G) hp hn
  dsimp only at hnum
  rw [← hcard] at hnum
  have hmean : ∀ u, (selectorBudget p (Fintype.card G) : ℝ) ≤
      (∑ i, successProbability p τ (demand u i)) - t := by
    intro u
    have hsum : (Fintype.card I : ℝ) * (p : ℝ)^4 ≤
        ∑ i, successProbability p τ (demand u i) := by
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hprob u i)
    dsimp [t]
    linarith [hnum.1]
  have hraw := full_sample_universal_availability hodd q η a b
    hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ e demand
    (selectorBudget p (Fintype.card G)) t ht hmean
  have hexp : Real.exp (-t^2 / (2 * (Fintype.card I : ℝ) * (1/4))) ≤
      Real.exp (-((p : ℝ)^8 / 32000) * (Fintype.card G : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [t]
    simpa only [neg_div, neg_mul] using neg_le_neg hnum.2
  exact hraw.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- The same bound after forgetting all auxiliary coins. The event asserts
existence of one augmentation which works for every specified query and
later forbidden set; the actual query family is still supplied explicitly. -/
theorem original_sample_four_orbit_budget {Q I J : Type*}
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (p τ : ℝ≥0) (hp : 0 < (p : ℝ))
    (h : 3 * p + 3 * τ ≤ 1)
    (hP : (p : ℝ) = rho q η * a) (hQ : (τ : ℝ) = rho q η * b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (hcard : Fintype.card I = Fintype.card G / 1000)
    (hprob : ∀ u i, (p : ℝ)^4 ≤ successProbability p τ (demand u i)) :
    (originalMeasure q hq0 hq1).real
      {s : OriginalSample G | ¬ OriginalAdmitsAvailable e demand
        (selectorBudget p (Fintype.card G)) s} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-((p : ℝ)^8 / 32000) * (Fintype.card G : ℝ)) := by
  have hp' := originalProcess_measurePreserving (G := G)
    q η a b hq0 hq1 hη0 hη1 ha hb hab
  rw [← hp'.measureReal_preimage (by measurability)]
  apply le_trans (measureReal_mono ?_)
    (full_sample_four_orbit_budget hodd hn q η a b hq0 hq1 hη0 hη1 ha hb hab
      p τ hp h hP hQ e demand hcard hprob)
  intro ω hbad hgood
  exact hbad ⟨ω, rfl, hgood⟩

end
end EndpointFullProduct
