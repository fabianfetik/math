import CorralFormalization.EndpointProof.Probability.FlowBudget
import CorralFormalization.EndpointProof.Probability.SamplingParameterChoices

/-!
Q-reservoir common availability at paired cover construction's forbidden-support budget.

This transports a supplied actual packing and a supplied success bound for
each candidate. It does not construct the six-root flow or its packings.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFullProduct

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointReservoirAvailability
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Actual full-model common availability with `floor(n/1000)` candidates,
success probability at least `τ⁹`, and packing budget's exact integer budget. -/
theorem full_sample_nine_orbit_budget {Q I J : Type*}
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (p τ : ℝ≥0) (hτ : 0 < (τ : ℝ))
    (h : 3 * p + 3 * τ ≤ 1)
    (hP : (p : ℝ) = rho q η * a) (hQ : (τ : ℝ) = rho q η * b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (hcard : Fintype.card I = Fintype.card G / 1000)
    (hprob : ∀ u i, (τ : ℝ)^9 ≤ successProbability p τ (demand u i)) :
    (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω : FullSample G | ¬ FullAvailable e demand
        (flowBudget τ (Fintype.card G)) ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-((τ : ℝ)^18 / 32000) * (Fintype.card G : ℝ)) := by
  let t : ℝ := (Fintype.card I : ℝ) * (τ : ℝ)^9 / 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hnum := flow_mean_and_exponent (τ : ℝ) (Fintype.card G) hτ hn
  dsimp only at hnum
  rw [← hcard] at hnum
  have hmean : ∀ u, (flowBudget τ (Fintype.card G) : ℝ) ≤
      (∑ i, successProbability p τ (demand u i)) - t := by
    intro u
    have hsum : (Fintype.card I : ℝ) * (τ : ℝ)^9 ≤
        ∑ i, successProbability p τ (demand u i) := by
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hprob u i)
    dsimp [t]
    linarith [hnum.1]
  have hraw := full_sample_universal_availability hodd q η a b
    hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ e demand
    (flowBudget τ (Fintype.card G)) t ht hmean
  have hexp : Real.exp (-t^2 / (2 * (Fintype.card I : ℝ) * (1/4))) ≤
      Real.exp (-((τ : ℝ)^18 / 32000) * (Fintype.card G : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [t]
    simpa only [neg_div, neg_mul] using neg_le_neg hnum.2
  exact hraw.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- The same budget event, projected to the original vertex/colour law
with one augmentation for every later query and forbidden support. -/
theorem original_sample_nine_orbit_budget {Q I J : Type*}
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) (p τ : ℝ≥0) (hτ : 0 < (τ : ℝ))
    (h : 3 * p + 3 * τ ≤ 1)
    (hP : (p : ℝ) = rho q η * a) (hQ : (τ : ℝ) = rho q η * b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (hcard : Fintype.card I = Fintype.card G / 1000)
    (hprob : ∀ u i, (τ : ℝ)^9 ≤ successProbability p τ (demand u i)) :
    (originalMeasure q hq0 hq1).real
      {s : OriginalSample G | ¬ OriginalAdmitsAvailable e demand
        (flowBudget τ (Fintype.card G)) s} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-((τ : ℝ)^18 / 32000) * (Fintype.card G : ℝ)) := by
  have hp' := originalProcess_measurePreserving (G := G)
    q η a b hq0 hq1 hη0 hη1 ha hb hab
  rw [← hp'.measureReal_preimage (by measurability)]
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (full_sample_nine_orbit_budget hodd hn q η a b hq0 hq1 hη0 hη1 ha hb hab
      p τ hτ h hP hQ e demand hcard hprob)
  intro ω hbad hgood
  exact hbad ⟨ω, rfl, hgood⟩

/-- uniform exact-matching theorem's literal parameters, with one q-dependent threshold and a
group-independent polynomial bound on supplied query families. -/
theorem original_nine_orbit_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) (C : ℝ) (k : ℕ) :
    ∃ N : ℕ, ∀ (G : Type*) [Fintype G] [AddCommGroup G]
      (Q I J : Type*) [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
      (hodd : Odd (Fintype.card G))
      (hn : max N 2000 ≤ Fintype.card G)
      (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label),
      Fintype.card I = Fintype.card G / 1000 →
      (∀ u i, (tauNN q : ℝ)^9 ≤ successProbability (pNN q) (tauNN q) (demand u i)) →
      (Fintype.card Q : ℝ) ≤ C * (Fintype.card G : ℝ)^k →
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsAvailable e demand
          (flowBudget (tau q) (Fintype.card G)) s} ≤
        Real.exp (-(xi q^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := sampling_rates_pay_polynomial_union q C k hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ Q I J _ _ _ _ hodd hn e demand hcard hprob hqueries
  have hn2000 : 2000 ≤ Fintype.card G := (le_max_right N 2000).trans hn
  have hnN : N ≤ Fintype.card G := (le_max_left N 2000).trans hn
  obtain ⟨hη0,hη1,ha,hb,hab,hp,hcat,hP,hQ⟩ :=
    samplingParameters_admissible q hq0 hq1
  have hτ0 : 0 < (tauNN q : ℝ) := by
    change 0 < tau q
    unfold tau p SamplingConstants.rho eta
    positivity
  have hbase := original_sample_nine_orbit_budget hodd hn2000 q eta (1/4)
    (tau q / SamplingConstants.rho q)
    (le_of_lt hq0) hq1 hη0 hη1 ha hb hab (pNN q) (tauNN q) hτ0 hcat hP hQ
    e demand hcard hprob
  have hqueries' := mul_le_mul_of_nonneg_right hqueries
    (le_of_lt (Real.exp_pos (-((tau q)^18 / 32000) * (Fintype.card G : ℝ))))
  exact hbase.trans (hqueries'.trans (hN (Fintype.card G) hnN).1)

end
end EndpointFullProduct
