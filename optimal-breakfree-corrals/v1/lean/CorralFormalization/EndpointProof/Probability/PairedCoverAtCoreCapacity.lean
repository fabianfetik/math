import CorralFormalization.EndpointProof.Flow.AbelianTransport.Access
import CorralFormalization.EndpointProof.Probability.ExponentialMargin

/-!
The existing joint selector/paired-cover event already serves forbidden sets
and residuals up to the smaller linear core capacity `kappa q * n`. This is
a paired-cover result, not a universal-absorber or endpoint theorem.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace EndpointFlow.AbelianTransport

open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
open CorralFormalization.EndpointProof.Probability.ExponentialMargin

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The sample-to-target edits plus the zero-coordinate exclusion fit the
smaller integer core capacity once `kappa*n ≥ 2`. -/
theorem edit_count_add_zero_le_core_capacity (q : ℝ) (n edits : ℕ)
    (hedits : (edits : ℝ) ≤ (1 / 10^6 : ℝ) * kappa q * (n : ℝ))
    (hn : (2 : ℝ) ≤ kappa q * (n : ℝ)) :
    edits + 1 ≤ ⌊kappa q * (n : ℝ)⌋₊ := by
  apply Nat.le_floor
  push_cast
  nlinarith

/-- Two independent later inventories at the old core capacity together
fit the existing real paired-cover budget. -/
theorem pairedCover_budget_of_core_capacity (q : ℝ) (n : ℕ)
    (u s : ℝ) (hu : u ≤ kappa q * n) (hs : s ≤ kappa q * n) :
    2*u + 20*s ≤ (tau q)^9 * n / 10^6 := by
  have htau : 0 ≤ tau q := by unfold tau p rho eta; positivity
  have hp : 0 ≤ (tau q)^9 := pow_nonneg htau _
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : (22 : ℝ) * (1 / 10^30) ≤ 1 / 10^6 := by norm_num
  have hcp := mul_le_mul_of_nonneg_right hc hp
  have hcpn := mul_le_mul_of_nonneg_right hcp hn
  unfold kappa at hu hs
  nlinarith

/-- One augmentation retains the selector and six-root data while serving
every subsequent admissible paired-cover query at the smaller core capacity.
It does not construct a core which handles all later residuals. -/
theorem original_joint_witness_covers_at_core_capacity
    (q : ℝ) (sample : OriginalSample G)
    (hgood : OriginalAdmitsSelectorsSixRootsAndCovers
      (selectorExternalBudget (p q) (Fintype.card G))
      (flowBudget (tau q) (Fintype.card G)) sample) :
    ∃ ω : FullSample G, originalProcess ω = sample ∧
      ColouredSelectors ω (selectorExternalBudget (p q) (Fintype.card G)) ∧
      SixRootSupplier (ReservoirVertex ω true) (flowBudget (tau q) (Fintype.card G)) ∧
      (∀ (S : Finset (Vertex G)), Balanced S → (∀ v ∈ S, v.2 ≠ 0) →
        (∑ v ∈ S, v.2 = 0) → ∀ U : Finset G,
        (U.card : ℝ) ≤ kappa q * (Fintype.card G : ℝ) →
        (S.card : ℝ) ≤ kappa q * (Fintype.card G : ℝ) →
        ∃ C : PairedCover (ReservoirVertex ω true) S U,
          ∀ v ∈ C.added, originalSigned v.1 sample v.2) := by
  obtain ⟨ω, hω, hselectors, hflow, hcover⟩ := hgood
  refine ⟨ω, hω, hselectors, hflow, ?_⟩
  intro S hb hnz hsum U hU hS
  have hbudget := pairedCover_budget_of_core_capacity q (Fintype.card G)
    (U.card : ℝ) (S.card : ℝ) hU hS
  have hint : 2*U.card + 20*S.card ≤ flowBudget (tau q) (Fintype.card G) := by
    have htau : 0 ≤ tau q := by unfold tau p rho eta; positivity
    apply (le_flowBudget_iff (tau q) (Fintype.card G) _ htau).2
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hbudget
  obtain ⟨C⟩ := hcover S hb hnz hsum U hint
  refine ⟨C, ?_⟩
  intro v hv
  simpa only [hω] using ReservoirVertex.originalSigned ω true v (C.added_Q v hv)

/-- A single original sample admits an augmentation with selectors, six-root
supplies, and every later paired-cover query at the smaller core capacity. -/
def OriginalAdmitsCoreCapacityCovers (q : ℝ) (sample : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = sample ∧
    ColouredSelectors ω (selectorExternalBudget (p q) (Fintype.card G)) ∧
    SixRootSupplier (ReservoirVertex ω true) (flowBudget (tau q) (Fintype.card G)) ∧
    (∀ (S : Finset (Vertex G)), Balanced S → (∀ v ∈ S, v.2 ≠ 0) →
      (∑ v ∈ S, v.2 = 0) → ∀ U : Finset G,
      (U.card : ℝ) ≤ kappa q * (Fintype.card G : ℝ) →
      (S.card : ℝ) ≤ kappa q * (Fintype.card G : ℝ) →
      ∃ C : PairedCover (ReservoirVertex ω true) S U,
        ∀ v ∈ C.added, originalSigned v.1 sample v.2)

/-- The same original-model probability bound supplies all these adaptive
paired-cover queries at once. The witnesses need not share one absorber. -/
theorem original_core_capacity_covers_probability_abelian
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G]
      (_hodd : Odd (Fintype.card G)) (_hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {sample : OriginalSample G | ¬ OriginalAdmitsCoreCapacityCovers q sample} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ := original_selectors_sixRoots_and_covers_probability_abelian q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hN G hodd hn)
  intro sample hbad hgood
  exact hbad (original_joint_witness_covers_at_core_capacity q sample hgood)

/-- The smaller-capacity joint event also retains the newly established
strict exponential reserve. A later intersection still requires bounds on
all the other events and compatible choices of augmentation. -/
theorem original_core_capacity_covers_probability_with_margin_abelian
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G]
      (_hodd : Odd (Fintype.card G)) (_hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {sample : OriginalSample G | ¬ OriginalAdmitsCoreCapacityCovers q sample} ≤
        Real.exp (-(2 * (xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ :=
    original_selectors_sixRoots_and_covers_probability_with_margin_abelian q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hN G hodd hn)
  intro sample hbad hgood
  exact hbad (original_joint_witness_covers_at_core_capacity q sample hgood)

end
end EndpointFlow.AbelianTransport
