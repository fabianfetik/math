import CorralFormalization.EndpointProof.Matching.UniversalCore.RawSampleAlignment
import CorralFormalization.EndpointProof.Matching.UniversalCore.CoreResidualCapacity
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.RawAdapter

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.Rounding
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section
universe u

/-- The physical exact receiver, now connected to the proved common core
and raw-event inputs. The only remaining local supplier is the actual
fractional-perfect weights on every nearby later target; AKS is the explicit
external input. The threshold is uniform over group types. -/
theorem physical_exact_on_shared_core_and_fractionalWeights
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      N ≤ Fintype.card G →
      ∀ ω : FullSample G,
        UniversalCoreEvent (tau q) ω →
        fractionalRawEvent q (originalProcess ω) →
        ActualFractionalWeights (signedRawTarget (originalProcess ω)) ∅ q
          (EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ)) →
      ∀ X Y C : Finset G,
        Disjoint X Y → (0 : G) ∉ C → X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        (physicalEditDistance (originalTailSet (originalProcess ω))
          (originalHeadSet (originalProcess ω)) (originalColourSet (originalProcess ω)) X Y C : ℝ) ≤
          (1 / 10^6 : ℝ) * kappa q * (Fintype.card G : ℝ) →
        Nonempty (PhysicalDifferenceMatching X Y C) := by
  obtain ⟨Dstar,Cstar,hDstar,hCstar,hrem⟩ := physical_actual_remainder_on_raw_event hAKS
  have hCnonneg : 0 ≤ 3 * (Real.sqrt 6 * Cstar) := by positivity
  obtain ⟨N,hN⟩ := exact_receiver_thresholds q (3 * (Real.sqrt 6 * Cstar)) Dstar hq0 hCnonneg
  refine ⟨N, ?_⟩
  intro G _ _ hn ω hcore hraw hweights X Y C hdisjoint hzero hXY hXC hchecksum hdistance
  obtain ⟨hκ,hbudget,hdegree,hcap⟩ := hN (Fintype.card G) hn
  apply physical_exact_from_universalCore q hq0 hq1 ω hcore X Y C hdistance hκ hXY hXC hchecksum
  intro A hAin hAnonzero hAbal hAsum hAsize
  have hAr : (A.card : ℝ) ≤ 16200 * tau q * (Fintype.card G : ℝ) := by
    have hcast : (A.card : ℝ) ≤ (⌊16200 * tau q * (Fintype.card G : ℝ)⌋₊ : ℝ) := by exact_mod_cast hAsize
    have hnonneg : 0 ≤ 16200 * tau q * (Fintype.card G : ℝ) := by
      unfold tau p CorralFormalization.EndpointProof.RateBudget.SamplingConstants.rho eta
      positivity
    exact hcast.trans (Nat.floor_le hnonneg)
  have hbr := core_and_edit_budget_for_fractional_supplier q hq0 hq1 (Fintype.card G)
    (physicalEditDistance (originalTailSet (originalProcess ω))
      (originalHeadSet (originalProcess ω)) (originalColourSet (originalProcess ω)) X Y C)
    A.card hdistance hAr hbudget
  have hban : ∀ z : Vertex G, ((banAt (∅ : Finset (Finset (Vertex G))) z).card : ℝ) ≤
      beta q * (Fintype.card G : ℝ) := by
    intro z
    simp [banAt, beta]
    positivity
  have hz : (zeroCharge (residual (signedTarget X Y C) A ∅) : ℝ) ≤ 3 := by
    exact_mod_cast zeroCharge_le_three (residual (signedTarget X Y C) A ∅)
  have hbudget' :
      (taggedDistance (signedRawTarget (originalProcess ω)) (signedTarget X Y C) : ℝ) +
      (A.card : ℝ) + 3 * ((emptyMatching (G := G)).edges.card : ℝ) +
      (zeroCharge (residual (signedTarget X Y C) A ∅) : ℝ) ≤
        EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ) := by
    rw [raw_taggedDistance_eq_physical]
    simp only [emptyMatching, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
    unfold EndpointFractionalRawEvent.rho
    linarith
  obtain ⟨M,hroles,htotal⟩ := hrem G q (originalProcess ω) X Y C A ∅
    (emptyMatching (G := G)) ∅ hq0 hq1 hraw hdisjoint hzero hXY hXC hchecksum
    hAbal hAsum hAin (by simp) (by simp [emptyMatching]) hban hbudget' hdegree hweights
  have hres : (residual (signedTarget X Y C) A M.covered).card ≤
      ⌊kappa q * (Fintype.card G : ℝ)⌋₊ := by
    apply hcap
    simpa only [remainderProfile, mul_assoc] using htotal
  exact ⟨M.toCompatibleNearMatching _ hres⟩

end
end EndpointMatching.UniversalCore
