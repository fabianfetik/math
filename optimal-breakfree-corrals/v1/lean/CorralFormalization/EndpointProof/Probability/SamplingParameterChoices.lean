import CorralFormalization.EndpointProof.Probability.SelectorAvailability

/-!
Admissibility of the exact exact-matching parameters for the actual sampling interface.
This supplies no orbit packings and no exact-matching theorem.
-/

open scoped NNReal

namespace CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

def pNN (q : ℝ) : ℝ≥0 := ⟨p q, by unfold p rho; positivity⟩
def tauNN (q : ℝ) : ℝ≥0 := ⟨tau q, by unfold tau p rho; positivity⟩

/-- All categorical parameter conditions required by the full-sample
availability theorem, for the literal exact-matching constants. The P/Q relabelling
probabilities are `1/4` and `τ/ρ`. -/
theorem samplingParameters_admissible (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    0 ≤ eta ∧ eta ≤ 1 ∧
    (0 : ℝ) ≤ 1/4 ∧ 0 ≤ tau q / rho q ∧ 1/4 + tau q / rho q ≤ 1 ∧
    0 < (pNN q : ℝ) ∧ 3 * pNN q + 3 * tauNN q ≤ 1 ∧
    (pNN q : ℝ) = EndpointOriginalReservoir.rho q eta * (1/4) ∧
    (tauNN q : ℝ) = EndpointOriginalReservoir.rho q eta * (tau q / rho q) := by
  have hη0 : 0 < eta := by norm_num [eta]
  have hη1 : eta ≤ 1 := by norm_num [eta]
  have hηq0 : 0 < eta*q := mul_pos hη0 hq0
  have hηq1 : eta*q ≤ 1 := by norm_num [eta] at *; nlinarith
  have hsq : (eta*q)^2 ≤ 1 := pow_le_one₀ (le_of_lt hηq0) hηq1
  have hρ0 : 0 < rho q := by unfold rho; positivity
  have hρ1 : rho q ≤ 1/9 := by unfold rho; nlinarith
  have hp0 : 0 < p q := by unfold p; positivity
  have hp1 : p q ≤ 1/36 := by unfold p; nlinarith
  have hpone : p q ≤ 1 := by linarith
  have hp4 : (p q)^4 ≤ p q := pow_le_of_le_one (le_of_lt hp0) hpone (by norm_num)
  have ht0 : 0 < tau q := by unfold tau; positivity
  have htp : tau q ≤ p q := by unfold tau; nlinarith
  have hratio0 : 0 ≤ tau q / rho q := by positivity
  have hratio1 : tau q / rho q ≤ 1/4 := by
    apply (div_le_iff₀ hρ0).2
    unfold p at htp
    linarith
  have hsum : 3 * p q + 3 * tau q ≤ 1 := by linarith
  have hsumNN : 3 * pNN q + 3 * tauNN q ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    change (3 : ℝ) * p q + 3 * tau q ≤ 1
    exact hsum
  have heqP : (pNN q : ℝ) = EndpointOriginalReservoir.rho q eta * (1/4) := by
    change p q = EndpointOriginalReservoir.rho q eta * (1/4)
    unfold p rho EndpointOriginalReservoir.rho
    ring
  have heqQ : (tauNN q : ℝ) =
      EndpointOriginalReservoir.rho q eta * (tau q / rho q) := by
    change tau q = EndpointOriginalReservoir.rho q eta * (tau q / rho q)
    have hrho : EndpointOriginalReservoir.rho q eta = rho q := by rfl
    rw [hrho]
    field_simp [ne_of_gt hρ0]
  refine ⟨le_of_lt hη0, hη1, by norm_num, hratio0, by linarith,
    ?_, hsumNN, heqP, heqQ⟩
  exact hp0

end
end CorralFormalization.EndpointProof.RateBudget.SamplingConstants
