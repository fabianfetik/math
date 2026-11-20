import CorralFormalization.EndpointProof.Probability.SamplingParameterChoices

/-!
The selector external-forbidden-set margin relative to the larger primitive
availability budget. This only pays numerical support; it constructs no
selector, helper pair, or additional reservoir candidate.
-/

namespace CorralFormalization.EndpointProof.RateBudget

noncomputable section

/-- Integer form of the smaller external support allowance `C_P`. -/
def selectorExternalBudget (p : ℝ) (n : ℕ) : ℕ :=
  ⌊p^4 * (n : ℝ) / 10^12⌋₊

/-- For integer support sizes the written real bound and its floor agree. -/
theorem le_selectorExternalBudget_iff (p : ℝ) (n m : ℕ) :
    m ≤ selectorExternalBudget p n ↔ (m : ℝ) ≤ p^4 * (n : ℝ) / 10^12 := by
  unfold selectorExternalBudget
  exact Nat.le_floor_iff (by positivity)

/-- For each fixed positive density the larger P primitive budget eventually
contains the external budget plus 4000 additional numerical coordinates. -/
theorem selector_external_slack (p : ℝ) (hp : 0 < p) :
    ∃ N : ℕ, ∀ n ≥ N,
      selectorExternalBudget p n + 4000 ≤ selectorBudget p n := by
  let gap : ℝ := p^4 / 10^10 - p^4 / 10^12
  have hp4 : 0 < p^4 := pow_pos hp _
  have hgap : 0 < gap := by dsimp [gap]; nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (4000 / gap)
  refine ⟨N, ?_⟩
  intro n hn
  have hnreal : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hNgap : (4000 : ℝ) < gap * N := by
    simpa only [mul_comm] using (div_lt_iff₀ hgap).mp hN
  have hngap : (4000 : ℝ) ≤ gap * n := by nlinarith
  have hsmall : (selectorExternalBudget p n : ℝ) ≤ p^4 * (n : ℝ) / 10^12 := by
    unfold selectorExternalBudget
    exact Nat.floor_le (by positivity)
  unfold selectorBudget
  apply Nat.le_floor
  push_cast
  dsimp [gap] at hngap
  nlinarith

namespace SamplingConstants

/-- The paper's literal `p(q)` satisfies the same asymptotic margin. -/
theorem selector_external_budget_slack (q : ℝ) (hq : 0 < q) :
    ∃ N : ℕ, ∀ n ≥ N,
      selectorExternalBudget (p q) n + 4000 ≤ selectorBudget (p q) n := by
  apply selector_external_slack
  unfold p rho eta
  positivity

end SamplingConstants
end
end CorralFormalization.EndpointProof.RateBudget
