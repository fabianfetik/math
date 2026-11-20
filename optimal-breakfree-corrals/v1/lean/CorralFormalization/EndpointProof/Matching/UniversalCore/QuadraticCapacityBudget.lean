import CorralFormalization.EndpointProof.Matching.UniversalCore.TetrahedronToCore
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
noncomputable section

/-- Literal integer budgets for the quadratic-capacity core. -/
def quadraticCoverBudget (τ : ℝ) (n : ℕ) : ℕ := ⌊τ^2 * n / 1000⌋₊
def quadraticCoreCapacity (τ : ℝ) (n : ℕ) : ℕ := ⌊(1 / 10^6 : ℝ) * τ^2 * n⌋₊
def paddingQuota (τ : ℝ) (n : ℕ) : ℕ := ⌊τ * n / 10000⌋₊
def paddingBufferCount (τ : ℝ) (n : ℕ) : ℕ := ⌊τ * n / 1000⌋₊

/-- One explicit large-order threshold pays the actual integer floors in
absorber: the cover queries, the 4/3 residual-to-padding comparison, and the
quadratic numerical-deletion radius. It does not supply graph or buffers. -/
theorem quadratic_capacity_budgets (τ : ℝ) (n : ℕ) (u : ℕ)
    (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3)
    (hnlarge : (4000 : ℝ) ≤ τ^2 * n)
    (hu : u ≤ quadraticCoreCapacity τ n) :
    2 * u + 20 * quadraticCoreCapacity τ n ≤ quadraticCoverBudget τ n ∧
    4 * quadraticCoreCapacity τ n ≤ 3 * paddingQuota τ n ∧
    (quadraticCoverBudget τ n : ℝ) ≤ τ^2 * n / 192 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hc : (quadraticCoreCapacity τ n : ℝ) ≤ (1 / 10^6 : ℝ) * τ^2 * n := by
    unfold quadraticCoreCapacity
    exact Nat.floor_le (by positivity)
  have hqL : τ^2 * n / 1000 < (quadraticCoverBudget τ n : ℝ) + 1 := by
    unfold quadraticCoverBudget
    exact Nat.lt_floor_add_one _
  have hqU : (quadraticCoverBudget τ n : ℝ) ≤ τ^2 * n / 1000 := by
    unfold quadraticCoverBudget
    exact Nat.floor_le (by positivity)
  have hkL : τ * n / 10000 < (paddingQuota τ n : ℝ) + 1 := by
    unfold paddingQuota
    exact Nat.lt_floor_add_one _
  have hu' : (u : ℝ) ≤ quadraticCoreCapacity τ n := Nat.cast_le.mpr hu
  have ht : τ^2 * n ≤ τ * n / 3 := by
    have hx : 0 ≤ ((1 / 3 : ℝ) - τ) * τ * n := by positivity
    nlinarith
  have hnonneg : 0 ≤ τ^2 * n := by positivity
  constructor
  · have hreal : (2 : ℝ) * u + 20 * quadraticCoreCapacity τ n ≤
        quadraticCoverBudget τ n := by nlinarith
    exact_mod_cast hreal
  constructor
  · have hreal : (4 : ℝ) * quadraticCoreCapacity τ n ≤
        3 * paddingQuota τ n := by nlinarith
    exact_mod_cast hreal
  · nlinarith

/-- The paper's chosen buffer count is at least five times its padding
quota, once the same explicit large-order threshold holds. -/
theorem padding_buffer_floor_bound (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3)
    (hnlarge : (4000 : ℝ) ≤ τ^2 * n) :
    5 * paddingQuota τ n ≤ paddingBufferCount τ n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have ht : τ^2 * n ≤ τ * n / 3 := by
    have hx : 0 ≤ ((1 / 3 : ℝ) - τ) * τ * n := by positivity
    nlinarith
  have hk : (paddingQuota τ n : ℝ) ≤ τ * n / 10000 := by
    unfold paddingQuota
    exact Nat.floor_le (by positivity)
  have hL : τ * n / 1000 < (paddingBufferCount τ n : ℝ) + 1 := by
    unfold paddingBufferCount
    exact Nat.lt_floor_add_one _
  have hreal : (5 : ℝ) * paddingQuota τ n ≤ paddingBufferCount τ n := by nlinarith
  exact_mod_cast hreal

end
end EndpointMatching.UniversalCore
