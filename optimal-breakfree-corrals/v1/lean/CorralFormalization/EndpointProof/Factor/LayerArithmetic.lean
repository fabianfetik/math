import CorralFormalization.EndpointProof.Factor.FactorParameters

/-!
# Layer division and the true remainder

The finite arithmetic behind the paper's division of the target vertex set
into equally sized layers. This proves no existence statement about the
layers or their edges.
-/

namespace EndpointFactor.LayerArithmetic

/-- After division into `k` layers, the unused group points are the original
missing points plus the exact division remainder. -/
theorem layer_remainder (n W k : ℕ) (hW : W ≤ n) (hk : 0 < k) :
    W % k < k ∧ W = k * (W / k) + W % k ∧
      n - k * (W / k) = (n - W) + W % k := by
  have hdiv := Nat.mod_add_div W k
  have hrem := Nat.mod_lt W hk
  constructor
  · exact hrem
  constructor <;> omega

/-- The paper's `d ≤ 2 ε n` follows once both the original deficit and
one layer's rounding remainder have each been budgeted by `ε n`. -/
theorem layer_remainder_real_bound (n W k : ℕ) (ε : ℝ)
    (hW : W ≤ n) (hk : 0 < k)
    (hdeficit : ((n - W : ℕ) : ℝ) ≤ ε * n)
    (hround : (k : ℝ) ≤ ε * n) :
    ((n - k * (W / k) : ℕ) : ℝ) ≤ 2 * ε * n := by
  obtain ⟨hrem, _, htotal⟩ := layer_remainder n W k hW hk
  have hrem_real : ((W % k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrem.le
  rw [htotal, Nat.cast_add]
  linarith

end EndpointFactor.LayerArithmetic
