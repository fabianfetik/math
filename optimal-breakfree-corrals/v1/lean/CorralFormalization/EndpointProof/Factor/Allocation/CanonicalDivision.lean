import CorralFormalization.EndpointProof.Factor.Allocation.WholeOrdinary
import CorralFormalization.EndpointProof.Factor.Allocation.Asymptotics
import CorralFormalization.EndpointProof.Factor.LayerArithmetic

/-! # Canonical division of an arbitrary later target -/

open scoped Classical
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointFactor.LayerArithmetic
noncomputable section
variable {G : Type*} [Fintype G] [DecidableEq G]

/-- The actual floor quotient, remainder and deficit satisfy every finite
division premise used by the preparation once `k ≤ εn`. -/
theorem canonical_division_bounds (W : Finset G) (k : ℕ) (ε : ℝ)
    (hk : 0 < k) (hW : (1-ε)*(Fintype.card G : ℝ) ≤ (W.card : ℝ))
    (hkbound : (k : ℝ) ≤ ε*Fintype.card G) :
    let ℓ := W.card / k
    let w := W.card % k
    let d := Fintype.card G - k*ℓ
    W.card = k*ℓ+w ∧ k*ℓ+d = Fintype.card G ∧
    ((w : ℝ) ≤ ε*Fintype.card G) ∧ ((d : ℝ) ≤ 2*ε*Fintype.card G) := by
  dsimp only
  have hWcard : W.card ≤ Fintype.card G := Finset.card_le_univ W
  obtain ⟨hrem, hdiv, hdef⟩ := layer_remainder (Fintype.card G) W.card k hWcard hk
  have hdiv' : k*(W.card/k)+(Fintype.card G-k*(W.card/k)) = Fintype.card G := by omega
  have hmissing : (((Fintype.card G-W.card : ℕ) : ℝ)) ≤ ε*Fintype.card G := by
    rw [Nat.cast_sub hWcard]
    nlinarith
  have hd := layer_remainder_real_bound (Fintype.card G) W.card k ε hWcard hk hmissing hkbound
  have hw : ((W.card % k : ℕ) : ℝ) ≤ ε*Fintype.card G := by
    have hr : ((W.card % k : ℕ) : ℝ) ≤ k := by exact_mod_cast hrem.le
    exact hr.trans hkbound
  exact ⟨hdiv, hdiv', hw, hd⟩

end
end EndpointFactor.Allocation
