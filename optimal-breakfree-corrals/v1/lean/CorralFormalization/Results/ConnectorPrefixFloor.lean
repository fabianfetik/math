import CorralFormalization.DiversityCompletion.CyclicEndpointConnectorOrbits
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

/-! Exact floor parameter choice for the factorial-order lower bound.
The endpoint-completion statement remains an explicit premise. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply
  LatinPrefixSupply.FixedConnectorPrefix CorralLatinTailMarker PhysicalCorral

/-- The natural-valued version of the connector-prefix floor. The square root is
nonnegative, so it agrees with the integer floor (proved below). -/
noncomputable def connectorPrefixRadius (ε : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.sqrt (ε * (n : ℝ) / 4 - 2)⌋₊

theorem connectorPrefixRadius_intFloor (ε : ℝ) (n : ℕ) :
    (connectorPrefixRadius ε n : ℤ) = ⌊Real.sqrt (ε * (n : ℝ) / 4 - 2)⌋ :=
  Int.natCast_floor_eq_floor (Real.sqrt_nonneg _)

theorem connectorPrefixRadius_sqrt_sub_one_lt (ε : ℝ) (n : ℕ) :
    Real.sqrt (ε * (n : ℝ) / 4 - 2) - 1 < (connectorPrefixRadius ε n : ℝ) := by
  have h := Nat.lt_floor_add_one (Real.sqrt (ε * (n : ℝ) / 4 - 2))
  change Real.sqrt (ε * (n : ℝ) / 4 - 2) < (connectorPrefixRadius ε n : ℝ) + 1 at h
  linarith

/-- The lower square estimate retains the exact error term needed for the
asymptotic deduction. Its premise only makes the radicand at least one. -/
theorem connectorPrefixRadius_square_bounds {ε : ℝ} {n : ℕ}
    (hn : 12 ≤ ε * (n : ℝ)) :
    ε * (n : ℝ) / 4 - 2 - 2 * Real.sqrt (ε * (n : ℝ) / 4 - 2) ≤
        (connectorPrefixRadius ε n : ℝ)^2 ∧
      (connectorPrefixRadius ε n : ℝ)^2 ≤ ε * (n : ℝ) / 4 - 2 := by
  have hrad : 0 ≤ ε * (n : ℝ) / 4 - 2 := by linarith
  have hone : (1 : ℝ) ≤ Real.sqrt (ε * (n : ℝ) / 4 - 2) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hfloor : (connectorPrefixRadius ε n : ℝ) ≤
      Real.sqrt (ε * (n : ℝ) / 4 - 2) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hsqrt := Real.sq_sqrt hrad
  have hrnonneg : (0 : ℝ) ≤ connectorPrefixRadius ε n := Nat.cast_nonneg _
  have hlower := connectorPrefixRadius_sqrt_sub_one_lt ε n
  have hsqLower := (sq_le_sq₀ (by linarith :
    0 ≤ Real.sqrt (ε * (n : ℝ) / 4 - 2) - 1) hrnonneg).mpr hlower.le
  constructor <;> nlinarith [Real.sqrt_nonneg (ε * (n : ℝ) / 4 - 2)]

/-- All finite numerical obligations for the connector-prefix parameter. -/
theorem connectorPrefixRadius_bounds {ε : ℝ} {n : ℕ}
    (hε : ε ≤ (1 : ℝ) / 100) (hn : 24 ≤ ε * (n : ℝ)) :
    2 ≤ connectorPrefixRadius ε n ∧
      100 * connectorPrefixRadius ε n * connectorPrefixRadius ε n ≤ n ∧
      ((4 * connectorPrefixRadius ε n * connectorPrefixRadius ε n + 6 : ℕ) : ℝ) ≤
        ε * (n : ℝ) := by
  have hrad : 0 ≤ ε * (n : ℝ) / 4 - 2 := by linarith
  have htwo : (2 : ℝ) ≤ Real.sqrt (ε * (n : ℝ) / 4 - 2) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hr : 2 ≤ connectorPrefixRadius ε n := Nat.le_floor htwo
  have hfloor : (connectorPrefixRadius ε n : ℝ) ≤
      Real.sqrt (ε * (n : ℝ) / 4 - 2) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hsqrt := Real.sq_sqrt hrad
  have hrnonneg : (0 : ℝ) ≤ connectorPrefixRadius ε n := Nat.cast_nonneg _
  have hsq : (connectorPrefixRadius ε n : ℝ)^2 ≤ ε * (n : ℝ) / 4 - 2 := by
    nlinarith [Real.sqrt_nonneg (ε * (n : ℝ) / 4 - 2)]
  have heprod : ε * (n : ℝ) ≤ ((1 : ℝ) / 100) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg n)
  have hlarge : (100 : ℝ) * connectorPrefixRadius ε n * connectorPrefixRadius ε n ≤ n := by
    nlinarith
  refine ⟨hr, ?_, ?_⟩
  · exact_mod_cast hlarge
  · push_cast
    nlinarith

/-- An explicit threshold in n exists for every positive epsilon. -/
theorem connectorPrefixRadius_eventually {ε : ℝ} (hεpos : 0 < ε)
    (hε : ε ≤ (1 : ℝ) / 100) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 ≤ connectorPrefixRadius ε n ∧
        100 * connectorPrefixRadius ε n * connectorPrefixRadius ε n ≤ n ∧
        ((4 * connectorPrefixRadius ε n * connectorPrefixRadius ε n + 6 : ℕ) : ℝ) ≤
          ε * (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (24 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  apply connectorPrefixRadius_bounds hε
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht : 24 ≤ (N : ℝ) * ε := (div_le_iff₀ hεpos).mp hN
  nlinarith

/-- The complete fixed-constant content of Hypothesis 9. Introducing this
name is only a definitional refactoring of its existing quantifiers. -/
def OddCyclicRainbowEndpointCompletionAt (ε0 : ℝ) (n0 : ℕ) : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → n0 ≤ n →
    ∀ (W D : Finset (ZMod n)) (x y : ZMod n),
      (n : ℝ) - ε0*(n : ℝ) ≤ (W.card : ℝ) →
      x ∈ W → y ∈ W → x ≠ y → 0 ∉ D →
      D.card+1 = W.card → (∑ z ∈ D, z) = y-x → EndpointPathClaim W D x y

theorem oddCyclicEndpointCompletion_iff : OddCyclicRainbowEndpointCompletion ↔
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 := Iff.rfl

/-- Constant-preserving version of oddCyclicEndpointCompletion_local. In contrast
to its existential interface this lemma can be applied at any specified
genuine cyclic endpoint witness without replacing epsilon0. -/
theorem oddCyclicEndpointCompletionAt_local {ε0 : ℝ} {n0 n t : ℕ} [NeZero n]
    (H : OddCyclicRainbowEndpointCompletionAt ε0 n0) (hodd : Odd n) (hn0 : n0 ≤ n)
    (htn : t ≤ n) (ht : (t : ℝ) ≤ ε0 * (n : ℝ)) :
    EndpointCompletionAt n t := by
  refine ⟨?_⟩
  intro W D x y hcard hx hy hxy hz hcount hsum
  have hc : ((n-t : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub htn] at hc
  have hd : (n : ℝ) - ε0*(n : ℝ) ≤ (W.card : ℝ) := by linarith
  exact H n hodd hn0 W D x y hd hx hy hxy hz hcount hsum

/-- The connector-prefix floor choice closes the actual census bound at every
sufficiently large height, at any specified genuine cyclic endpoint constant. -/
theorem oddCyclicEndpointCompletionAt_floor_total_lower {ε0 : ℝ} {n0 : ℕ}
    (H : OddCyclicRainbowEndpointCompletionAt ε0 n0) {ε : ℝ}
    (hεpos : 0 < ε) (hε : ε ≤ min ε0 ((1 : ℝ) / 100)) :
    ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
      latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤
        PhysicalCensus.A_h h (hh0.trans hh) := by
  obtain ⟨N, hN⟩ := connectorPrefixRadius_eventually hεpos (hε.trans (min_le_right _ _))
  refine ⟨max 2 (max n0 N), by omega, ?_⟩
  intro h hh
  let n := 2*h-1
  let r := connectorPrefixRadius ε n
  have hh2 : 2 ≤ h := by omega
  have hn : n = 2*h-1 := rfl
  have hn0 : n0 ≤ n := by dsimp [n]; omega
  have hnN : N ≤ n := by dsimp [n]; omega
  obtain ⟨hr, hlarge, hbudget⟩ := hN n hnN
  have hr2 : 2 ≤ r := hr
  have ht : 4*r*r+6 ≤ n := by nlinarith
  have heprod : ε * (n : ℝ) ≤ ε0 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (hε.trans (min_le_left _ _)) (Nat.cast_nonneg n)
  have : NeZero h := ⟨by omega⟩
  have : NeZero n := ⟨by dsimp [n]; omega⟩
  have : NeZero r := ⟨by omega⟩
  have : NeZero (h*n) := ⟨Nat.mul_ne_zero (NeZero.ne h) (NeZero.ne n)⟩
  have hodd : Odd n := by
    refine ⟨h-1, ?_⟩
    dsimp [n]
    omega
  have Hlocal : EndpointCompletionAt n (4*r*r+6) :=
    oddCyclicEndpointCompletionAt_local H hodd hn0 ht (hbudget.trans heprod)
  exact endpoint_hypothesis_total_lower hr2 hn hlarge Hlocal

/-- Hypothesis 9 supplies its actual epsilon0 and n0, which are retained
as witnesses together with the Theorem 10 conclusion. -/
theorem oddCyclicEndpointCompletion_floor_total_lower (H : OddCyclicRainbowEndpointCompletion) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ) / 100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤
            PhysicalCensus.A_h h (hh0.trans hh) := by
  obtain ⟨ε0, hε0, n0, H0⟩ := oddCyclicEndpointCompletion_iff.mp H
  exact ⟨ε0, hε0, n0, H0, fun ε hεpos hε =>
    oddCyclicEndpointCompletionAt_floor_total_lower H0 hεpos hε⟩

#print axioms connectorPrefixRadius_intFloor
#print axioms connectorPrefixRadius_sqrt_sub_one_lt
#print axioms connectorPrefixRadius_square_bounds
#print axioms connectorPrefixRadius_bounds
#print axioms connectorPrefixRadius_eventually
#print axioms oddCyclicEndpointCompletion_iff
#print axioms oddCyclicEndpointCompletionAt_local
#print axioms oddCyclicEndpointCompletionAt_floor_total_lower
#print axioms oddCyclicEndpointCompletion_floor_total_lower

end CorralFormalization.LatinCompletion.TerraceCompletion
