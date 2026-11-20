import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# The literal connector-free prefix radius

The connector-free prefix construction in Sections 8.1 and
8.5, has `3*r*r + 8` prefix vertices and `3*r*r + 7` edges. Its radius is
`floor (sqrt ((ε*n - 7)/3))`, unlike the maintained earlier connector-prefix
radius `floor (sqrt (ε*n/4 - 2))`.

This file proves only the numerical parameter choice and its rounding losses.
It does not construct the rainbow prefix, its physical row tiles, or an
injection into asymmetric physical corral orbits.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

/-- The natural-valued version of the exact floor printed in Theorem 10.
The following theorem identifies it with the integer floor as well. -/
noncomputable def radius (ε : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.sqrt ((ε * (n : ℝ) - 7) / 3)⌋₊

theorem radius_intFloor (ε : ℝ) (n : ℕ) :
    (radius ε n : ℤ) = ⌊Real.sqrt ((ε * (n : ℝ) - 7) / 3)⌋ :=
  Int.natCast_floor_eq_floor (Real.sqrt_nonneg _)

theorem radius_le_sqrt (ε : ℝ) (n : ℕ) :
    (radius ε n : ℝ) ≤ Real.sqrt ((ε * (n : ℝ) - 7) / 3) :=
  Nat.floor_le (Real.sqrt_nonneg _)

theorem radius_sqrt_sub_one_lt (ε : ℝ) (n : ℕ) :
    Real.sqrt ((ε * (n : ℝ) - 7) / 3) - 1 < (radius ε n : ℝ) := by
  have h := Nat.lt_floor_add_one (Real.sqrt ((ε * (n : ℝ) - 7) / 3))
  change Real.sqrt ((ε * (n : ℝ) - 7) / 3) <
    (radius ε n : ℝ) + 1 at h
  linarith

/-- The new radius is exactly the greatest natural radius whose edge budget
fits. The threshold is necessary for the zero-radius case as well. -/
theorem le_radius_iff_budget {ε : ℝ} {n k : ℕ}
    (hn : 7 ≤ ε * (n : ℝ)) :
    k ≤ radius ε n ↔
      ((3 * k * k + 7 : ℕ) : ℝ) ≤ ε * (n : ℝ) := by
  have hrad : 0 ≤ (ε * (n : ℝ) - 7) / 3 := by linarith
  have hsqrt := Real.sq_sqrt hrad
  have hsnonneg := Real.sqrt_nonneg ((ε * (n : ℝ) - 7) / 3)
  constructor
  · intro hk
    have hcast : (k : ℝ) ≤ radius ε n := by exact_mod_cast hk
    have hle := hcast.trans (radius_le_sqrt ε n)
    have hsq : (k : ℝ)^2 ≤ (ε * (n : ℝ) - 7) / 3 := by
      nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    push_cast
    nlinarith
  · intro hk
    apply Nat.le_floor
    apply Real.le_sqrt_of_sq_le
    push_cast at hk
    nlinarith

theorem radius_budget {ε : ℝ} {n : ℕ}
    (hn : 7 ≤ ε * (n : ℝ)) :
    ((3 * radius ε n * radius ε n + 7 : ℕ) : ℝ) ≤
      ε * (n : ℝ) :=
  (le_radius_iff_budget hn).mp le_rfl

/-- A finite, explicit form of all radius conditions used in Section 8.5.
In particular the height requirement is stronger than `n ≥ 200*r²` used by
the connector-free prefix. This theorem has no endpoint or counting premise. -/
theorem radius_bounds {ε : ℝ} {n : ℕ}
    (hε : ε ≤ (1 : ℝ) / 100) (hn : 34 ≤ ε * (n : ℝ)) :
    3 ≤ radius ε n ∧
      300 * radius ε n * radius ε n + 700 ≤ n ∧
      ((3 * radius ε n * radius ε n + 7 : ℕ) : ℝ) ≤
        ε * (n : ℝ) := by
  have hthree : (3 : ℝ) ≤ Real.sqrt ((ε * (n : ℝ) - 7) / 3) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hr : 3 ≤ radius ε n := Nat.le_floor hthree
  have hbudget := radius_budget (by linarith : 7 ≤ ε * (n : ℝ))
  have heprod : ε * (n : ℝ) ≤ ((1 : ℝ) / 100) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg n)
  have hlarge : (300 : ℝ) * radius ε n * radius ε n + 700 ≤ n := by
    push_cast at hbudget
    nlinarith
  exact ⟨hr, by exact_mod_cast hlarge, hbudget⟩

/-- The rounding error is strictly less than twice the square root before
the constant term is included. This directly supports the paper's
`r_*² = ε*n/3 + O(√n)` assertion. -/
theorem radius_square_bounds {ε : ℝ} {n : ℕ}
    (hn : 10 ≤ ε * (n : ℝ)) :
    ε * (n : ℝ) / 3 - 7 / 3 - 2 * Real.sqrt ((ε * (n : ℝ) - 7) / 3) <
        (radius ε n : ℝ)^2 ∧
      (radius ε n : ℝ)^2 ≤ ε * (n : ℝ) / 3 - 7 / 3 := by
  have hrad : 0 ≤ (ε * (n : ℝ) - 7) / 3 := by linarith
  have hone : (1 : ℝ) ≤ Real.sqrt ((ε * (n : ℝ) - 7) / 3) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsqrt := Real.sq_sqrt hrad
  have hsnonneg := Real.sqrt_nonneg ((ε * (n : ℝ) - 7) / 3)
  have hfloor := radius_le_sqrt ε n
  have hrnonneg : (0 : ℝ) ≤ radius ε n := Nat.cast_nonneg _
  have hlower := radius_sqrt_sub_one_lt ε n
  have hlowsq : (Real.sqrt ((ε * (n : ℝ) - 7) / 3) - 1)^2 ≤
      (radius ε n : ℝ)^2 :=
    (sq_le_sq₀ (by linarith) hrnonneg).mpr hlower.le
  constructor <;> nlinarith

/-- A concrete natural threshold for the finite budget conditions. -/
theorem radius_bounds_of_ceil_threshold {ε : ℝ} {n : ℕ}
    (hεpos : 0 < ε) (hε : ε ≤ (1 : ℝ) / 100)
    (hn : ⌈34 / ε⌉₊ ≤ n) :
    3 ≤ radius ε n ∧
      300 * radius ε n * radius ε n + 700 ≤ n ∧
      ((3 * radius ε n * radius ε n + 7 : ℕ) : ℝ) ≤
        ε * (n : ℝ) := by
  apply radius_bounds hε
  have hceil : 34 / ε ≤ (⌈34 / ε⌉₊ : ℝ) := Nat.le_ceil _
  have hcast : (⌈34 / ε⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simpa only [mul_comm] using (div_le_iff₀ hεpos).mp (hceil.trans hcast)

theorem radius_eventually {ε : ℝ}
    (hεpos : 0 < ε) (hε : ε ≤ (1 : ℝ) / 100) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      3 ≤ radius ε n ∧
        300 * radius ε n * radius ε n + 700 ≤ n ∧
        ((3 * radius ε n * radius ε n + 7 : ℕ) : ℝ) ≤
          ε * (n : ℝ) :=
  ⟨⌈34 / ε⌉₊, fun _ hn => radius_bounds_of_ceil_threshold hεpos hε hn⟩

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
