import OccurrenceSpans
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Definitions shared by the complete five-task formalization. -/

namespace RealPinwheel

variable {α : Type*} [DecidableEq α]

/-- Number of services of one task in a half-open integer window. -/
noncomputable def serviceCount (S : ℤ → α) (i : α) (m L : ℤ) : ℕ :=
  windowCount (fun t => S t = i) m L

/-- The original real-period requirement, including every positive scale. -/
def ValidPeriods (a : α → ℝ) (S : ℤ → α) : Prop :=
  ∀ (i : α) (m : ℤ) (ell : ℕ), 0 < ell →
    ell ≤ serviceCount S i m ⌈(ell : ℝ) * a i⌉

/-- Equivalent count-rate condition: `floor (L * r i) ≤ count`.
The strict real inequality avoids unnecessary casts in construction lemmas. -/
def ValidRates (r : α → ℝ) (S : ℤ → α) : Prop :=
  ∀ (i : α) (m : ℤ) (L : ℕ),
    (L : ℝ) * r i < (serviceCount S i m (L : ℤ) : ℝ) + 1

def SchedulableRates (r : α → ℝ) : Prop := ∃ S : ℤ → α, ValidRates r S

structure RateCap where
  bound : ℚ
  closed : Bool
  deriving DecidableEq, Repr

def RateCap.Holds (c : RateCap) (x : ℝ) : Prop :=
  if c.closed then x ≤ (c.bound : ℝ) else x < (c.bound : ℝ)

def CapsHold (caps : Fin 5 → RateCap) (r : Fin 5 → ℝ) : Prop :=
  ∀ i, (caps i).Holds (r i)

def LinearLe (v : Fin 5 → ℚ) (r : Fin 5 → ℝ) (b : ℚ) : Prop :=
  (∑ i, (v i : ℝ) * r i) ≤ (b : ℝ)

def OrderedFive (r : Fin 5 → ℝ) : Prop :=
  r 1 ≤ r 0 ∧ r 2 ≤ r 1 ∧ r 3 ≤ r 2 ∧ r 4 ≤ r 3

def NormalizedFive (r : Fin 5 → ℝ) : Prop :=
  OrderedFive r ∧ 0 < r 4 ∧ (∑ i, r i) = (5 : ℝ) / 6

end RealPinwheel
