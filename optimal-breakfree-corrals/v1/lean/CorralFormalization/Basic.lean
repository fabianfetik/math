import Mathlib

namespace CorralFormalization

/-- The width in the original Corral statement. -/
def width (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The natural partial sum through position `j`, where `j : Fin n` indexes
the entries `1,...,n`. A permutation of `Fin n` represents the actual gap
values after adding one to each value. -/
def partialSum {n : ℕ} (ρ : Equiv.Perm (Fin n)) (j : Fin n) : ℕ :=
  ∑ k : Fin n, if k.val ≤ j.val then (ρ k).val + 1 else 0

/-- The residue at `(row, position)` in the source statement, with shifts kept
as integers and reduction represented by `ZMod`. -/
def originalResidue {h n : ℕ}
    (ρ : Fin h → Equiv.Perm (Fin n)) (τ : Fin h → ℤ)
    (ij : Fin h × Fin n) : ZMod (width n) :=
  (τ ij.1 : ZMod (width n)) + (partialSum (ρ ij.1) ij.2 : ZMod (width n))

/-- Exact original witness predicate: every row is a permutation of
`{1,...,n}`, shifts are integers, and all `h*n` residues including `j=n`
are pairwise distinct. -/
def OriginalCorral (h n : ℕ) : Prop :=
  ∃ ρ : Fin h → Equiv.Perm (Fin n), ∃ τ : Fin h → ℤ,
    Function.Injective (originalResidue ρ τ)

/-- The full original existence domain and conclusion. Its proof is supplied
by `originalTarget_proved` in the Existence module. -/
def OriginalTarget : Prop :=
  ∀ h n : ℕ, 0 < h → 0 < n → 2 * h - 1 ≤ n → OriginalCorral h n

/-- For a component on a clock of width `U`, `f` is its least site and `t`
is the distance from its last site to the right cut. Its removed cyclic wrap
is `f+t`. -/
def oldWraps (fC tC fD tD : ℕ) : List ℕ := [fC + tC, fD + tD]

/-- The two new seams after concatenating the C block and then the D block. -/
def newSeams (fC tC fD tD : ℕ) : List ℕ := [tC + fD, tD + fC]

/-- Equal heads restore the two removed wraps in their original order. -/
theorem seams_restore_of_equal_heads
    (fC tC fD tD : ℕ) (h : fC = fD) :
    newSeams fC tC fD tD = oldWraps fC tC fD tD := by
  simp [newSeams, oldWraps, h, Nat.add_comm]

/-- Equal tails restore the two removed wraps in the opposite order. -/
theorem seams_restore_of_equal_tails
    (fC tC fD tD : ℕ) (h : tC = tD) :
    newSeams fC tC fD tD = (oldWraps fC tC fD tD).reverse := by
  simp [newSeams, oldWraps, h, Nat.add_comm]

/-- The seam calculation pays the complete multiset of removed wraps, whether
the endpoint match is by equal heads or equal tails. -/
theorem seam_inventory_restore_of_equal_heads
    (fC tC fD tD : ℕ) (h : fC = fD) :
    Multiset.ofList (newSeams fC tC fD tD) =
      Multiset.ofList (oldWraps fC tC fD tD) := by
  rw [seams_restore_of_equal_heads fC tC fD tD h]

theorem seam_inventory_restore_of_equal_tails
    (fC tC fD tD : ℕ) (h : tC = tD) :
    Multiset.ofList (newSeams fC tC fD tD) =
      Multiset.ofList (oldWraps fC tC fD tD) := by
  rw [seams_restore_of_equal_tails fC tC fD tD h]
  simp

end CorralFormalization
