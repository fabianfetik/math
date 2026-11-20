import CorralFormalization.Constructions.Optimal.Odd.OneSwap
import CorralFormalization.CorralRows

/-!
# Height-seven certificate check

This module contains no certificate literals. The replay helper parses the input
JSON, preserving all array orders, and emits a separate Lean module containing
one value of `Certificate`. That module uses kernel-checked `decide` proofs
for the finite checks. The exact sorted-row statement follows from decided
strict order and site equality via the generic theorem `rowsOK_of_checks`.

The fixed index type `Fin 7` makes every row index explicit. `ShapeOK` checks
that `getD` never uses its default in a valid certificate. The arrivals are the
thirteen positive-prefix arrivals: the initial shift is
not emitted as an extra fourteenth entry, and the final full-winding arrival is
included. Integer remainder handles the stored signed integer shifts.
-/

namespace HeightSevenCertificate

structure Certificate where
  height : Nat
  order : Nat
  width : Nat
  rows : List (List Nat)
  permutations : List (List Nat)
  shifts : List Int
  deriving Repr, DecidableEq

/-- The target instance is height 7, order 13, width 91. -/
abbrev HeaderOK (c : Certificate) : Prop :=
  c.height = 7 ∧ c.order = 13 ∧ c.width = 91

/-- All three outer arrays and every row/gap array have the declared shape. -/
abbrev ShapeOK (c : Certificate) : Prop :=
  c.rows.length = c.height ∧
  c.permutations.length = c.height ∧
  c.shifts.length = c.height ∧
  (∀ row ∈ c.rows, row.length = c.order) ∧
  (∀ gaps ∈ c.permutations, gaps.length = c.order)

/-- The literal stored row at index `s`, without sorting or normalization. -/
def storedRow (c : Certificate) (s : Fin 7) : List Nat :=
  c.rows.getD s.val []

/-- The literal stored gap word at index `s`, preserving its order. -/
def storedGaps (c : Certificate) (s : Fin 7) : List Nat :=
  c.permutations.getD s.val []

/-- The literal stored signed integer starting site. -/
def storedShift (c : Certificate) (s : Fin 7) : Int :=
  c.shifts.getD s.val 0

/-- Equality to the *increasing list* of the supplied construction, not just
    equality after discarding duplicate entries. -/
abbrev RowsOK (c : Certificate) : Prop :=
  ∀ s : Fin 7,
    storedRow c s = (CorralFormalization.OneSwapOdd.R 2 s).sort (· ≤ ·)

/-- Kernel-reduction friendly route to the exact sorted-list statement.
    The supplied `R` reduces to a literal finite set, whereas `Finset.sort`
    uses well-founded merge sort. Proving order and set equality separately
    avoids executing that sort; this theorem proves the full list equality. -/
theorem rowsOK_of_checks {c : Certificate}
    (hincreasing : ∀ s : Fin 7, (storedRow c s).Pairwise (· < ·))
    (hsites : ∀ s : Fin 7,
      (storedRow c s).toFinset = CorralFormalization.OneSwapOdd.R 2 s) :
    RowsOK c := by
  intro s
  apply (hincreasing s).sortedLT.eq_of_mem_iff (Finset.sortedLT_sort _)
  intro x
  calc
    x ∈ storedRow c s ↔ x ∈ (storedRow c s).toFinset := List.mem_toFinset.symm
    _ ↔ x ∈ CorralFormalization.OneSwapOdd.R 2 s := by rw [hsites s]
    _ ↔ x ∈ (CorralFormalization.OneSwapOdd.R 2 s).sort (· ≤ ·) :=
      (Finset.mem_sort (· ≤ ·)).symm

/-- Each stored gap word contains every one-based gap exactly once. -/
abbrev PermutationsOK (c : Certificate) : Prop :=
  ∀ s : Fin 7,
    (storedGaps c s).Perm (CorralFormalization.fullGapList c.order)

/-- Arrivals after one through `order` gaps, in their stored traversal order.
    With `HeaderOK`, each remainder is modulo the positive integer 91. -/
def arrivals (c : Certificate) (s : Fin 7) : List Nat :=
  (List.range c.order).map (fun j =>
    ((storedShift c s + ((storedGaps c s).take (j + 1)).sum) %
      (c.width : Int)).toNat)

/-- List permutation compares multiplicities as well as occupied sites. -/
abbrev ArrivalsOK (c : Certificate) : Prop :=
  ∀ s : Fin 7, (arrivals c s).Perm (storedRow c s)

/-- The complete requested certificate statement. -/
abbrev Valid (c : Certificate) : Prop :=
  HeaderOK c ∧ ShapeOK c ∧ RowsOK c ∧ PermutationsOK c ∧ ArrivalsOK c

end HeightSevenCertificate
