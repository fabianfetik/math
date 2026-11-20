import CorralFormalization.RowJoin
import CorralFormalization.OrderedGaps

namespace CorralFormalization

/-- The joint physical-and-gap return used by the odd construction. The
same owner permutation must satisfy the endpoint match for the actual pair of
component rows; separately obtained witnesses are not sufficient. -/
theorem joined_factors_contract {h U V : ℕ} (C D : Fin h → Finset ℕ)
    (π : Equiv.Perm (Fin h))
    (hneC : ∀ i, (C i).Nonempty) (hneD : ∀ j, (D j).Nonempty)
    (hCbound : ∀ i x, x ∈ C i → x < U)
    (hDbound : ∀ j y, y ∈ D j → y < V)
    (hC : ∀ x, x < U → ∃! i, x ∈ C i)
    (hD : ∀ y, y < V → ∃! j, y ∈ D j)
    (hmatch : ∀ i, (C i).min' (hneC i) = (D (π i)).min' (hneD (π i)) ∨
      U - (C i).max' (hneC i) = V - (D (π i)).max' (hneD (π i))) :
    (∀ x, x < U + V ↔ ∃! i, x ∈ joinedRow U C D π i) ∧
    ∀ i, finiteCyclicGapInventory (U + V) (joinedRow U C D π i) =
      finiteCyclicGapInventory U (C i) + finiteCyclicGapInventory V (D (π i)) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact joined_rows_partition_iff C D π hCbound hDbound hC hD x
  · intro i
    exact finite_set_cyclic_gap_join U V (C i) (D (π i)) (hneC i) (hneD (π i))
      (hCbound i) (hDbound (π i)) (hmatch i)

end CorralFormalization
