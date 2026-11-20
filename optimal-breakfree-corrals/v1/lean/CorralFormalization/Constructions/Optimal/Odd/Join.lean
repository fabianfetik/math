import CorralFormalization.Constructions.Optimal.Odd.Endpoints
import CorralFormalization.Constructions.Optimal.Odd.PhysicalFactor
import CorralFormalization.Assembly

namespace CorralFormalization

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. -/

open OddSeamAssignment OddCorePhysicalRows

/-- Conjugate the paper's actual owner permutation from `ZMod h` to the
canonical representatives `Fin h` used by the physical join. -/
noncomputable def oddConstructionOwnerFin (A : ℕ) : Equiv.Perm (Fin (h A)) := by
  letI : NeZero (h A) := ⟨by dsimp [h]; omega⟩
  exact (ZMod.finEquiv (h A)).toEquiv.trans
    ((explicitOwner A).trans (ZMod.finEquiv (h A)).toEquiv.symm)

/-- The conjugated permutation selects the same actual index used in (11). -/
theorem oddConstructionOwnerFin_apply (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    oddConstructionOwnerFin A s = explicitOwnerIndex A hA s := by
  letI : NeZero (h A) := ⟨by dsimp [h]; omega⟩
  have hcast : (s.val : ZMod (h A)) = (ZMod.finEquiv (h A)) s := by
    apply ZMod.val_injective (h A)
    rw [ZMod.val_natCast_of_lt s.isLt]
    rfl
  apply Fin.ext
  change ((ZMod.finEquiv (h A)).toEquiv.symm
      (explicitOwner A ((ZMod.finEquiv (h A)) s))).val =
        (explicitOwner A (s.val : ZMod (h A))).val
  rw [hcast]
  rfl

theorem oddConstructionPhysicalSites_nonempty (A : ℕ) (t : Fin (h A)) :
    (physicalRowSites A t).Nonempty := by
  unfold physicalRowSites
  simp

theorem oddConstructionPhysicalSites_min (A : ℕ) (t : Fin (h A)) :
    (physicalRowSites A t).min' (oddConstructionPhysicalSites_nonempty A t) = dHead A t := by
  simp [physicalRowSites, dHead, Finset.min'_insert]

theorem oddConstructionPhysicalSites_max (A : ℕ) (t : Fin (h A)) :
    (physicalRowSites A t).max' (oddConstructionPhysicalSites_nonempty A t) =
      max (dFirst A t.val) (dSecond A t.val) := by
  simp [physicalRowSites, Finset.max'_insert]

theorem oddConstructionCoreSites_bound (A : ℕ) (s : Fin (h A))
    (x : ℕ) (hx : x ∈ oddConstructionCoreSites A s) :
    x < (2 * A + 3) * (4 * A + 3) := by
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
  exact Nat.mod_lt _ (by positivity)

theorem oddConstructionPhysicalSites_bound (A : ℕ) (hA : 2 ≤ A) (t : Fin (h A))
    (x : ℕ) (hx : x ∈ physicalRowSites A t) : x < 2 * h A := by
  have hb := physicalRowSites_bounds_distinct A hA t
  simp only [physicalRowSites, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> omega

/-- The two actual component rows selected by the paper's owner permutation
meet the head-or-tail premise of the physical join. -/
theorem oddConstructionActualEndpointMatch (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (h A)) :
    (oddConstructionCoreSites A s).min' (oddConstructionCoreSites_nonempty A hA s) =
        (physicalRowSites A (oddConstructionOwnerFin A s)).min'
          (oddConstructionPhysicalSites_nonempty A (oddConstructionOwnerFin A s)) ∨
      (2 * A + 3) * (4 * A + 3) -
          (oddConstructionCoreSites A s).max' (oddConstructionCoreSites_nonempty A hA s) =
        2 * h A - (physicalRowSites A (oddConstructionOwnerFin A s)).max'
          (oddConstructionPhysicalSites_nonempty A (oddConstructionOwnerFin A s)) := by
  have hmatch := oddConstructionConcreteEndpointMatch A hA s
  by_cases htail : explicitUsesTail A s.val
  · right
    simp only [if_pos htail] at hmatch
    rw [oddConstructionOwnerFin_apply A hA s, oddConstructionPhysicalSites_max]
    simpa [dTail] using hmatch
  · left
    simp only [if_neg htail] at hmatch
    rw [oddConstructionOwnerFin_apply A hA s, oddConstructionPhysicalSites_min]
    exact hmatch

/-- The completed physical row (12), using actual first and second factors
and the paper's owner permutation. -/
noncomputable def oddConstructionJoinedSites (A : ℕ) (s : Fin (h A)) : Finset ℕ :=
  joinedRow ((2 * A + 3) * (4 * A + 3))
    (oddConstructionCoreSites A) (physicalRowSites A) (oddConstructionOwnerFin A) s

/-- The literal rows (12) partition the physical clock, and each row's
cyclic-gap multiset is the sum of its actual core gaps and the two missing
gaps. The identification of the core's gaps with the word is supplied
by the subsequent CoreGaps module. -/
theorem oddConstructionJoinedSites_partition_and_gaps (A : ℕ) (hA : 2 ≤ A) :
    (∀ x, x < (2 * A + 3) * (4 * A + 3) + 2 * h A ↔
      ∃! s : Fin (h A), x ∈ oddConstructionJoinedSites A s) ∧
    ∀ s : Fin (h A),
      finiteCyclicGapInventory ((2 * A + 3) * (4 * A + 3) + 2 * h A)
          (oddConstructionJoinedSites A s) =
        finiteCyclicGapInventory ((2 * A + 3) * (4 * A + 3)) (oddConstructionCoreSites A s) +
          Multiset.ofList [3, 2 * h A - 3] := by
  have hC : ∀ x, x < (2 * A + 3) * (4 * A + 3) →
      ∃! s : Fin (h A), x ∈ oddConstructionCoreSites A s := by
    intro x hx
    exact actualOddCoreRows_partition A hA x hx
  have hD : ∀ y, y < 2 * h A →
      ∃! t : Fin (h A), y ∈ physicalRowSites A t := by
    intro y hy
    exact physicalRowSites_partition_nat A hA y hy
  have hjoined := joined_factors_contract (oddConstructionCoreSites A) (physicalRowSites A)
    (oddConstructionOwnerFin A) (oddConstructionCoreSites_nonempty A hA)
    (oddConstructionPhysicalSites_nonempty A) (oddConstructionCoreSites_bound A)
    (oddConstructionPhysicalSites_bound A hA) hC hD (oddConstructionActualEndpointMatch A hA)
  constructor
  · intro x
    exact hjoined.1 x
  · intro s
    calc
      _ = finiteCyclicGapInventory ((2 * A + 3) * (4 * A + 3)) (oddConstructionCoreSites A s) +
          finiteCyclicGapInventory (2 * h A) (physicalRowSites A (oddConstructionOwnerFin A s)) :=
        hjoined.2 s
      _ = _ := congrArg
        (fun m => finiteCyclicGapInventory ((2 * A + 3) * (4 * A + 3))
          (oddConstructionCoreSites A s) + m)
        (physicalRow_finiteCyclicGapInventory A hA (oddConstructionOwnerFin A s))

end CorralFormalization
