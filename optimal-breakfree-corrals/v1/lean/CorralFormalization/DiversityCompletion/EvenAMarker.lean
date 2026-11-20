import CorralFormalization.DiversityCompletion.EvenSwitches
import CorralFormalization.DiversityCompletion.WordBridge

/-! The actual §6 switched A row has the displayed gap-n neighbour
marker for every allowed bit choice, with its actual physical wrap. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral DiversitySymmetry

theorem rowA_physical_inventory (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    finiteCyclicGapInventory (clock m)
      ((physicalSites (clock m) (rowA m a)).image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  rw [physicalSites_decode (rowA m a) (rowA_bounded m hm a)]
  exact rowA_gap_inventory m hm a

theorem rowA_physical_rigid (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    RigidRow (physicalSites (clock m) (rowA m a)) := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  exact rigidRow_of_finiteCyclicGapInventory (order m) _
    (by unfold order; omega) (rowA_physical_inventory m hm a)

theorem rowA_physical_marker (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    HasGapNeighborPair (physicalSites (clock m) (rowA m a)) (order m)
      {height m, height m + 1} := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  let : NeZero (order m) := ⟨by unfold order; omega⟩
  let g := switchedWordA m a
  have hglen : g.length = order m := switchedWordA_length m a
  have hgpos : ∀ x ∈ g, 0 < x := by
    intro x hx
    exact ((fullGapList_mem _ _).mp ((switchedWordA_perm m hm a).mem_iff.mp hx)).1
  have hgsum : g.sum = clock m := switchedWordA_sum m hm a
  obtain ⟨E, _, hgap⟩ := cyclicRow_of_positive_word (M := clock m) g hglen hgpos hgsum
    (by unfold order; omega)
  have hsite : wordSites (clock m) (order m) g = physicalSites (clock m) (rowA m a) := by
    rw [wordSites_eq_physicalPrefixes g hglen, rowA_eq_properPrefixes m hm a]
  have hentry (k : ℕ) (hk : k < order m) :
      E.gap (k : ZMod (order m)) = baselineGapA m (switchEdgeNat m a k) := by
    rw [hgap]
    simp [g, ZMod.val_natCast_of_lt hk, switchedWordA, switchEdge]
  let i : ZMod (order m) := ((4*m+1 : ℕ) : ZMod (order m))
  have him : i - 1 = ((4*m : ℕ) : ZMod (order m)) := by
    dsimp [i]
    push_cast
    ring
  have hip : i + 1 = ((4*m+2 : ℕ) : ZMod (order m)) := by
    dsimp [i]
    push_cast
    ring
  obtain ⟨_, _, hprev, hmid, hnext, _, _⟩ := switched_A_fixed_gaps m hm a
  have hgi : E.gap i = order m := by
    dsimp [i]
    rw [hentry _ (by unfold order; omega), hmid]
  have hgm : E.gap (i - 1) = height m := by
    rw [him, hentry _ (by unfold order; omega), hprev]
  have hgp : E.gap (i + 1) = height m + 1 := by
    rw [hip, hentry _ (by unfold order; omega), hnext]
  have hh := E.hasGapNeighborPair i
  rw [hgi, hgm, hgp] at hh
  rw [hsite] at hh
  exact hh

/-- The marker is unique because all physical gaps are distinct. -/
theorem rowA_physical_marker_iff (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (P : Finset ℕ) :
    HasGapNeighborPair (physicalSites (clock m) (rowA m a)) (order m) P ↔
      P = {height m, height m + 1} := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  obtain ⟨S, hS, huniq⟩ := unique_max_gap_neighbor_pair (order m)
    (physicalSites (clock m) (rowA m a)) (by unfold order; omega)
      (rowA_physical_inventory m hm a)
  constructor
  · intro hP
    exact (huniq P hP).trans (huniq _ (rowA_physical_marker m hm a)).symm
  · rintro rfl
    exact rowA_physical_marker m hm a

end CorralFormalization.EvenSwitches
