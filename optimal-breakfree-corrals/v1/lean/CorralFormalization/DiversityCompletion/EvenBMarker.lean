import CorralFormalization.DiversityCompletion.EvenSwitchesC
import CorralFormalization.DiversityCompletion.WordBridge

/-! The actual D7 B-row has the second displayed gap-n neighbour marker,
including m=1, on the physical clock. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral DiversitySymmetry

theorem rowB_physical_inventory (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    finiteCyclicGapInventory (clock m)
      ((physicalSites (clock m) (rowB m a)).image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  rw [physicalSites_decode (rowB m a) (rowB_bounded m hm a)]
  exact rowB_gap_inventory m hm a

theorem rowB_physical_rigid (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    RigidRow (physicalSites (clock m) (rowB m a)) := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  exact rigidRow_of_finiteCyclicGapInventory (order m) _
    (by unfold order; omega) (rowB_physical_inventory m hm a)

theorem rowB_physical_marker (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    HasGapNeighborPair (physicalSites (clock m) (rowB m a)) (order m)
      {height m - 2, height m + 3} := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  let : NeZero (order m) := ⟨by unfold order; omega⟩
  let g := switchedWordB m a
  have hglen : g.length = order m := switchedWordB_length m a
  have hgpos : ∀ x ∈ g, 0 < x := by
    intro x hx
    exact ((fullGapList_mem _ _).mp ((switchedWordB_perm m hm a).mem_iff.mp hx)).1
  have hgsum : g.sum = clock m := switchedWordB_sum m hm a
  obtain ⟨E, _, hgap⟩ := cyclicRow_of_positive_word (M := clock m) g hglen hgpos hgsum
    (by unfold order; omega)
  have hentry (k : ℕ) (hk : k < order m) :
      E.gap (k : ZMod (order m)) = baselineGapB m (switchEdgeBNat m a k) := by
    rw [hgap]
    simp [g, ZMod.val_natCast_of_lt hk, switchedWordB, switchEdgeB]
  have hs1 : switchEdgeBNat m a 1 = 1 := by simp [switchEdgeBNat]
  have hs2 : switchEdgeBNat m a 2 = 2 := by
    simp [switchEdgeBNat, epsilon_one m hm a.2]
  have hs3 : switchEdgeBNat m a 3 = 3 := by
    simp [switchEdgeBNat, epsilon_one m hm a.2]
    omega
  have hb1 : baselineGapB m 1 = height m - 2 := by simp [baselineGapB, height]
  have hb2 : baselineGapB m 2 = order m := by simp [baselineGapB, order]
  have hb3 : baselineGapB m 3 = height m + 3 := by
    by_cases hm1 : m = 1
    · subst m
      norm_num [baselineGapB, height]
    · have hb : 3 < 4*m-1 := by omega
      simp [baselineGapB, height, hb]
  let i : ZMod (order m) := (2 : ℕ)
  have him : i - 1 = ((1 : ℕ) : ZMod (order m)) := by dsimp [i]; norm_num
  have hip : i + 1 = ((3 : ℕ) : ZMod (order m)) := by dsimp [i]; norm_num
  have hgi : E.gap i = order m := by
    have hv := hentry 2 (by unfold order; omega)
    rw [hs2, hb2] at hv
    simpa [i] using hv
  have hgm : E.gap (i - 1) = height m - 2 := by
    rw [him, hentry _ (by unfold order; omega), hs1, hb1]
  have hgp : E.gap (i + 1) = height m + 3 := by
    rw [hip, hentry _ (by unfold order; omega), hs3, hb3]
  have hh := E.hasGapNeighborPair i
  rw [hgi, hgm, hgp] at hh
  let c : ZMod (clock m) := (((height m)^2-1 : ℕ) : ZMod (clock m))
  have hmoved := hasGapNeighborPair_rotation_forward _ c _ _ hh
  have hsite : (Motion.rotation c).onRow (wordSites (clock m) (order m) g) =
      physicalSites (clock m) (rowB m a) := by
    rw [wordSites_eq_physicalPrefixes g hglen, ← rowB_eq_shifted_prefixes m hm a]
    simp only [Motion.onRow, physicalSites, Finset.image_image, Function.comp_def, Motion.act,
      ZMod.natCast_mod, Nat.cast_add]
    congr 1
    funext x
    dsimp [c]
    ring
  rw [hsite] at hmoved
  exact hmoved

theorem rowB_physical_marker_iff (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (P : Finset ℕ) :
    HasGapNeighborPair (physicalSites (clock m) (rowB m a)) (order m) P ↔
      P = {height m - 2, height m + 3} := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  obtain ⟨S, _, huniq⟩ := unique_max_gap_neighbor_pair (order m)
    (physicalSites (clock m) (rowB m a)) (by unfold order; omega)
      (rowB_physical_inventory m hm a)
  constructor
  · intro hP
    exact (huniq P hP).trans (huniq _ (rowB_physical_marker m hm a)).symm
  · rintro rfl
    exact rowB_physical_marker m hm a

end CorralFormalization.EvenSwitches
