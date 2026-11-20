import CorralFormalization.DiversityCompletion.WordBridge

namespace CorralFormalization.DiversitySymmetry

open Finset
open CorralFormalization.PhysicalCorral

theorem pair_flatMap_length {A B : Type*} (xs : List A) (f g : A → B) :
    (xs.flatMap (fun a => [f a, g a])).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, List.flatMap_cons]; omega

theorem pair_flatMap_get_even {A B : Type*} (xs : List A) (f g : A → B)
    (i : ℕ) (hi : i < xs.length) :
    (xs.flatMap (fun a => [f a, g a]))[2 * i]'(by rw [pair_flatMap_length]; omega) =
      f xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa [List.flatMap_cons, Nat.mul_succ, Nat.add_assoc] using ih i (by simpa using hi)

theorem pair_flatMap_get_odd {A B : Type*} (xs : List A) (f g : A → B)
    (i : ℕ) (hi : i < xs.length) :
    (xs.flatMap (fun a => [f a, g a]))[2 * i + 1]'(by rw [pair_flatMap_length]; omega) =
      g xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa [List.flatMap_cons, Nat.mul_succ, Nat.add_assoc] using ih i (by simpa using hi)

theorem evenConstructionLowList_last_odd (k : ℕ) (hk : 1 ≤ k) :
    (evenConstructionLowList k)[k - 1]'(by rw [evenConstructionLowList_length k hk]; omega) = 1 := by
  unfold evenConstructionLowList
  rw [List.getElem_append_left (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  omega

theorem evenConstructionLowList_first_even (k : ℕ) (hk : 2 ≤ k) :
    (evenConstructionLowList k)[k]'(by rw [evenConstructionLowList_length k (by omega)]; omega) =
      2 * k - 2 := by
  unfold evenConstructionLowList
  rw [List.getElem_append_right (by simp)]
  simp

theorem evenConstructionGapWord_get_even (k : ℕ) (hk : 1 ≤ k) (i : ℕ)
    (hi : i < (evenConstructionLowList k).length) :
    (evenConstructionGapWord k)[2 * i]'(by have h := evenConstructionLowList_length k hk; rw [evenConstructionGapWord_length k hk]; omega) =
      (evenConstructionLowList k)[i] := by
  unfold evenConstructionGapWord
  rw [List.getElem_append_left (by rw [pair_flatMap_length]; omega)]
  exact pair_flatMap_get_even (evenConstructionLowList k) id (fun a => 4 * k - a) i hi

theorem evenConstructionGapWord_get_odd (k : ℕ) (hk : 1 ≤ k) (i : ℕ)
    (hi : i < (evenConstructionLowList k).length) :
    (evenConstructionGapWord k)[2 * i + 1]'(by have h := evenConstructionLowList_length k hk; rw [evenConstructionGapWord_length k hk]; omega) =
      4 * k - (evenConstructionLowList k)[i] := by
  unfold evenConstructionGapWord
  rw [List.getElem_append_left (by rw [pair_flatMap_length]; omega)]
  exact pair_flatMap_get_odd (evenConstructionLowList k) id (fun a => 4 * k - a) i hi

/-- The concrete three entries around the maximal gap of the printed
even-height word. The position is internal for every `k≥2`. -/
theorem evenConstructionGapWord_max_neighbors (k : ℕ) (hk : 2 ≤ k) :
    (evenConstructionGapWord k)[2 * k - 2]'(by rw [evenConstructionGapWord_length k (by omega)]; omega) = 1 ∧
    (evenConstructionGapWord k)[2 * k - 1]'(by rw [evenConstructionGapWord_length k (by omega)]; omega) = 4 * k - 1 ∧
    (evenConstructionGapWord k)[2 * k]'(by rw [evenConstructionGapWord_length k (by omega)]; omega) = 2 * k - 2 := by
  have hk1 : 1 ≤ k := by omega
  have hi : k - 1 < (evenConstructionLowList k).length := by rw [evenConstructionLowList_length k hk1]; omega
  have hik : k < (evenConstructionLowList k).length := by rw [evenConstructionLowList_length k hk1]; omega
  have heven := evenConstructionGapWord_get_even k hk1 (k - 1) hi
  have hodd := evenConstructionGapWord_get_odd k hk1 (k - 1) hi
  have hnext := evenConstructionGapWord_get_even k hk1 k hik
  rw [evenConstructionLowList_last_odd k hk1] at heven hodd
  rw [evenConstructionLowList_first_even k hk] at hnext
  have hindex0 : 2 * (k - 1) = 2 * k - 2 := by omega
  have hindex1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  exact ⟨by simpa only [hindex0] using heven, by simpa only [hindex1] using hodd, hnext⟩

/-- Exactly the row R starting at zero in manuscript §§3 and 6. -/
def evenConstructionSeed (k : ℕ) : Finset (ZMod (evenConstructionClock k)) :=
  physicalSites (evenConstructionClock k) (evenConstructionRawPrefixSet k)

/-- The full physical gap inventory of the actual seed, derived from the
existing explicit even construction and representative decoding. -/
theorem evenConstructionSeed_inventory (k : ℕ) (hk : 1 ≤ k) :
    finiteCyclicGapInventory (evenConstructionClock k) ((evenConstructionSeed k).image ZMod.val) =
      Multiset.ofList (fullGapList (4 * k - 1)) := by
  let : NeZero (evenConstructionClock k) := ⟨Nat.ne_of_gt (evenConstructionClock_pos k hk)⟩
  unfold evenConstructionSeed
  rw [physicalSites_decode (evenConstructionRawPrefixSet k)
    (evenConstructionRawPrefixSet_clock_bound k · hk)]
  rw [evenConstructionRawPrefixSet_gaps k hk]
  exact Multiset.coe_eq_coe.mpr (evenConstructionGapWord_perm_full k hk)

/-- The seed's concrete maximal-gap marker is {1,h-2}, with h=2k.
No validity, marker, or motion-invariance hypothesis is an input. -/
theorem evenConstructionSeed_marker (k : ℕ) (hk : 2 ≤ k) :
    HasGapNeighborPair (evenConstructionSeed k) (4 * k - 1) {1, 2 * k - 2} := by
  have hk1 : 1 ≤ k := by omega
  let : NeZero (evenConstructionClock k) := ⟨Nat.ne_of_gt (evenConstructionClock_pos k hk1)⟩
  let n := 4 * k - 1
  let : NeZero n := ⟨by dsimp [n]; omega⟩
  let g := evenConstructionGapWord k
  have hlen : g.length = n := evenConstructionGapWord_length k hk1
  have hpos : ∀ x ∈ g, 0 < x := evenConstructionGapWord_positive k hk1
  have hsum : g.sum = evenConstructionClock k := (evenConstructionClock_eq_sum k hk1).symm
  obtain ⟨E, _, hEgap⟩ := cyclicRow_of_positive_word g hlen hpos hsum (by dsimp [n]; omega)
  let i : ZMod n := ((2 * k - 1 : ℕ) : ZMod n)
  have hiv : i.val = 2 * k - 1 := by
    dsimp [i]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by dsimp [n]; omega)]
  have hone : (1 : ZMod n).val = 1 := ZMod.val_one'' (by dsimp [n]; omega)
  have hiprev : (i - 1).val = 2 * k - 2 := by
    rw [ZMod.val_sub (by rw [hiv, hone]; omega), hiv, hone]
    omega
  have hinext : (i + 1).val = 2 * k := by
    rw [ZMod.val_add, hiv, hone, Nat.mod_eq_of_lt (by dsimp [n]; omega)]
    omega
  obtain ⟨hprev, hmax, hnext⟩ := evenConstructionGapWord_max_neighbors k hk
  have hgi : E.gap i = 4 * k - 1 := by
    rw [hEgap i]
    simpa only [g, hiv] using hmax
  have hgprev : E.gap (i - 1) = 1 := by
    rw [hEgap (i - 1)]
    simpa only [g, hiprev] using hprev
  have hgnext : E.gap (i + 1) = 2 * k - 2 := by
    rw [hEgap (i + 1)]
    simpa only [g, hinext] using hnext
  have hmarker := E.hasGapNeighborPair i
  rw [hgi, hgprev, hgnext] at hmarker
  rw [wordSites_eq_physicalPrefixes g hlen] at hmarker
  exact hmarker

theorem evenConstructionSeed_marker_iff (k : ℕ) (hk : 2 ≤ k) (pair : Finset ℕ) :
    HasGapNeighborPair (evenConstructionSeed k) (4 * k - 1) pair ↔ pair = {1, 2 * k - 2} := by
  have hk1 : 1 ≤ k := by omega
  let : NeZero (evenConstructionClock k) := ⟨Nat.ne_of_gt (evenConstructionClock_pos k hk1)⟩
  have huniq := unique_max_gap_neighbor_pair (4 * k - 1) (evenConstructionSeed k) (by omega)
    (evenConstructionSeed_inventory k hk1)
  constructor
  · intro hp
    exact huniq.unique hp (evenConstructionSeed_marker k hk)
  · rintro rfl
    exact evenConstructionSeed_marker k hk

theorem evenConstructionSeed_rigid (k : ℕ) (hk : 2 ≤ k) : RigidRow (evenConstructionSeed k) := by
  have hk1 : 1 ≤ k := by omega
  let : NeZero (evenConstructionClock k) := ⟨Nat.ne_of_gt (evenConstructionClock_pos k hk1)⟩
  exact rigidRow_of_finiteCyclicGapInventory (4 * k - 1) (evenConstructionSeed k) (by omega)
    (evenConstructionSeed_inventory k hk1)

/-- The literal parameterization of Theorem 3: h=4m+2, n=8m+3. -/
theorem evenSwitchFamily_seed_marker (m : ℕ) (hm : 1 ≤ m) :
    HasGapNeighborPair (evenConstructionSeed (2 * m + 1)) (8 * m + 3) {1, 4 * m} := by
  have hn : 4 * (2 * m + 1) - 1 = 8 * m + 3 := by
    have h : 4 * (2 * m + 1) = 8 * m + 4 := by ring
    omega
  have hp : 2 * (2 * m + 1) - 2 = 4 * m := by
    have h : 2 * (2 * m + 1) = 4 * m + 2 := by ring
    omega
  simpa only [hn, hp] using evenConstructionSeed_marker (2 * m + 1) (by omega)

theorem evenSwitchFamily_seed_rigid (m : ℕ) (hm : 1 ≤ m) :
    RigidRow (evenConstructionSeed (2 * m + 1)) :=
  evenConstructionSeed_rigid (2 * m + 1) (by omega)

end CorralFormalization.DiversitySymmetry
