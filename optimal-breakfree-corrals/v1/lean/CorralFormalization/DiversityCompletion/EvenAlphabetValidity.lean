import CorralFormalization.DiversityCompletion.EvenAlphabet

namespace CorralFormalization.EvenSwitches

open PhysicalCorral

theorem physicalSites_rotate (W T : ℕ) (S : Finset ℕ) :
    physicalSites W (S.image (fun p => (p + T) % W)) =
      (Motion.rotation (T : ℕ)).onRow (physicalSites W S) := by
  unfold physicalSites Motion.onRow
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro p hp
  change (((p + T) % W : ℕ) : ZMod W) = (T : ZMod W) + p
  rw [ZMod.natCast_mod, Nat.cast_add]
  exact add_comm _ _

theorem physical_rotation_decode {W : ℕ} [NeZero W] (S : Finset ℕ) (t : ZMod W) :
    ((Motion.rotation t).onRow (physicalSites W S)).image ZMod.val =
      S.image (fun p => (p + t.val) % W) := by
  unfold physicalSites Motion.onRow
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro p hp
  change (t + (p : ZMod W)).val = (p + t.val) % W
  rw [ZMod.val_add, ZMod.val_natCast]
  simpa only [Nat.add_comm] using Nat.add_mod_mod t.val p W

theorem shifted_word_inventory (W n : ℕ) [NeZero W] (g : List ℕ)
    (hW : 0 < W) (hsum : g.sum = W) (hperm : g.Perm (fullGapList n)) (t : ZMod W) :
    finiteCyclicGapInventory W
      (((Motion.rotation t).onRow (physicalSites W (properPrefixSites g).toFinset)).image ZMod.val) =
      Multiset.ofList (fullGapList n) := by
  have hpos : ∀ x ∈ g, 0 < x := by
    intro x hx
    exact ((fullGapList_mem _ _).mp (hperm.mem_iff.mp hx)).1
  have hbound : ∀ p ∈ (properPrefixSites g).toFinset, p < W := by
    intro p hp
    simpa [hsum] using properPrefixSites_lt_sum g hpos p (List.mem_toFinset.mp hp)
  rw [physical_rotation_decode, finite_set_cyclic_gap_rotate _ _ _ hW hbound, ← hsum]
  cases g with
  | nil => simp at hsum; omega
  | cons x xs =>
    rw [properPrefixSites_finite_gaps x xs hpos]
    exact Multiset.coe_eq_coe.mpr hperm

theorem reflected_prefix_eq_reverse (W : ℕ) (g : List ℕ)
    (hW : 0 < W) (hsum : g.sum = W) (hpos : ∀ x ∈ g, 0 < x) :
    (Motion.reflection 0).onRow (physicalSites W (properPrefixSites g).toFinset) =
      physicalSites W (properPrefixSites g.reverse).toFinset := by
  have hgsum : 0 < g.sum := by rw [hsum]; exact hW
  rw [properPrefixSites_reverse_reflect g hpos hgsum, hsum]
  unfold physicalSites Motion.onRow
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro p hp
  have hb : p < W := by simpa [hsum] using properPrefixSites_lt_sum g hpos p (List.mem_toFinset.mp hp)
  change (0 : ZMod W) - p = (((W - p) % W : ℕ) : ZMod W)
  rw [ZMod.natCast_mod, Nat.cast_sub (Nat.le_of_lt hb)]
  simp

theorem reflected_A_gap_inventory (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    finiteCyclicGapInventory (clock m)
      (((Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onRow
        (physicalSites (clock m) (rowA m a))).image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  have hW : 0 < clock m := by unfold clock height order; positivity
  let : NeZero (clock m) := ⟨Nat.ne_of_gt hW⟩
  have hp : ∀ x ∈ switchedWordA m a, 0 < x := by
    intro x hx
    exact ((fullGapList_mem _ _).mp ((switchedWordA_perm m hm a).mem_iff.mp hx)).1
  have hcomp : (Motion.reflection ((height m) ^ 2 - 1 : ℕ) : Motion (clock m)) =
      (Motion.rotation ((height m) ^ 2 - 1 : ℕ)).compose (Motion.reflection 0) := by
    simp [Motion.compose]
  rw [rowA_eq_properPrefixes m hm a, hcomp, Motion.onRow_compose,
    reflected_prefix_eq_reverse _ _ hW (switchedWordA_sum m hm a) hp]
  exact shifted_word_inventory _ _ _ hW (by simpa using switchedWordA_sum m hm a)
    ((List.reverse_perm _).trans (switchedWordA_perm m hm a)) _

theorem reflected_B_gap_inventory (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    finiteCyclicGapInventory (clock m)
      (((Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onRow
        (physicalSites (clock m) (rowB m a))).image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  have hW : 0 < clock m := by unfold clock height order; positivity
  let : NeZero (clock m) := ⟨Nat.ne_of_gt hW⟩
  have hp : ∀ x ∈ switchedWordB m a, 0 < x := by
    intro x hx
    exact ((fullGapList_mem _ _).mp ((switchedWordB_perm m hm a).mem_iff.mp hx)).1
  rw [← rowB_eq_shifted_prefixes m hm a, physicalSites_rotate, ← Motion.onRow_compose]
  simp only [Motion.compose, sub_self]
  rw [reflected_prefix_eq_reverse _ _ hW (switchedWordB_sum m hm a) hp]
  simpa only [Motion.identity_onRow] using shifted_word_inventory (clock m) (order m)
    (switchedWordB m a).reverse hW (by simpa using switchedWordB_sum m hm a)
    ((List.reverse_perm _).trans (switchedWordB_perm m hm a)) 0

/-- Every row of every actual new letter (including both reflected rows)
has the complete physical cyclic gap palette, with no validity premise. -/
theorem alphabetLetter_gap_inventory (m : ℕ) (hm : 1 ≤ m) (ab : Choices m × Bool)
    (S : Finset (ZMod (clock m))) (hS : S ∈ alphabetLetter m ab) :
    finiteCyclicGapInventory (clock m) (S.image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  rcases ab with ⟨a, i⟩
  cases i
  · change S ∈ baseLetter m a at hS
    simp only [baseLetter, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · rw [physicalSites_decode _ (rowA_bounded m hm a)]
      exact rowA_gap_inventory m hm a
    · rw [physicalSites_decode _ (rowB_bounded m hm a)]
      exact rowB_gap_inventory m hm a
  · change S ∈ reflectedLetter m a at hS
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hS
    rw [← hTS]
    simp only [baseLetter, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact reflected_A_gap_inventory m hm a
    · exact reflected_B_gap_inventory m hm a

theorem alphabetLetter_rows_nonempty (m : ℕ) (hm : 1 ≤ m) (ab : Choices m × Bool)
    (S : Finset (ZMod (clock m))) (hS : S ∈ alphabetLetter m ab) : S.Nonempty := by
  have hc := congrArg Multiset.card (alphabetLetter_gap_inventory m hm ab S hS)
  rw [PhysicalCorral.finiteCyclicGapInventory_card] at hc
  simp only [Multiset.coe_card, List.length_map, List.length_range, fullGapList] at hc
  have hn : (S.image ZMod.val).Nonempty := Finset.card_pos.mp (by rw [hc]; unfold order; omega)
  obtain ⟨x, hx⟩ := hn
  obtain ⟨y, hy, _⟩ := Finset.mem_image.mp hx
  exact ⟨y, hy⟩

theorem physical_rotation_inventory {W : ℕ} [NeZero W]
    (S : Finset (ZMod W)) (t : ZMod W) :
    finiteCyclicGapInventory W (((Motion.rotation t).onRow S).image ZMod.val) =
      finiteCyclicGapInventory W (S.image ZMod.val) := by
  have hW : 0 < W := Nat.pos_of_ne_zero (NeZero.ne W)
  have hb : ∀ p ∈ S.image ZMod.val, p < W := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact ZMod.val_lt _
  calc
    _ = finiteCyclicGapInventory W
        (((Motion.rotation t).onRow (physicalSites W (S.image ZMod.val))).image ZMod.val) := by
      rw [physicalSites_encode]
    _ = finiteCyclicGapInventory W ((S.image ZMod.val).image (fun p => (p + t.val) % W)) := by
      rw [physical_rotation_decode]
    _ = _ := finite_set_cyclic_gap_rotate W t.val (S.image ZMod.val) hW hb

/-- The actual period-p translation of a physical unlabelled letter. -/
def translatedLetter (m j : ℕ) (ab : Choices m × Bool) : Finset (Finset (ZMod (clock m))) :=
  (Motion.rotation (2 * order m * j : ℕ)).onFamily (alphabetLetter m ab)

theorem translatedLetter_injective (m : ℕ) (hm : 1 ≤ m) (j : ℕ) :
    Function.Injective (translatedLetter m j) := by
  intro a b hab
  apply alphabetLetter_injective m hm
  apply Finset.image_injective
    (Finset.image_injective (Motion.act_injective (.rotation (2 * order m * j : ℕ))))
  exact hab

theorem translatedLetter_card (m : ℕ) (hm : 1 ≤ m) (j : ℕ) (ab : Choices m × Bool) :
    (translatedLetter m j ab).card = 2 := by
  have hi : Function.Injective (fun S : Finset (ZMod (clock m)) =>
      (Motion.rotation (2 * order m * j : ℕ)).onRow S) := by
    intro S T hST
    exact Finset.image_injective (Motion.act_injective _) hST
  exact (Finset.card_image_of_injective _ hi).trans (alphabetLetter_card m hm ab)

theorem translatedLetter_gap_inventory (m : ℕ) (hm : 1 ≤ m) (j : ℕ) (ab : Choices m × Bool)
    (S : Finset (ZMod (clock m))) (hS : S ∈ translatedLetter m j ab) :
    finiteCyclicGapInventory (clock m) (S.image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  obtain ⟨R, hR, hRS⟩ := Finset.mem_image.mp hS
  rw [← hRS, physical_rotation_inventory]
  exact alphabetLetter_gap_inventory m hm ab R hR

theorem translatedLetter_rows_nonempty (m : ℕ) (hm : 1 ≤ m) (j : ℕ) (ab : Choices m × Bool)
    (S : Finset (ZMod (clock m))) (hS : S ∈ translatedLetter m j ab) : S.Nonempty := by
  obtain ⟨R, hR, hRS⟩ := Finset.mem_image.mp hS
  rw [← hRS]
  exact (alphabetLetter_rows_nonempty m hm ab R hR).image _

end CorralFormalization.EvenSwitches
