import CorralFormalization.DiversityCompletion.EvenSwitchesC
import CorralFormalization.DiversityCompletion.EvenAInjective

namespace CorralFormalization.EvenSwitches

open PhysicalCorral

theorem zero_mem_A (m : ℕ) (a : Choices m) : 0 ∈ rowA m a := by
  rw [rowA_mem_iff]
  exact Or.inl rfl

theorem firstpoint_mem_A (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    2 * height m - 2 ∈ rowA m a := by
  have hj : 0 < halfHeight m := by unfold halfHeight; omega
  have hx : lowerA m a.1 0 ∈ rowA m a := by rw [rowA_mem_iff]; aesop
  simpa only [(A_fixed_seams m hm a).1] using hx

theorem largest_point_mem_A (m : ℕ) (hm : 1 ≤ m) (a : Choices m) : order m ∈ rowA m a := by
  have hj : 1 < halfHeight m := by unfold halfHeight; omega
  have hx : middleA m 1 ∈ rowA m a := by rw [rowA_mem_iff]; aesop
  have heq : middleA m 1 = order m := by unfold middleA height order; simp; omega
  simpa only [heq] using hx

theorem last_middle_mem_A (m : ℕ) (hm : 1 ≤ m) (a : Choices m) : middleA m (2 * m) ∈ rowA m a := by
  have hj0 : 1 ≤ 2 * m := by omega
  have hj : 2 * m < halfHeight m := by unfold halfHeight; omega
  rw [rowA_mem_iff]
  aesop

theorem center_mem_B (m : ℕ) (a : Choices m) : (height m) ^ 2 - 1 ∈ rowB m a := by
  rw [rowB_mem_iff]
  exact Or.inl rfl

theorem switchedWordA_starts (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    ∃ g, switchedWordA m a = (2 * height m - 2) :: g := by
  have hlen := switchedWordA_length m a
  have hget : (switchedWordA m a)[0]'(by rw [hlen]; unfold order; omega) = 2 * height m - 2 := by
    simp only [switchedWordA, List.getElem_ofFn]
    change baselineGapA m (switchEdgeNat m a 0) = 2 * height m - 2
    exact (switched_A_fixed_gaps m hm a).1
  cases hw : switchedWordA m a with
  | nil => simp [hw, order] at hlen
  | cons x xs =>
    have hx : x = 2 * height m - 2 := by simpa [hw] using hget
    exact ⟨xs, by rw [hx]⟩

theorem rowA_positive_min (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (x : ℕ) (hx : x ∈ rowA m a) (hx0 : x ≠ 0) : 2 * height m - 2 ≤ x := by
  obtain ⟨g, hg⟩ := switchedWordA_starts m hm a
  rw [rowA_eq_properPrefixes m hm a, hg] at hx
  simp only [properPrefixSites, List.mem_toFinset, List.mem_cons, List.mem_map] at hx
  rcases hx with hx | ⟨y, _, hxy⟩
  · exact False.elim (hx0 hx)
  · omega

theorem seed_small_point_not_mem_A (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    height m - 1 ∉ rowA m a := by
  intro hx
  have hmin := rowA_positive_min m hm a (height m - 1) hx (by unfold height; omega)
  unfold height at hmin
  omega

theorem rowB_positive (m : ℕ) (hm : 1 ≤ m) (a : Choices m) (x : ℕ)
    (hx : x ∈ rowB m a) : 0 < x := by
  have hh : 6 ≤ height m := by unfold height; omega
  have hM : 1 < clock m := by unfold clock height order; nlinarith
  rcases (rowB_mem_iff m a x).mp hx with hx | hx | hx | ⟨j, hj, hx⟩ | ⟨j, hj0, hj, hx⟩ | ⟨j, hj, hx⟩ | ⟨r, hr, hx⟩
  · have hs : 1 < (height m) ^ 2 := by nlinarith
    omega
  · nlinarith
  · omega
  · have hb := eta_le_one m a.1 j
    have hc : 0 < 2 * j + 2 - eta m a.1 j := by omega
    have hp := Nat.mul_pos hc (show 0 < height m - 1 by omega)
    simpa [← hx, lowerB] using hp
  · have hprod : 2 * height m ≤ 2 * height m * j := by
      simpa using Nat.mul_le_mul_left (2 * height m) hj0
    unfold middleB at hx
    omega
  · have hb := epsilon_le_one m a.2 j
    have hprod : 0 < (height m + 2 + 2 * j) * (height m - 1) :=
      Nat.mul_pos (by omega) (by omega)
    unfold upperB at hx
    omega
  · have hprod : 0 < fixedB m r := by
      unfold fixedB
      exact Nat.mul_pos (by omega) (by unfold halfHeight; omega)
    rcases hx with hx | hx <;> omega

theorem zero_not_mem_B (m : ℕ) (hm : 1 ≤ m) (a : Choices m) : 0 ∉ rowB m a := by
  intro hx
  have := rowB_positive m hm a 0 hx
  omega

theorem center_eq_lastMiddle_add_order (m : ℕ) :
    (height m) ^ 2 - 1 = middleA m (2 * m) + order m := by
  have hpos : 0 < (height m) ^ 2 := by unfold height; positivity
  have hs := Nat.sub_add_cancel (show 1 ≤ (height m) ^ 2 by omega)
  have hp : (2 * m) % 2 = 0 := by omega
  unfold middleA
  rw [hp, Nat.sub_zero]
  unfold height order at *
  nlinarith

theorem reflection_largest_point (m : ℕ) :
    ((height m) ^ 2 - 1 : ℕ) - (order m : ZMod (clock m)) =
      (middleA m (2 * m) : ZMod (clock m)) := by
  have hc := congrArg (fun n : ℕ => (n : ZMod (clock m))) (center_eq_lastMiddle_add_order m)
  rw [Nat.cast_add] at hc
  rw [hc]
  simp

def baseLetter (m : ℕ) (a : Choices m) : Finset (Finset (ZMod (clock m))) :=
  {physicalSites (clock m) (rowA m a), physicalSites (clock m) (rowB m a)}

def reflectedLetter (m : ℕ) (a : Choices m) : Finset (Finset (ZMod (clock m))) :=
  (Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily (baseLetter m a)

theorem physical_zero_mem_A (m : ℕ) (a : Choices m) :
    (0 : ZMod (clock m)) ∈ physicalSites (clock m) (rowA m a) := by
  exact Finset.mem_image.mpr ⟨0, zero_mem_A m a, by simp⟩

theorem physical_zero_not_mem_B (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (0 : ZMod (clock m)) ∉ physicalSites (clock m) (rowB m a) := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  rw [physicalSites_mem_iff _ (rowB_bounded m hm a)]
  simpa using zero_not_mem_B m hm a

theorem center_not_mem_A (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (height m) ^ 2 - 1 ∉ rowA m a := by
  intro hx
  have hh : 6 ≤ height m := by unfold height; omega
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hC : (height m) ^ 2 - 1 + 1 = (height m) ^ 2 := Nat.sub_add_cancel (by nlinarith)
  rcases (rowA_mem_iff m a _).mp hx with hx | ⟨j, hj, hx⟩ | ⟨j, hj0, hj, hx⟩ | ⟨j, hj, hx⟩ | ⟨r, hr, hx⟩
  · nlinarith
  · have hb := eta_le_one m a.1 j
    have hc : 2 * j + 1 + eta m a.1 j ≤ height m := by unfold halfHeight height at *; omega
    have hp := Nat.mul_le_mul_right (height m - 1) hc
    unfold lowerA at hx
    rw [hheight] at hp hx
    unfold height at *
    nlinarith
  · have hj' : j ≤ 2 * m := by unfold halfHeight at hj; omega
    have hp := Nat.mul_le_mul_left (2 * height m) hj'
    have hs : middleA m j ≤ 2 * height m * j := Nat.sub_le _ _
    have hmax : 2 * height m * (2 * m) < (height m) ^ 2 - 1 := by unfold height at *; nlinarith
    omega
  · have hc : height m + 2 ≤ height m + 2 + 2 * j := by omega
    have hp := Nat.mul_le_mul_right (height m - 1) hc
    unfold upperA at hx
    rw [hheight] at hp hx
    unfold height at *
    nlinarith
  · have hc : halfHeight m + 1 ≤ halfHeight m + 1 + 2 * r := by omega
    have hp := Nat.mul_le_mul_left (2 * height m) hc
    have hs : fixedA m r ≤ fixedA m r + height m - 1 := by omega
    unfold fixedA at hx hs
    rcases hx with hx | hx <;> unfold height halfHeight at * <;> nlinarith

theorem last_middle_not_mem_B (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    middleA m (2 * m) ∉ rowB m a := by
  intro hx
  have hh : 6 ≤ height m := by unfold height; omega
  have hheight : height m - 1 = 4 * m + 1 := by unfold height; omega
  have hp : (2 * m) % 2 = 0 := by omega
  have hD : middleA m (2 * m) = 2 * height m * (2 * m) := by simp [middleA, hp]
  have hC := center_eq_lastMiddle_add_order m
  have hsq : (height m) ^ 2 - 1 + 1 = (height m) ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hmaxM : middleA m (2 * m) + height m < clock m := by
    rw [hD]; unfold clock height order; nlinarith
  rcases (rowB_mem_iff m a _).mp hx with hx | hx | hx | ⟨j, hj, hx⟩ | ⟨j, hj0, hj, hx⟩ | ⟨j, hj, hx⟩ | ⟨r, hr, hx⟩
  · have hn : 0 < order m := by unfold order; omega
    omega
  · omega
  · omega
  · by_cases hjlast : j = 2 * m
    · subst j
      unfold lowerB at hx
      rw [eta_last, hheight] at hx
      have hc : 2 * (2 * m) + 2 - 1 = 4 * m + 1 := by omega
      rw [hc, hD] at hx
      unfold height at hx
      nlinarith
    · have hc : 2 * j + 2 - eta m a.1 j ≤ 4 * m := by unfold halfHeight at hj; omega
      have hp' := Nat.mul_le_mul_right (height m - 1) hc
      unfold lowerB at hx
      rw [hx, hD, hheight] at hp'
      unfold height at *
      nlinarith
  · by_cases hjlast : j = 2 * m
    · subst j
      unfold middleB at hx
      rw [hp, Nat.sub_zero, hD] at hx
      have hd : 0 < 2 * height m * (2 * m) := by unfold height; positivity
      omega
    · have hj' : j < 2 * m := by unfold halfHeight at hj; omega
      have hp' := Nat.mul_lt_mul_of_pos_left hj' (show 0 < 2 * height m by omega)
      have hs : middleB m j ≤ 2 * height m * j := Nat.sub_le _ _
      rw [hx, hD] at hs
      omega
  · have hb := epsilon_le_one m a.2 j
    have hc : height m + 2 ≤ height m + 2 + 2 * j := by omega
    have hp' := Nat.mul_le_mul_right (height m - 1) hc
    have hs : (height m + 2 + 2 * j) * (height m - 1) ≤ upperB m a.2 j := by unfold upperB; omega
    rw [hx, hD] at hs
    rw [hheight] at hp' hs
    unfold height at *
    nlinarith
  · have hc : 2 * m + 3 ≤ halfHeight m + 2 + 2 * r := by unfold halfHeight; omega
    have hp' := Nat.mul_le_mul_left (2 * height m) hc
    have hs : fixedB m r ≤ fixedB m r + height m - 1 := by omega
    unfold fixedB at hx hs
    rcases hx with hx | hx <;> rw [hD] at hx <;> unfold height at * <;> nlinarith

theorem reflection_mem_iff {M : ℕ} (C x : ZMod M) (S : Finset (ZMod M)) :
    x ∈ (Motion.reflection C).onRow S ↔ C - x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    change C - y = x at hxy
    have h : C - x = y := by rw [← hxy]; ring
    rw [h]
    exact hy
  · intro hx
    exact Finset.mem_image.mpr ⟨C - x, hx, by change C - (C - x) = x; ring⟩

theorem baseLetter_injective (m : ℕ) (hm : 1 ≤ m) : Function.Injective (baseLetter m) := by
  intro a b hab
  have hrow : physicalSites (clock m) (rowA m a) ∈ baseLetter m b := by
    rw [← hab]
    simp [baseLetter]
  simp only [baseLetter, Finset.mem_insert, Finset.mem_singleton] at hrow
  rcases hrow with hrow | hrow
  · exact rowA_physical_injective m hm hrow
  · have hzero := physical_zero_mem_A m a
    rw [hrow] at hzero
    exact False.elim (physical_zero_not_mem_B m hm b hzero)

theorem baseLetter_ne_reflected (m : ℕ) (hm : 1 ≤ m) (a b : Choices m) :
    baseLetter m a ≠ reflectedLetter m b := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  intro heq
  have hrow : physicalSites (clock m) (rowA m a) ∈ reflectedLetter m b := by
    rw [← heq]
    simp [baseLetter]
  obtain ⟨S, hS, hSR⟩ := Finset.mem_image.mp hrow
  simp only [baseLetter, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl
  · have hz : (0 : ZMod (clock m)) ∈ (Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onRow
        (physicalSites (clock m) (rowA m b)) := by rw [hSR]; exact physical_zero_mem_A m a
    rw [reflection_mem_iff, sub_zero] at hz
    have hmem := (physicalSites_mem_iff _ (rowA_bounded m hm b) _).mp hz
    have hCbound : (height m) ^ 2 - 1 < clock m :=
      rowB_bounded m hm b _ (center_mem_B m b)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hCbound] at hmem
    exact center_not_mem_A m hm b hmem
  · have hn : (order m : ZMod (clock m)) ∈ physicalSites (clock m) (rowA m a) :=
      Finset.mem_image.mpr ⟨order m, largest_point_mem_A m hm a, rfl⟩
    rw [← hSR, reflection_mem_iff, reflection_largest_point] at hn
    have hmem := (physicalSites_mem_iff _ (rowB_bounded m hm b) _).mp hn
    have hDbound := rowA_bounded m hm a _ (last_middle_mem_A m hm a)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hDbound] at hmem
    exact last_middle_not_mem_B m hm b hmem

theorem reflectedLetter_injective (m : ℕ) (hm : 1 ≤ m) : Function.Injective (reflectedLetter m) := by
  intro a b hab
  apply baseLetter_injective m hm
  have h := congrArg (Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily hab
  change (Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily
      ((Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily (baseLetter m a)) =
    (Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily
      ((Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily (baseLetter m b)) at h
  rw [Motion.reflection_onFamily_involutive _ (baseLetter m a),
    Motion.reflection_onFamily_involutive _ (baseLetter m b)] at h
  exact h

/-- The literal reflection-closed alphabet (D12), still with unlabelled rows. -/
def alphabetLetter (m : ℕ) (ab : Choices m × Bool) : Finset (Finset (ZMod (clock m))) :=
  if ab.2 then reflectedLetter m ab.1 else baseLetter m ab.1

theorem alphabetLetter_injective (m : ℕ) (hm : 1 ≤ m) : Function.Injective (alphabetLetter m) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ hab
  cases i <;> cases j
  · change baseLetter m a = baseLetter m b at hab
    exact Prod.ext (baseLetter_injective m hm hab) rfl
  · change baseLetter m a = reflectedLetter m b at hab
    exact False.elim (baseLetter_ne_reflected m hm a b hab)
  · change reflectedLetter m a = baseLetter m b at hab
    exact False.elim (baseLetter_ne_reflected m hm b a hab.symm)
  · change reflectedLetter m a = reflectedLetter m b at hab
    exact Prod.ext (reflectedLetter_injective m hm hab) rfl

def alphabet (m : ℕ) : Finset (Finset (Finset (ZMod (clock m)))) :=
  Finset.univ.image (alphabetLetter m)

theorem alphabet_card (m : ℕ) (hm : 1 ≤ m) : (alphabet m).card = 2 ^ (halfHeight m - 1) := by
  rw [alphabet, Finset.card_image_of_injective _ (alphabetLetter_injective m hm)]
  simp only [Finset.card_univ, Fintype.card_prod, choices_card m hm, Fintype.card_bool]
  rw [← pow_succ]
  congr 1
  unfold halfHeight
  omega

theorem alphabetLetter_reflection (m : ℕ) (ab : Choices m × Bool) :
    (Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily (alphabetLetter m ab) =
      alphabetLetter m (ab.1, !ab.2) := by
  rcases ab with ⟨a, i⟩
  cases i
  · rfl
  · exact Motion.reflection_onFamily_involutive _ (baseLetter m a)

theorem alphabet_reflection_closed (m : ℕ) :
    (alphabet m).image (Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily = alphabet m := by
  ext F
  constructor
  · intro hF
    obtain ⟨G, hG, hGF⟩ := Finset.mem_image.mp hF
    obtain ⟨ab, _, hab⟩ := Finset.mem_image.mp hG
    subst G
    refine Finset.mem_image.mpr ⟨(ab.1, !ab.2), Finset.mem_univ _, ?_⟩
    exact (alphabetLetter_reflection m ab).symm.trans hGF
  · intro hF
    obtain ⟨ab, _, hab⟩ := Finset.mem_image.mp hF
    refine Finset.mem_image.mpr ⟨alphabetLetter m (ab.1, !ab.2),
      Finset.mem_image.mpr ⟨(ab.1, !ab.2), Finset.mem_univ _, rfl⟩, ?_⟩
    rw [alphabetLetter_reflection]
    simpa using hab

theorem baseLetter_card (m : ℕ) (hm : 1 ≤ m) (a : Choices m) : (baseLetter m a).card = 2 := by
  have hne : physicalSites (clock m) (rowA m a) ≠ physicalSites (clock m) (rowB m a) := by
    intro h
    have hz := physical_zero_mem_A m a
    rw [h] at hz
    exact physical_zero_not_mem_B m hm a hz
  simp [baseLetter, hne]

theorem alphabetLetter_card (m : ℕ) (hm : 1 ≤ m) (ab : Choices m × Bool) :
    (alphabetLetter m ab).card = 2 := by
  rcases ab with ⟨a, i⟩
  cases i
  · exact baseLetter_card m hm a
  · change ((Motion.reflection ((height m) ^ 2 - 1 : ℕ)).onFamily (baseLetter m a)).card = 2
    rw [Motion.onFamily, Finset.card_image_of_injective _
      (Motion.reflection_onRow_involutive _).injective]
    exact baseLetter_card m hm a

end CorralFormalization.EvenSwitches
