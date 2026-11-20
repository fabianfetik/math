import CorralFormalization.DiversityCompletion.EvenAlphabet

/-! Literal statement translation for the switch bits in (D3). It proves that the compressed independent bits cover
every pair of literal binary strings satisfying (D3), on the stated indices. -/

namespace CorralFormalization.Results.ConstructionCorrespondence.SwitchBits

open EvenSwitches

private theorem bit_toNat (x : ℕ) (hx : x ≤ 1) :
    (decide (x = 1)).toNat = x := by
  by_cases h : x = 1
  · simp [h]
  · have h0 : x = 0 := by omega
    simp [h0]

theorem eta_encoding_surjective (m : ℕ) (v : ℕ → ℕ)
    (hbin : ∀ j, j ≤ 2 * m → v j ≤ 1)
    (hsym : ∀ j, j ≤ 2 * m → v (2 * m - j) = v j)
    (hzero : v 0 = 1) (hlast : v (2 * m) = 1) :
    ∃ a : Fin m → Bool, ∀ j, j ≤ 2 * m → eta m a j = v j := by
  let a : Fin m → Bool := fun i => decide (v (i.val + 1) = 1)
  refine ⟨a, ?_⟩
  intro j hj
  by_cases hin : 0 < j ∧ j < 2 * m
  · have hminpos : 0 < min j (2 * m - j) := by omega
    have hminbound : min j (2 * m - j) ≤ 2 * m := by omega
    have hfold : v (min j (2 * m - j)) = v j := by
      rcases le_total j (2 * m - j) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, hsym j hj]
    rw [eta, dif_pos hin]
    change (decide (v (min j (2 * m - j) - 1 + 1) = 1)).toNat = v j
    rw [Nat.sub_add_cancel (by omega), bit_toNat _ (hbin _ hminbound), hfold]
  · have hends : j = 0 ∨ j = 2 * m := by omega
    rcases hends with rfl | rfl
    · simp [hzero]
    · simp [hlast]

theorem epsilon_encoding_surjective (m : ℕ) (hm : 1 ≤ m) (v : ℕ → ℕ)
    (hbin : ∀ j, j ≤ 2 * m → v j ≤ 1)
    (hsym : ∀ j, j ≤ 2 * m → v (2 * m - j) = v j)
    (hzero : v 0 = 1) (hlast : v (2 * m) = 1)
    (hone : v 1 = 0) (hpenultimate : v (2 * m - 1) = 0) :
    ∃ a : Fin (m - 1) → Bool, ∀ j, j ≤ 2 * m → epsilon m a j = v j := by
  let a : Fin (m - 1) → Bool := fun i => decide (v (i.val + 2) = 1)
  refine ⟨a, ?_⟩
  intro j hj
  by_cases hin : 1 < j ∧ j < 2 * m - 1
  · have hminpos : 2 ≤ min j (2 * m - j) := by omega
    have hminbound : min j (2 * m - j) ≤ 2 * m := by omega
    have hfold : v (min j (2 * m - j)) = v j := by
      rcases le_total j (2 * m - j) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, hsym j hj]
    rw [epsilon, dif_pos hin]
    change (decide (v (min j (2 * m - j) - 2 + 2) = 1)).toNat = v j
    rw [Nat.sub_add_cancel hminpos, bit_toNat _ (hbin _ hminbound), hfold]
  · have hends : j = 0 ∨ j = 1 ∨ j = 2 * m - 1 ∨ j = 2 * m := by omega
    rcases hends with rfl | rfl | rfl | rfl
    · simp [hzero]
    · simp [epsilon_one m hm, hone]
    · simp [epsilon_penultimate m hm, hpenultimate]
    · simp [hlast]

theorem symmetric_bit_choices_surjective (m : ℕ) (hm : 1 ≤ m) (e f : ℕ → ℕ)
    (hebin : ∀ j, j ≤ 2 * m → e j ≤ 1)
    (hfbin : ∀ j, j ≤ 2 * m → f j ≤ 1)
    (hesym : ∀ j, j ≤ 2 * m → e (2 * m - j) = e j)
    (hfsym : ∀ j, j ≤ 2 * m → f (2 * m - j) = f j)
    (hezero : e 0 = 1) (helast : e (2 * m) = 1)
    (hfzero : f 0 = 1) (hflast : f (2 * m) = 1)
    (hfone : f 1 = 0) (hfpenultimate : f (2 * m - 1) = 0) :
    ∃ a : Choices m, (∀ j, j ≤ 2 * m → eta m a.1 j = e j) ∧
      (∀ j, j ≤ 2 * m → epsilon m a.2 j = f j) := by
  obtain ⟨a, ha⟩ := eta_encoding_surjective m e hebin hesym hezero helast
  obtain ⟨b, hb⟩ := epsilon_encoding_surjective m hm f hfbin hfsym hfzero hflast hfone hfpenultimate
  exact ⟨(a, b), ha, hb⟩

theorem base_decompositions_card (m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.image (baseLetter m)).card = 2 ^ (halfHeight m - 2) := by
  rw [Finset.card_image_of_injective _ (baseLetter_injective m hm), Finset.card_univ, choices_card m hm]
  congr 1


end CorralFormalization.Results.ConstructionCorrespondence.SwitchBits
