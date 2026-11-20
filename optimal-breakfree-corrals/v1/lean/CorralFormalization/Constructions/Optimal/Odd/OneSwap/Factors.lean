import CorralFormalization.Constructions.Optimal.Odd.OneSwap.Word

namespace CorralFormalization.OneSwapOdd

/-- The first factor with shift `z = 2A`. -/
def C (A : ℕ) (s : Fin (h A)) : Finset ℕ :=
  Finset.univ.image (fun j : Fin (K A) =>
    (oddConstructionPrefix A j.val + 2 * A + K A * s.val) % U A)

/-- The two-point factor in the odd construction. -/
def D (A : ℕ) (t : Fin (h A)) : Finset ℕ :=
  {2 * t.val, (2 * t.val + 3) % (2 * h A)}

theorem C_nonempty (A : ℕ) (s : Fin (h A)) : (C A s).Nonempty := by
  exact ⟨_, Finset.mem_image.mpr ⟨⟨0, by unfold K; omega⟩,
    Finset.mem_univ _, rfl⟩⟩

theorem C_bound (A : ℕ) (s : Fin (h A)) (x : ℕ) (hx : x ∈ C A s) :
    x < U A := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact Nat.mod_lt _ (by unfold U h K; positivity)

theorem C_eq_rotated_prefix (A : ℕ) (hA : 1 ≤ A) (s : Fin (h A)) :
    C A s = (oddConstructionRawPrefixSet A).image
      (fun p => (p + (2 * A + K A * s.val)) % U A) := by
  rw [raw_prefix_eq_image A hA, Finset.image_image]
  simp only [C, Function.comp_def, Nat.add_assoc]

theorem C_gaps (A : ℕ) (hA : 1 ≤ A) (s : Fin (h A)) :
    finiteCyclicGapInventory (U A) (C A s) = Multiset.ofList (oddConstructionGapWord A) := by
  rw [C_eq_rotated_prefix A hA s]
  rw [finite_set_cyclic_gap_rotate _ _ _ (by unfold U h K; positivity)
    (raw_prefix_bound A hA)]
  exact raw_prefix_gaps A hA

def Q (A : ℕ) : Finset ℕ :=
  Finset.univ.image (fun j : Fin (K A) => (oddConstructionPrefix A j.val + 2 * A) % U A)

def shiftedResidue (A : ℕ) (j : Fin (K A)) : Fin (K A) :=
  ⟨((oddConstructionPrefix A j.val + 2 * A) % U A) % K A,
    Nat.mod_lt _ (by unfold K; omega)⟩

theorem shiftedResidue_bijective (A : ℕ) (hA : 1 ≤ A) :
    Function.Bijective (shiftedResidue A) := by
  let : NeZero (K A) := ⟨by unfold K; omega⟩
  let z : Fin (K A) := ⟨2 * A, by unfold K; omega⟩
  have heq : shiftedResidue A =
      (Equiv.addRight z) ∘ actualOddPrefixResidue A := by
    funext j
    apply Fin.ext
    change ((oddConstructionPrefix A j.val + 2 * A) % (h A * K A)) % K A =
      (oddConstructionPrefix A j.val % K A + 2 * A) % K A
    rw [Nat.mod_mul_left_mod, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by unfold K; omega : 2 * A < K A)]
  rw [heq]
  exact (Equiv.addRight z).bijective.comp (prefix_residue_bijective A hA)

theorem Q_transversal (A : ℕ) (hA : 1 ≤ A) :
    ∀ r, r < K A → ∃! q, q ∈ Q A ∧ q % K A = r := by
  intro r hr
  obtain ⟨j, hj⟩ := (shiftedResidue_bijective A hA).surjective ⟨r, hr⟩
  let q := (oddConstructionPrefix A j.val + 2 * A) % U A
  have hq : q ∈ Q A := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hqr : q % K A = r := congrArg Fin.val hj
  refine ⟨q, ⟨hq, hqr⟩, ?_⟩
  intro p ⟨hp, hpr⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
  have heq : shiftedResidue A i = shiftedResidue A j := by
    apply Fin.ext
    change ((oddConstructionPrefix A i.val + 2 * A) % U A) % K A = q % K A
    rw [hi, hpr, hqr]
  have hij := (shiftedResidue_bijective A hA).injective heq
  subst i
  exact hi.symm

theorem C_eq_translatedSites (A : ℕ) (s : Fin (h A)) :
    C A s = translatedSites (h A) (K A) s.val (Q A) := by
  simp [C, translatedSites, Q, Finset.image_image, Function.comp_def,
    U, Nat.mod_add_mod]

theorem C_partition (A : ℕ) (hA : 1 ≤ A) (x : ℕ) (hx : x < U A) :
    ∃! s : Fin (h A), x ∈ C A s := by
  simp only [C_eq_translatedSites]
  apply transversal_block_translates_partition _ _ _ (by unfold h; omega)
    (by unfold K; omega)
  · intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.mod_lt _ (by unfold U h K; positivity)
  · exact Q_transversal A hA
  · exact hx

theorem D_nonempty (A : ℕ) (t : Fin (h A)) : (D A t).Nonempty := by
  simp [D]

theorem D_second (A : ℕ) (t : Fin (h A)) :
    (2 * t.val + 3) % (2 * h A) =
      if t.val = 2 * A + 2 then 1 else 2 * t.val + 3 := by
  have ht := t.isLt
  unfold h at ht ⊢
  split_ifs with he
  · rw [he]
    have hnum : 2 * (2 * A + 2) + 3 = 2 * (2 * A + 3) + 1 := by omega
    rw [hnum, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * (2 * A + 3))]
  · exact Nat.mod_eq_of_lt (by omega)

theorem D_bound (A : ℕ) (t : Fin (h A)) (x : ℕ) (hx : x ∈ D A t) :
    x < 2 * h A := by
  have ht := t.isLt
  simp only [D, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · omega
  · exact Nat.mod_lt _ (by unfold h; omega)

theorem D_partition (A : ℕ) (x : ℕ) (hx : x < 2 * h A) :
    ∃! t : Fin (h A), x ∈ D A t := by
  have hmem (t : Fin (h A)) :
      x ∈ D A t ↔ x = 2 * t.val ∨
        x = (if t.val = 2 * A + 2 then 1 else 2 * t.val + 3) := by
    simp [D, D_second]
  have huniq (t u : Fin (h A)) (ht : x ∈ D A t) (hu : x ∈ D A u) : t = u := by
    apply Fin.ext
    have htlt := t.isLt
    have hult := u.isLt
    rw [hmem] at ht hu
    unfold h at htlt hult
    split_ifs at ht hu <;> omega
  by_cases heven : x % 2 = 0
  · let t : Fin (h A) := ⟨x / 2, by omega⟩
    have ht : x ∈ D A t := (hmem t).2 (Or.inl (by dsimp [t]; omega))
    exact ⟨t, ht, fun u hu => huniq u t hu ht⟩
  · by_cases hx1 : x = 1
    · let t : Fin (h A) := ⟨2 * A + 2, by unfold h; omega⟩
      have ht : x ∈ D A t := (hmem t).2 (Or.inr (by simp [t, hx1]))
      exact ⟨t, ht, fun u hu => huniq u t hu ht⟩
    · let t : Fin (h A) := ⟨(x - 3) / 2, by unfold h at *; omega⟩
      have ht : x ∈ D A t := by
        apply (hmem t).2
        right
        have htne : t.val ≠ 2 * A + 2 := by dsimp [t]; unfold h at hx; omega
        rw [if_neg htne]
        dsimp [t]
        omega
      exact ⟨t, ht, fun u hu => huniq u t hu ht⟩

theorem D_min (A : ℕ) (t : Fin (h A)) :
    (D A t).min' (D_nonempty A t) =
      if t.val = 2 * A + 2 then 1 else 2 * t.val := by
  simp only [D, Finset.min'_pair]
  rw [D_second]
  split_ifs with ht
  · rw [ht, min_eq_right (by omega)]
  · exact min_eq_left (by omega)

theorem D_tail (A : ℕ) (t : Fin (h A)) :
    2 * h A - (D A t).max' (D_nonempty A t) =
      if t.val = 2 * A + 2 then 2 else K A - 2 * t.val := by
  simp only [D, Finset.max'_pair]
  rw [D_second]
  split_ifs with ht
  · rw [ht, max_eq_left (by omega)]
    unfold h
    omega
  · rw [max_eq_right (by omega)]
    unfold h K
    omega

theorem D_gaps (A : ℕ) (t : Fin (h A)) :
    finiteCyclicGapInventory (2 * h A) (D A t) = Multiset.ofList [3, K A] := by
  rw [D, D_second]
  split_ifs with ht
  · rw [ht]
    have hpair := OddCorePhysicalRows.finiteCyclicGapInventory_pair
      (2 * h A) 1 (2 * (2 * A + 2)) (by omega) (by unfold h; omega)
    rw [Finset.pair_comm]
    rw [hpair]
    have hlarge : 2 * (2 * A + 2) - 1 = K A := by unfold K; omega
    have hsmall : 2 * h A + 1 - 2 * (2 * A + 2) = 3 := by unfold h; omega
    rw [hlarge, hsmall]
    exact Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ [])
  · have htlt : 2 * t.val + 3 < 2 * h A := by
      have := t.isLt
      unfold h at *
      omega
    rw [OddCorePhysicalRows.finiteCyclicGapInventory_pair
      (2 * h A) (2 * t.val) (2 * t.val + 3) (by omega) htlt]
    have hsmall : 2 * t.val + 3 - 2 * t.val = 3 := by omega
    have hlarge : 2 * h A + 2 * t.val - (2 * t.val + 3) = K A := by
      unfold h K; omega
    rw [hsmall, hlarge]

end CorralFormalization.OneSwapOdd
