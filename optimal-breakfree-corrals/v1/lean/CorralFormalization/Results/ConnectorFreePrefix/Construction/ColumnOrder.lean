import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# The translated Walecki columns in Section 8.1.1

All differences here are ordinary integers. In particular the boundary result
is stronger than congruence modulo the even column modulus.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction

/-- The least even integer at least `r`. -/
def modulus (r : ℕ) : ℕ := if r % 2 = 0 then r else r + 1

/-- The translation in (L4). -/
def translation (r : ℕ) : ℕ :=
  if r % 4 = 2 then (r + 2) / 4 else if r % 4 = 3 then (r + 1) / 4 else 0

/-- The first `r` entries of the Walecki ordering on the even modulus. -/
def walecki (r t : ℕ) : ℕ :=
  if t % 2 = 0 then t / 2 else modulus r - 1 - (t - 1) / 2

/-- The actual ordinary representatives of (L4). -/
def column (r t : ℕ) : ℕ := (walecki r t + translation r) % modulus r

/-- An internal ordinary difference, before reducing modulo any clock. -/
def delta (r t : ℕ) : ℤ := (column r (t + 1) : ℤ) - column r t

/-- The ordinary row boundary difference in (L5). -/
def boundary (r : ℕ) : ℤ := (column r 0 : ℤ) - column r (r - 1)

theorem modulus_bounds (r : ℕ) : r ≤ modulus r ∧ modulus r ≤ r + 1 := by
  unfold modulus
  split_ifs <;> omega

theorem modulus_even (r : ℕ) : modulus r % 2 = 0 := by
  unfold modulus
  split_ifs <;> omega

theorem modulus_pos {r : ℕ} (hr : 0 < r) : 0 < modulus r :=
  hr.trans_le (modulus_bounds r).1

theorem translation_lt {r : ℕ} (hr : 3 ≤ r) : translation r < modulus r := by
  have hm := modulus_bounds r
  unfold translation
  split_ifs <;> omega

theorem column_lt {r : ℕ} (hr : 0 < r) (t : ℕ) : column r t < modulus r :=
  Nat.mod_lt _ (modulus_pos hr)

theorem walecki_lt {r t : ℕ} (hr : 0 < r) (ht : t < r) :
    walecki r t < modulus r := by
  have hm := modulus_bounds r
  unfold walecki
  split_ifs <;> omega

theorem walecki_injective {r s t : ℕ} (hr : 0 < r) (hs : s < r) (ht : t < r)
    (h : walecki r s = walecki r t) : s = t := by
  have hm := modulus_bounds r
  have he := modulus_even r
  unfold walecki at h
  split_ifs at h <;> omega

theorem column_injective {r s t : ℕ} (hr : 0 < r) (hs : s < r) (ht : t < r)
    (h : column r s = column r t) : s = t := by
  apply walecki_injective hr hs ht
  have hc : walecki r s + translation r ≡ walecki r t + translation r [MOD modulus r] := h
  have hc' := Nat.ModEq.add_right_cancel' (translation r) hc
  exact hc'.eq_of_lt_of_lt (walecki_lt hr hs) (walecki_lt hr ht)

/-- A positive residue representative for the unshifted consecutive difference. -/
def deltaResidue (r t : ℕ) : ℕ :=
  if t % 2 = 0 then modulus r - 1 - t else t + 1

theorem deltaResidue_range {r t : ℕ} (hr : 3 ≤ r) (ht : t < r - 1) :
    0 < deltaResidue r t ∧ deltaResidue r t < modulus r := by
  have hm := modulus_bounds r
  unfold deltaResidue
  split_ifs <;> omega

theorem deltaResidue_injective {r s t : ℕ} (hr : 3 ≤ r)
    (hs : s < r - 1) (ht : t < r - 1)
    (h : deltaResidue r s = deltaResidue r t) : s = t := by
  have hm := modulus_bounds r
  have he := modulus_even r
  unfold deltaResidue at h
  split_ifs at h <;> omega

private theorem column_modEq (r t : ℕ) :
    (column r t : ℤ) ≡ (walecki r t : ℤ) + translation r [ZMOD (modulus r : ℤ)] := by
  dsimp [Int.ModEq, column]
  simp only [Int.natCast_mod, Int.natCast_add, Int.emod_emod]

/-- The translated consecutive difference has the exact Walecki residue.
The two parity classes are odd descending and even ascending respectively. -/
theorem delta_modEq {r t : ℕ} (hr : 3 ≤ r) (ht : t < r - 1) :
    delta r t ≡ (deltaResidue r t : ℤ) [ZMOD (modulus r : ℤ)] := by
  have hm := modulus_bounds r
  have he := modulus_even r
  have h := (column_modEq r (t+1)).sub (column_modEq r t)
  have hraw : (walecki r (t+1) : ℤ) - walecki r t =
      if t % 2 = 0 then (modulus r : ℤ) - 1 - t else (t : ℤ) + 1 - modulus r := by
    unfold walecki
    split_ifs <;> omega
  have hsimple : delta r t ≡ (walecki r (t+1) : ℤ) - walecki r t
      [ZMOD (modulus r : ℤ)] := by
    simpa only [delta, add_sub_add_right_eq_sub] using h
  rw [hraw] at hsimple
  by_cases hp : t % 2 = 0
  · simp only [hp, if_true] at hsimple
    simp only [deltaResidue, hp, if_true]
    convert hsimple using 1 <;> omega
  · simp only [hp, if_false] at hsimple
    simp only [deltaResidue, hp, if_false]
    have hc : (t : ℤ) + 1 - modulus r ≡ (t : ℤ) + 1 [ZMOD (modulus r : ℤ)] := by
      simp [Int.ModEq, Int.sub_emod]
    simpa only [Int.natCast_add, Int.natCast_one] using hsimple.trans hc

theorem delta_residue_injective {r s t : ℕ} (hr : 3 ≤ r)
    (hs : s < r-1) (ht : t < r-1)
    (h : delta r s ≡ delta r t [ZMOD (modulus r : ℤ)]) : s = t := by
  have hc := (delta_modEq hr hs).symm.trans (h.trans (delta_modEq hr ht))
  have hb := deltaResidue_range hr hs
  have hd := deltaResidue_range hr ht
  apply deltaResidue_injective hr hs ht
  have hn : deltaResidue r s ≡ deltaResidue r t [MOD modulus r] := (Int.natCast_modEq_iff).mp hc
  exact hn.eq_of_lt_of_lt hb.2 hd.2

/-- No internal difference is zero modulo the even column modulus. -/
theorem delta_not_modEq_zero {r t : ℕ} (hr : 3 ≤ r) (ht : t < r-1) :
    ¬ delta r t ≡ 0 [ZMOD (modulus r : ℤ)] := by
  intro h
  have hc := (delta_modEq hr ht).symm.trans h
  have hb := deltaResidue_range hr ht
  have hn : deltaResidue r t ≡ 0 [MOD modulus r] := (Int.natCast_modEq_iff).mp hc
  have heq := hn.eq_of_lt_of_lt hb.2 (modulus_pos (by omega : 0 < r))
  omega

/-- The table's index of the internal difference equal to the boundary. -/
def boundaryIndex (r : ℕ) : ℕ :=
  if r % 4 = 0 then r / 2 - 1 else if r % 4 = 1 then r / 2 + 1 else r / 2 - 1

private theorem column_eq_of_sum {r t v : ℕ}
    (h : walecki r t + translation r = v) (hv : v < modulus r) : column r t = v := by
  rw [column, h, Nat.mod_eq_of_lt hv]

private theorem column_eq_zero_of_sum {r t : ℕ}
    (h : walecki r t + translation r = modulus r) : column r t = 0 := by
  rw [column, h, Nat.mod_self]

private theorem column_table_zero {k : ℕ} (hk : 1 ≤ k) :
    column (4*k) 0 = 0 ∧ column (4*k) (4*k-1) = 2*k ∧
      column (4*k) (2*k-1) = 3*k ∧ column (4*k) (2*k) = k := by
  have hm : modulus (4*k) = 4*k := by unfold modulus; split_ifs <;> omega
  have hc : translation (4*k) = 0 := by unfold translation; split_ifs <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega

private theorem column_table_one {k : ℕ} (hk : 1 ≤ k) :
    column (4*k+1) 0 = 0 ∧ column (4*k+1) (4*k) = 2*k ∧
      column (4*k+1) (2*k+1) = 3*k+1 ∧ column (4*k+1) (2*k+2) = k+1 := by
  have hm : modulus (4*k+1) = 4*k+2 := by unfold modulus; split_ifs <;> omega
  have hc : translation (4*k+1) = 0 := by unfold translation; split_ifs <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega

private theorem column_table_two {k : ℕ} (hk : 1 ≤ k) :
    column (4*k+2) 0 = k+1 ∧ column (4*k+2) (4*k+1) = 3*k+2 ∧
      column (4*k+2) (2*k) = 2*k+1 ∧ column (4*k+2) (2*k+1) = 0 := by
  have hm : modulus (4*k+2) = 4*k+2 := by unfold modulus; split_ifs <;> omega
  have hc : translation (4*k+2) = k+1 := by unfold translation; split_ifs <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  · apply column_eq_zero_of_sum
    simp only [walecki, hm, hc]
    split_ifs <;> omega

private theorem column_table_three (k : ℕ) :
    column (4*k+3) 0 = k+1 ∧ column (4*k+3) (4*k+2) = 3*k+2 ∧
      column (4*k+3) (2*k) = 2*k+1 ∧ column (4*k+3) (2*k+1) = 0 := by
  have hm : modulus (4*k+3) = 4*k+4 := by unfold modulus; split_ifs <;> omega
  have hc : translation (4*k+3) = k+1 := by unfold translation; split_ifs <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  constructor
  · apply column_eq_of_sum <;> simp only [walecki, hm, hc] <;> (try split_ifs) <;> omega
  · apply column_eq_zero_of_sum
    simp only [walecki, hm, hc]
    split_ifs <;> omega

private theorem column_of_mod_four {r : ℕ} (hr : 3 ≤ r) :
    boundary r = -(r / 2 : ℕ) ∧
      boundaryIndex r < r - 1 ∧ delta r (boundaryIndex r) = boundary r := by
  have hr4 : r % 4 < 4 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div r 4
  generalize hk : r / 4 = k at *
  interval_cases hmod : r % 4
  · have hkpos : 1 ≤ k := by omega
    have heq : r = 4*k := by omega
    rw [heq]
    obtain ⟨h0, hl, hs, hn⟩ := column_table_zero hkpos
    have hi : boundaryIndex (4*k) = 2*k-1 := by unfold boundaryIndex; split_ifs <;> omega
    have hin : boundaryIndex (4*k) + 1 = 2*k := by omega
    constructor
    · simp only [boundary, h0, hl]; omega
    constructor
    · omega
    · unfold delta boundary
      rw [hin, hi]
      simp only [h0, hl, hs, hn]
      omega
  · have hkpos : 1 ≤ k := by omega
    have heq : r = 4*k+1 := by omega
    rw [heq]
    obtain ⟨h0, hl, hs, hn⟩ := column_table_one hkpos
    have hi : boundaryIndex (4*k+1) = 2*k+1 := by unfold boundaryIndex; split_ifs <;> omega
    have hin : boundaryIndex (4*k+1) + 1 = 2*k+2 := by omega
    have hlast : 4*k+1-1 = 4*k := by omega
    constructor
    · simp only [boundary, hlast, h0, hl]; omega
    constructor
    · omega
    · unfold delta boundary
      rw [hin, hi]
      simp only [hlast, h0, hl, hs, hn]
      omega
  · have hkpos : 1 ≤ k := by omega
    have heq : r = 4*k+2 := by omega
    rw [heq]
    obtain ⟨h0, hl, hs, hn⟩ := column_table_two hkpos
    have hi : boundaryIndex (4*k+2) = 2*k := by unfold boundaryIndex; split_ifs <;> omega
    have hin : boundaryIndex (4*k+2) + 1 = 2*k+1 := by omega
    have hlast : 4*k+2-1 = 4*k+1 := by omega
    constructor
    · simp only [boundary, hlast, h0, hl]; omega
    constructor
    · omega
    · unfold delta boundary
      rw [hin, hi]
      simp only [hlast, h0, hl, hs, hn]
      omega
  · have heq : r = 4*k+3 := by omega
    rw [heq]
    obtain ⟨h0, hl, hs, hn⟩ := column_table_three k
    have hi : boundaryIndex (4*k+3) = 2*k := by unfold boundaryIndex; split_ifs <;> omega
    have hin : boundaryIndex (4*k+3) + 1 = 2*k+1 := by omega
    have hlast : 4*k+3-1 = 4*k+2 := by omega
    constructor
    · simp only [boundary, hlast, h0, hl]; omega
    constructor
    · omega
    · unfold delta boundary
      rw [hin, hi]
      simp only [hlast, h0, hl, hs, hn]
      omega

/-- The ordinary equality (L5), not only equality modulo `m`. -/
theorem boundary_eq {r : ℕ} (hr : 3 ≤ r) : boundary r = -(r / 2 : ℕ) :=
  (column_of_mod_four hr).1

theorem boundaryIndex_lt {r : ℕ} (hr : 3 ≤ r) : boundaryIndex r < r - 1 :=
  (column_of_mod_four hr).2.1

theorem delta_boundaryIndex {r : ℕ} (hr : 3 ≤ r) :
    delta r (boundaryIndex r) = boundary r :=
  (column_of_mod_four hr).2.2

/-- The ordinary boundary is one actual ordinary internal difference. -/
theorem boundary_internal {r : ℕ} (hr : 3 ≤ r) :
    ∃ t : Fin (r-1), delta r t.val = boundary r :=
  ⟨⟨boundaryIndex r, boundaryIndex_lt hr⟩, (column_of_mod_four hr).2.2⟩

theorem boundary_internal_unique {r t : ℕ} (hr : 3 ≤ r) (ht : t < r-1)
    (h : delta r t ≡ boundary r [ZMOD (modulus r : ℤ)]) : t = boundaryIndex r := by
  have heq := (column_of_mod_four hr).2.2
  rw [← heq] at h
  exact delta_residue_injective hr ht (boundaryIndex_lt hr) h

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction
