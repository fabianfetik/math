import CorralFormalization.Constructions.Optimal.Odd.OneSwap.Factors
import Mathlib.Data.Int.ModEq

namespace CorralFormalization.OneSwapOdd

/-- Formula (13), with the subtraction performed in the integers before
taking its nonnegative remainder. -/
def coreOwnerValue (A x p : ℕ) : ℕ :=
  (((x : ℤ) - (2 * A : ℕ) - p) % (U A : ℤ)).toNat / K A

theorem coreOwnerValue_of_site (A p : ℕ) (s : Fin (h A)) :
    coreOwnerValue A ((p + 2 * A + K A * s.val) % U A) p = s.val := by
  let x := (p + 2 * A + K A * s.val) % U A
  have hm : (x : ℤ) ≡ (p + 2 * A + K A * s.val : ℕ) [ZMOD U A] := by
    exact Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  have hm' := (hm.sub_right (2 * A : ℕ)).sub_right (p : ℤ)
  have hc : ((p + 2 * A + K A * s.val : ℕ) : ℤ) - (2 * A : ℕ) - p =
      (K A * s.val : ℕ) := by push_cast; ring
  rw [hc] at hm'
  have hbound : K A * s.val < U A := by
    have hm := Nat.mul_lt_mul_of_pos_left s.isLt (by unfold K; omega : 0 < K A)
    simpa only [U, Nat.mul_comm] using hm
  have hr : ((K A * s.val : ℕ) : ℤ) % (U A : ℤ) = (K A * s.val : ℕ) :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hbound)
  have hval := hm'.eq
  rw [hr] at hval
  unfold coreOwnerValue
  change (((x : ℤ) - (2 * A : ℕ) - p) % (U A : ℤ)).toNat / K A = _
  rw [hval, Int.toNat_natCast]
  exact Nat.mul_div_right _ (by unfold K; omega)

/-- The prefix selected modulo `K` in (13) exists and is unique.  The
equation `(p+z) % K = x % K` is the unsigned form of `p ≡ x-z (mod K)`. -/
theorem inverse_prefix_unique (A : ℕ) (hA : 1 ≤ A) (x : ℕ) :
    ∃! p, p ∈ oddConstructionRawPrefixSet A ∧ (p + 2 * A) % K A = x % K A := by
  obtain ⟨j, hj⟩ := (shiftedResidue_bijective A hA).surjective
    ⟨x % K A, Nat.mod_lt _ (by unfold K; omega)⟩
  have hres (i : Fin (K A)) :
      (shiftedResidue A i).val = (oddConstructionPrefix A i.val + 2 * A) % K A := by
    exact Nat.mod_mul_left_mod _ _ _
  have hj' : (oddConstructionPrefix A j.val + 2 * A) % K A = x % K A := by
    rw [← hres]
    exact congrArg Fin.val hj
  refine ⟨oddConstructionPrefix A j.val, ⟨?_, hj'⟩, ?_⟩
  · rw [raw_prefix_eq_image A hA]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · intro p ⟨hp, hpr⟩
    rw [raw_prefix_eq_image A hA] at hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have heq : shiftedResidue A i = shiftedResidue A j := by
      apply Fin.ext
      rw [hres, hres, hpr, hj']
    have hij := (shiftedResidue_bijective A hA).injective heq
    rw [hij]

/-- The literal quotient in (13) is a bounded owner and returns its actual
first-factor row for every site before the seam. -/
theorem C_inverse (A : ℕ) (hA : 1 ≤ A) (x : ℕ) (hx : x < U A)
    (p : ℕ) (hp : p ∈ oddConstructionRawPrefixSet A)
    (hpr : (p + 2 * A) % K A = x % K A) :
    ∃ hs : coreOwnerValue A x p < h A,
      x ∈ C A ⟨coreOwnerValue A x p, hs⟩ := by
  obtain ⟨s, hs, _⟩ := C_partition A hA x hx
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hs
  have hjr : (oddConstructionPrefix A j.val + 2 * A) % K A = x % K A := by
    rw [← hj]
    change _ = ((oddConstructionPrefix A j.val + 2 * A + K A * s.val) %
      (h A * K A)) % K A
    rw [Nat.mod_mul_left_mod, Nat.add_mul_mod_self_left]
  obtain ⟨p0, _, huniq⟩ := inverse_prefix_unique A hA x
  have hjmem : oddConstructionPrefix A j.val ∈ oddConstructionRawPrefixSet A := by
    rw [raw_prefix_eq_image A hA]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hpj : p = oddConstructionPrefix A j.val :=
    (huniq p ⟨hp, hpr⟩).trans (huniq _ ⟨hjmem, hjr⟩).symm
  have howner : coreOwnerValue A x p = s.val := by
    rw [hpj, ← hj]
    exact coreOwnerValue_of_site A _ s
  have hb : coreOwnerValue A x p < h A := by rw [howner]; exact s.isLt
  refine ⟨hb, ?_⟩
  have heq : (⟨coreOwnerValue A x p, hb⟩ : Fin (h A)) = s := Fin.ext howner
  rw [heq]
  exact hs

/-- The displayed even/odd inverse for the two-point factor.  For odd sites
the quotient is an integer, so the exceptional site `y=1` gives `-1 mod h`.
-/
def twoPointOwnerValue (A y : ℕ) : ℕ :=
  if y % 2 = 0 then y / 2 else
    ((((y : ℤ) - 3) / 2) % (h A : ℤ)).toNat

theorem twoPointOwnerValue_of_site (A : ℕ) (t : Fin (h A)) (y : ℕ)
    (hy : y ∈ D A t) : twoPointOwnerValue A y = t.val := by
  simp only [D, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · have heven : (2 * t.val) % 2 = 0 := by omega
    simp only [twoPointOwnerValue, if_pos heven]
    omega
  · rw [D_second]
    by_cases ht : t.val = 2 * A + 2
    · rw [if_pos ht]
      have hh : (0 : ℤ) < h A := by unfold h; omega
      have hminus : (-1 : ℤ) % (h A : ℤ) = (h A : ℤ) - 1 := by
        calc
          _ = (((h A : ℤ) - 1) - (h A : ℤ)) % (h A : ℤ) := by
            congr 1; ring
          _ = ((h A : ℤ) - 1) % (h A : ℤ) := by rw [Int.sub_emod]; simp
          _ = (h A : ℤ) - 1 := Int.emod_eq_of_lt (by omega) (by omega)
      norm_num only [twoPointOwnerValue, Nat.reduceMod, Nat.one_ne_zero, if_false]
      rw [hminus]
      have heq : (h A : ℤ) - 1 = ((h A - 1 : ℕ) : ℤ) := by omega
      rw [heq, Int.toNat_natCast]
      unfold h
      omega
    · rw [if_neg ht]
      have hodd : (2 * t.val + 3) % 2 ≠ 0 := by omega
      simp only [twoPointOwnerValue, if_neg hodd]
      have hquot : (((2 * t.val + 3 : ℕ) : ℤ) - 3) / 2 = (t.val : ℤ) := by omega
      rw [hquot, Int.emod_eq_of_lt (by omega) (by exact_mod_cast t.isLt), Int.toNat_natCast]

theorem D_inverse (A y : ℕ) (hy : y < 2 * h A) :
    ∃ ht : twoPointOwnerValue A y < h A,
      y ∈ D A ⟨twoPointOwnerValue A y, ht⟩ := by
  obtain ⟨t, ht, _⟩ := D_partition A y hy
  have howner := twoPointOwnerValue_of_site A t y ht
  have hb : twoPointOwnerValue A y < h A := by rw [howner]; exact t.isLt
  refine ⟨hb, ?_⟩
  have heq : (⟨twoPointOwnerValue A y, hb⟩ : Fin (h A)) = t := Fin.ext howner
  rw [heq]
  exact ht

end CorralFormalization.OneSwapOdd
