import CorralFormalization.Results.DensityObstruction.Flow

namespace CorralFormalization.Results.DensityObstruction

open scoped BigOperators

def residue (h : ℕ) : ZMod (3*h) →+* ZMod 3 :=
  ZMod.castHom (dvd_mul_right 3 h) (ZMod 3)

def residueClass (h : ℕ) [NeZero (3*h)] (r : ZMod 3) : Finset (ZMod (3*h)) :=
  Finset.univ.filter fun z => residue h z = r

theorem mem_residueClass {h : ℕ} [NeZero (3*h)] (r : ZMod 3) (z : ZMod (3*h)) :
    z ∈ residueClass h r ↔ residue h z = r := by
  simp [residueClass]

theorem residue_val {h : ℕ} [NeZero (3*h)] (z : ZMod (3*h)) :
    residue h z = (z.val : ZMod 3) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact map_natCast _ _

theorem residueClass_eq_image {h : ℕ} [NeZero (3*h)] (r : ZMod 3) :
    residueClass h r = (Finset.range h).image
      (fun k : ℕ => ((3*k+r.val : ℕ) : ZMod (3*h))) := by
  ext z
  rw [mem_residueClass, Finset.mem_image]
  constructor
  · intro hz
    have hmod : z.val % 3 = r.val := by
      rw [residue_val] at hz
      have hv := congrArg ZMod.val hz
      simpa only [ZMod.val_natCast] using hv
    refine ⟨z.val / 3, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      have hlt := z.val_lt
      omega
    · have hdecomp := Nat.mod_add_div z.val 3
      rw [hmod] at hdecomp
      have he : 3 * (z.val / 3) + r.val = z.val := by omega
      rw [he, ZMod.natCast_zmod_val]
  · rintro ⟨k, hk, rfl⟩
    rw [map_natCast]
    push_cast
    have h3 : (3 : ZMod 3) = 0 := by decide
    rw [h3, zero_mul, zero_add, ZMod.natCast_zmod_val]

theorem classParam_injOn {h : ℕ} [NeZero (3*h)] (r : ZMod 3) :
    Set.InjOn (fun k : ℕ => ((3*k+r.val : ℕ) : ZMod (3*h))) (Finset.range h) := by
  intro k hk l hl he
  have hk' := Finset.mem_range.mp hk
  have hl' := Finset.mem_range.mp hl
  have hr := r.val_lt
  have hkv : 3*k+r.val < 3*h := by omega
  have hlv : 3*l+r.val < 3*h := by omega
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hkv, ZMod.val_natCast_of_lt hlv] at hv
  omega

theorem residueClass_card {h : ℕ} [NeZero (3*h)] (r : ZMod 3) :
    (residueClass h r).card = h := by
  rw [residueClass_eq_image, Finset.card_image_of_injOn (classParam_injOn r),
    Finset.card_range]

theorem residueClass_disjoint {h : ℕ} [NeZero (3*h)]
    (r s : ZMod 3) (hrs : r ≠ s) :
    Disjoint (residueClass h r) (residueClass h s) := by
  apply Finset.disjoint_left.mpr
  intro z hz hr
  exact hrs ((mem_residueClass r z).mp hz |>.symm.trans ((mem_residueClass s z).mp hr))

theorem sum_classes_zero_one {h : ℕ} [NeZero (3*h)] :
    (∑ z ∈ residueClass h 0, z) + (∑ z ∈ residueClass h 1, z) = (h : ZMod (3*h)) := by
  rw [residueClass_eq_image, residueClass_eq_image,
    Finset.sum_image (classParam_injOn 0), Finset.sum_image (classParam_injOn 1)]
  have hv0 : (0 : ZMod 3).val = 0 := rfl
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  rw [hv0, hv1]
  let S : ZMod (3*h) := ∑ k ∈ Finset.range h, (k : ZMod (3*h))
  have hs2 : S * 2 = (h : ZMod (3*h)) * ((h-1 : ℕ) : ZMod (3*h)) := by
    have hh := congrArg (fun m : ℕ => (m : ZMod (3*h))) (Finset.sum_range_id_mul_two h)
    push_cast at hh
    exact hh
  have hn : (3 : ZMod (3*h)) * h = 0 := by
    have hh := ZMod.natCast_self (3*h)
    push_cast at hh
    exact hh
  calc
    _ = 3 * (S * 2) + (h : ZMod (3*h)) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
        add_zero, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      dsimp [S]
      ring
    _ = 3 * ((h : ZMod (3*h)) * ((h-1 : ℕ) : ZMod (3*h))) + h := by rw [hs2]
    _ = h := by rw [← mul_assoc, hn, zero_mul, zero_add]

end CorralFormalization.Results.DensityObstruction
