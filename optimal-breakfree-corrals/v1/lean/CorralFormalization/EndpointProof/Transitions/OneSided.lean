import CorralFormalization.EndpointProof.Transitions.FourierExceptional

/-!
# One-sided raw loss and arbitrary later additions

These bounds use exactly `K = R ∩ T` and `J = T \ R`.  Only raw deletions
are charged; later additions can be of constant density.  The exceptional
sets may depend on the entire later target.
-/

open scoped Classical BigOperators symmDiff

namespace EndpointTransitions

noncomputable section

open EndpointFractionalRawEvent

variable {G : Type*} [AddCommGroup G] [Fintype G]

def core (R T : Finset G) : Finset G := R ∩ T
def additions (R T : Finset G) : Finset G := T \ R

theorem pairCount_comm (R U : Finset G) (x : G) : pairCount R U x = pairCount U R x := by
  let e : Equiv.Perm G := ⟨fun y => x-y,fun y => x-y,by intro y; simp,by intro y; simp⟩
  unfold pairCount
  calc
    _ = ∑ y, setBit R (x-(x-y))*setBit U (x-y) := by
      exact (Equiv.sum_comp e (fun y => setBit R (x-y)*setBit U y)).symm
    _ = _ := by simp only [sub_sub_cancel]; apply Finset.sum_congr rfl; intro y _; ring

theorem pairCount_edit_bound (R U R' U' : Finset G) (x : G) :
    |pairCount R U x-pairCount R' U' x| ≤
      ((R ∆ R').card : ℝ)+((U ∆ U').card : ℝ) := by
  let e : Equiv.Perm G := ⟨fun y => x-y,fun y => x-y,by intro y; simp,by intro y; simp⟩
  simpa only [pairCount, e, Equiv.coe_fn_mk, Equiv.refl_apply] using
    productCount_edit_bound R U R' U' e (Equiv.refl G)

theorem raw_core_symmDiff (R T : Finset G) : R ∆ core R T = R \ T := by
  ext g
  simp [core, Finset.mem_symmDiff]
  tauto

/-- Exact cardinal conservation, including arbitrary later additions. -/
theorem additions_card_identity (R T : Finset G) :
    (additions R T).card + R.card = T.card + (R \ T).card := by
  have hR := Finset.card_sdiff_add_card_inter R T
  have hT := Finset.card_sdiff_add_card_inter T R
  simp only [Finset.inter_comm T R] at hT
  dsimp [additions]
  omega

/-- The `3ηn` addition-size estimate in the ordinary transition lemma. -/
theorem additions_size {R T : Finset G} {a q η : ℝ}
    (hraw : FourierGood R a η) (hη : 0 ≤ η) (hηone : η ≤ 1)
    (htarget : |(T.card : ℝ)-q*(Fintype.card G : ℝ)| ≤ η*(Fintype.card G : ℝ))
    (hloss : ((R \ T).card : ℝ) ≤ η*(Fintype.card G : ℝ)) :
    |((additions R T).card : ℝ)-(q-a)*(Fintype.card G : ℝ)| ≤
      3*η*(Fintype.card G : ℝ) := by
  have hid : ((additions R T).card : ℝ)+(R.card : ℝ) =
      (T.card : ℝ)+((R \ T).card : ℝ) := by exact_mod_cast additions_card_identity R T
  have hr := abs_le.mp hraw.rawSize
  have ht := abs_le.mp htarget
  have hηsq : η^2*(Fintype.card G : ℝ) ≤ η*(Fintype.card G : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)
  apply abs_le.mpr
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (R \ T).card]

/-- Passing from two raw sets to their surviving cores costs at most the
two raw losses at every label. -/
theorem core_pair_edit_bound (R S T U : Finset G) (x : G) :
    |pairCount (core R T) (core S U) x-pairCount R S x| ≤
      ((R \ T).card : ℝ)+((S \ U).card : ℝ) := by
  rw [abs_sub_comm]
  simpa only [raw_core_symmDiff] using pairCount_edit_bound R S (core R T) (core S U) x

/-- The pointwise core/core error of the ordinary transition lemma away from the one raw/raw
exceptional label set. -/
theorem core_pair_error {R S T U : Finset G} {a b η : ℝ} {x : G}
    (hR : FourierGood R a η) (hS : FourierGood S b η)
    (hη : 0 ≤ η) (hηone : η ≤ 1) (ha : 0 ≤ a) (haone : a ≤ 1)
    (hRloss : ((R \ T).card : ℝ) ≤ η*(Fintype.card G : ℝ))
    (hSloss : ((S \ U).card : ℝ) ≤ η*(Fintype.card G : ℝ))
    (hx : x ∉ exceptional R S a η) :
    |pairCount (core R T) (core S U) x-a*b*(Fintype.card G : ℝ)| ≤
      4*η*(Fintype.card G : ℝ) := by
  have hm := mixedError_le_of_not_exceptional R S a η x hx
  have hs := hS.rawSize
  have he := core_pair_edit_bound R S T U x
  have hsize : |a*((S.card : ℝ)-b*(Fintype.card G : ℝ))| ≤ η*(Fintype.card G : ℝ) := by
    rw [abs_mul, abs_of_nonneg ha]
    calc
      a*|(S.card : ℝ)-b*(Fintype.card G : ℝ)| ≤
        a*(η^2*(Fintype.card G : ℝ)) := mul_le_mul_of_nonneg_left hs ha
      _ ≤ 1*(η*(Fintype.card G : ℝ)) := by
        apply mul_le_mul haone
        · exact mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)
        · positivity
        · norm_num
      _ = _ := one_mul _
  have hraw : |pairCount R S x-a*b*(Fintype.card G : ℝ)| ≤
      2*η*(Fintype.card G : ℝ) := by
    have htri := abs_add_le (mixedError R S a x)
      (a*((S.card : ℝ)-b*(Fintype.card G : ℝ)))
    have hid : mixedError R S a x+a*((S.card : ℝ)-b*(Fintype.card G : ℝ)) =
        pairCount R S x-a*b*(Fintype.card G : ℝ) := by unfold mixedError; ring
    rw [hid] at htri
    linarith
  exact (abs_sub_le _ (pairCount R S x) _).trans (by linarith)

/-- The pointwise added/core error of the ordinary transition lemma. The exceptional set belongs to
the raw set and the actual realised addition set. -/
theorem additions_core_error {R S T U : Finset G} {a b q η : ℝ} {x : G}
    (hR : FourierGood R a η) (hS : FourierGood S b η)
    (hη : 0 ≤ η) (hηone : η ≤ 1) (ha : 0 ≤ a) (haone : a ≤ 1)
    (hU : |(U.card : ℝ)-q*(Fintype.card G : ℝ)| ≤ η*(Fintype.card G : ℝ))
    (hRloss : ((R \ T).card : ℝ) ≤ η*(Fintype.card G : ℝ))
    (hSloss : ((S \ U).card : ℝ) ≤ η*(Fintype.card G : ℝ))
    (hx : x ∉ exceptional R (additions S U) a η) :
    |pairCount (core R T) (additions S U) x-a*(q-b)*(Fintype.card G : ℝ)| ≤
      5*η*(Fintype.card G : ℝ) := by
  have hj := additions_size hS hη hηone hU hSloss
  have hm := mixedError_le_of_not_exceptional R (additions S U) a η x hx
  have he : |pairCount (core R T) (additions S U) x-pairCount R (additions S U) x| ≤
      η*(Fintype.card G : ℝ) := by
    rw [abs_sub_comm]
    have he := pairCount_edit_bound R (additions S U) (core R T) (additions S U) x
    simp [raw_core_symmDiff] at he
    exact he.trans hRloss
  have hs : |a*(((additions S U).card : ℝ)-(q-b)*(Fintype.card G : ℝ))| ≤
      3*η*(Fintype.card G : ℝ) := by
    rw [abs_mul, abs_of_nonneg ha]
    calc
      _ ≤ a*(3*η*(Fintype.card G : ℝ)) := mul_le_mul_of_nonneg_left hj ha
      _ ≤ 1*(3*η*(Fintype.card G : ℝ)) := mul_le_mul_of_nonneg_right haone (by positivity)
      _ = _ := one_mul _
  have hr : |pairCount R (additions S U) x-a*(q-b)*(Fintype.card G : ℝ)| ≤
      4*η*(Fintype.card G : ℝ) := by
    have htri := abs_add_le (mixedError R (additions S U) a x)
      (a*(((additions S U).card : ℝ)-(q-b)*(Fintype.card G : ℝ)))
    have hid : mixedError R (additions S U) a x+
        a*(((additions S U).card : ℝ)-(q-b)*(Fintype.card G : ℝ)) =
        pairCount R (additions S U) x-a*(q-b)*(Fintype.card G : ℝ) := by
      unfold mixedError; ring
    rw [hid] at htri
    linarith
  exact (abs_sub_le _ (pairCount R (additions S U) x) _).trans (by linarith)

end
end EndpointTransitions
