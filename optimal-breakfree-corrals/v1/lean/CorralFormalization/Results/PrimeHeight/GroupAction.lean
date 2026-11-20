import CorralFormalization.DiversityCompletion.WordBridge
import Mathlib.GroupTheory.GroupAction.CardCommute

/-!
# The physical stabilizer acts freely on unlabelled rigid rows

The action below uses exactly the existing physical motions and row images.
No row labels, selected construction, or symmetry hypothesis are introduced.
-/

namespace CorralFormalization.PhysicalCorral.Motion

variable {M : ℕ}

instance : Group (Motion M) where
  mul := compose
  mul_assoc := by
    intro a b c
    change compose (compose a b) c = compose a (compose b c)
    cases a <;> cases b <;> cases c <;>
      simp only [compose] <;> congr 1 <;> ring
  one := rotation 0
  one_mul := by
    intro a
    change compose (rotation 0) a = a
    cases a <;> simp [compose]
  mul_one := by
    intro a
    change compose a (rotation 0) = a
    cases a <;> simp [compose]
  inv := fun f => match f with
    | rotation c => rotation (-c)
    | reflection c => reflection c
  inv_mul_cancel := by
    rintro (a | a)
    · change compose (rotation (-a)) (rotation a) = rotation 0
      simp [compose]
    · change compose (reflection a) (reflection a) = rotation 0
      simp [compose]

@[simp] theorem one_eq : (1 : Motion M) = rotation 0 := rfl
@[simp] theorem mul_eq (f g : Motion M) : f * g = f.compose g := rfl
@[simp] theorem rotation_inv (c : ZMod M) : (rotation c)⁻¹ = rotation (-c) := rfl
@[simp] theorem reflection_inv (c : ZMod M) : (reflection c)⁻¹ = reflection c := rfl

def equivSum : Motion M ≃ ZMod M ⊕ ZMod M where
  toFun := fun f => match f with
    | rotation c => .inl c
    | reflection c => .inr c
  invFun := fun f => match f with
    | .inl c => rotation c
    | .inr c => reflection c
  left_inv := by rintro (c | c) <;> rfl
  right_inv := by rintro (c | c) <;> rfl

instance [NeZero M] : Fintype (Motion M) := Fintype.ofEquiv _ equivSum.symm

theorem card [NeZero M] : Fintype.card (Motion M) = 2 * M := by
  rw [Fintype.card_congr equivSum, Fintype.card_sum, ZMod.card, two_mul]

@[simp] theorem rotation_pow (c : ZMod M) (k : ℕ) :
    (rotation c : Motion M)^k = rotation (k • c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [mul_eq, compose, add_nsmul, one_nsmul]

@[simp] theorem reflection_sq (c : ZMod M) : (reflection c : Motion M)^2 = 1 := by
  simp [pow_two, compose]

theorem reflection_pow_odd (c : ZMod M) {k : ℕ} (hk : Odd k) :
    (reflection c : Motion M)^k = reflection c := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_add, pow_mul]
  simp [compose]

/-- The full physical action on unlabelled families, used by the orbit census. -/
instance familyAction : MulAction (Motion M) (Finset (Finset (ZMod M))) where
  smul := onFamily
  one_smul := identity_onFamily
  mul_smul := onFamily_compose

@[simp] theorem family_smul_eq (f : Motion M) (F : Finset (Finset (ZMod M))) :
    f • F = f.onFamily F := rfl

/-- On every clock of size at least three, distinct algebraic motions are
distinct actual site maps. This includes all odd-prime optimal clocks. -/
theorem act_faithful (hM : 3 ≤ M) : Function.Injective (fun f : Motion M => f.act) := by
  letI : NeZero M := ⟨by omega⟩
  have htwo : (2 : ZMod M) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    change ((2 : ℕ) : ZMod M).val = (0 : ZMod M).val at hv
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at hv
    omega
  intro f g hfg
  have h0 := congrFun hfg 0
  have h1 := congrFun hfg 1
  cases f with
  | rotation a =>
    cases g with
    | rotation b =>
      exact congrArg rotation (by simpa only [act, add_zero] using h0)
    | reflection b =>
      have hab : a = b := by simpa only [act, add_zero, sub_zero] using h0
      have he : a+1 = a-1 := by simpa only [act, hab] using h1
      exact False.elim (htwo (by linear_combination he))
  | reflection a =>
    cases g with
    | reflection b =>
      exact congrArg reflection (by simpa only [act, sub_zero] using h0)
    | rotation b =>
      have hab : a = b := by simpa only [act, add_zero, sub_zero] using h0
      have he : a-1 = a+1 := by simpa only [act, hab] using h1
      exact False.elim (htwo (by linear_combination -he))

end CorralFormalization.PhysicalCorral.Motion

namespace CorralFormalization.Results.PrimeHeight

open PhysicalCorral

variable {M : ℕ}

/-- The full physical stabilizer, including all permutations of unlabelled rows. -/
def familyStabilizer (F : Finset (Finset (ZMod M))) : Subgroup (Motion M) where
  carrier := {f | f.onFamily F = F}
  one_mem' := Motion.identity_onFamily F
  mul_mem' := by
    intro f g hf hg
    change (f.compose g).onFamily F = F
    rw [Motion.onFamily_compose, hg, hf]
  inv_mem' := by
    intro f hf
    change f⁻¹.onFamily F = F
    have h := congrArg (fun P => f⁻¹.onFamily P) hf
    rw [← Motion.onFamily_compose] at h
    change ((f⁻¹ * f).onFamily F) = f⁻¹.onFamily F at h
    simpa only [inv_mul_cancel, Motion.one_eq, Motion.identity_onFamily] using h.symm

@[simp] theorem mem_familyStabilizer (F : Finset (Finset (ZMod M))) (f : Motion M) :
    f ∈ familyStabilizer F ↔ f.onFamily F = F := Iff.rfl

theorem familyStabilizer_eq_mulAction_stabilizer (F : Finset (Finset (ZMod M))) :
    familyStabilizer F = MulAction.stabilizer (Motion M) F := rfl

/-- An element is an actual member of the unlabelled family. -/
abbrev FamilyRow (F : Finset (Finset (ZMod M))) := {R // R ∈ F}

instance familyRowAction (F : Finset (Finset (ZMod M))) :
    MulAction (familyStabilizer F) (FamilyRow F) where
  smul f R := ⟨f.val.onRow R.val, by
    have hm : f.val.onRow R.val ∈ f.val.onFamily F :=
      Finset.mem_image.mpr ⟨R.val, R.property, rfl⟩
    have hf : f.val.onFamily F = F := f.property
    exact Eq.mp (congrArg (fun P : Finset (Finset (ZMod M)) => f.val.onRow R.val ∈ P) hf) hm⟩
  one_smul := by
    intro R
    apply Subtype.ext
    exact Motion.identity_onRow _
  mul_smul := by
    intro f g R
    apply Subtype.ext
    exact Motion.onRow_compose _ _ _

@[simp] theorem familyRow_smul_val (F : Finset (Finset (ZMod M)))
    (f : familyStabilizer F) (R : FamilyRow F) :
    (f • R).val = f.val.onRow R.val := rfl

/-- Row rigidity is precisely freeness of the stabilizer action on rows. -/
theorem familyRow_action_free (F : Finset (Finset (ZMod M)))
    (hrigid : ∀ R ∈ F, RigidRow R)
    (f : familyStabilizer F) (R : FamilyRow F) (hf : f • R = R) : f = 1 := by
  apply Subtype.ext
  exact hrigid R.val R.property f.val (congrArg Subtype.val hf)

/-- A finite group acting freely on the rows has order dividing the number of rows. -/
theorem stabilizer_card_dvd_rows [NeZero M] (F : Finset (Finset (ZMod M)))
    (hrigid : ∀ R ∈ F, RigidRow R) : Nat.card (familyStabilizer F) ∣ F.card := by
  classical
  let G := familyStabilizer F
  let X := FamilyRow F
  letI (R : X) : Unique (MulAction.stabilizer G R) :=
    { default := 1
      uniq := fun a => Subtype.ext (familyRow_action_free F hrigid a.val R a.property) }
  have hc := MulAction.card_eq_sum_card_group_div_card_stabilizer G X
  simp only [Fintype.card_unique, Nat.div_one, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hc
  have hx : Fintype.card X = F.card := Fintype.card_coe F
  rw [hx] at hc
  rw [Nat.card_eq_fintype_card]
  exact ⟨_, hc.trans (Nat.mul_comm _ _)⟩

end CorralFormalization.Results.PrimeHeight
