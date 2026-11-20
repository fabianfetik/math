import CorralFormalization.DiversityCompletion.ReflectionCount

/-! A concrete pairing of the nonzero phases in Z/(2m+1), with negation
exchanging the two members of every pair. -/

namespace CorralFormalization.PhysicalCorral

instance phaseModNonzero (m : ℕ) : NeZero (2*m+1) := ⟨by omega⟩

def phasePosition (m : ℕ) (p : Fin m × Bool) : ℕ :=
  if p.2 then 2*m-p.1.val else p.1.val+1

theorem phasePosition_bounds (m : ℕ) (p : Fin m × Bool) :
    0 < phasePosition m p ∧ phasePosition m p < 2*m+1 := by
  rcases p with ⟨i, b⟩
  have hi := i.isLt
  cases b <;> simp [phasePosition] <;> omega

abbrev NonzeroPhase (m : ℕ) := {x : ZMod (2*m+1) // x ≠ 0}

def phaseEmbedding (m : ℕ) (p : Fin m × Bool) : NonzeroPhase m :=
  ⟨(phasePosition m p : ZMod (2*m+1)), by
    intro hz
    have hb := phasePosition_bounds m p
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hb.2] at hv
    simp at hv
    omega⟩

theorem phaseEmbedding_val (m : ℕ) (p : Fin m × Bool) :
    (phaseEmbedding m p).val.val = phasePosition m p :=
  ZMod.val_natCast_of_lt (phasePosition_bounds m p).2

theorem phase_val_positive (m : ℕ) (x : NonzeroPhase m) : 0 < x.val.val := by
  have hz : x.val.val ≠ 0 := by
    intro he
    apply x.property
    have hc := ZMod.natCast_zmod_val x.val
    rw [he] at hc
    simpa using hc.symm
  omega

def phaseInverse (m : ℕ) (x : NonzeroPhase m) : Fin m × Bool :=
  if hx : x.val.val ≤ m then
    (⟨x.val.val-1, by have := phase_val_positive m x; omega⟩, false)
  else
    (⟨2*m-x.val.val, by have := ZMod.val_lt x.val; omega⟩, true)

theorem phaseInverse_embedding (m : ℕ) (p : Fin m × Bool) :
    phaseInverse m (phaseEmbedding m p) = p := by
  rcases p with ⟨i, b⟩
  have hi := i.isLt
  cases b with
  | false =>
    have hb : (phaseEmbedding m (i, false)).val.val ≤ m := by
      rw [phaseEmbedding_val]; simp [phasePosition]
    simp only [phaseInverse, dif_pos hb]
    apply Prod.ext
    · apply Fin.ext
      change (phaseEmbedding m (i, false)).val.val - 1 = i.val
      rw [phaseEmbedding_val]
      simp [phasePosition]
    · rfl
  | true =>
    have hb : ¬ (phaseEmbedding m (i, true)).val.val ≤ m := by
      rw [phaseEmbedding_val]; simp [phasePosition]; omega
    simp only [phaseInverse, dif_neg hb]
    apply Prod.ext
    · apply Fin.ext
      change 2*m - (phaseEmbedding m (i, true)).val.val = i.val
      rw [phaseEmbedding_val]
      simp only [phasePosition, ↓reduceIte]
      omega
    · rfl

theorem phaseEmbedding_inverse (m : ℕ) (x : NonzeroPhase m) :
    phaseEmbedding m (phaseInverse m x) = x := by
  apply Subtype.ext
  apply ZMod.val_injective (2*m+1)
  rw [phaseEmbedding_val]
  have hp := phase_val_positive m x
  have hl := ZMod.val_lt x.val
  unfold phaseInverse
  split_ifs with hx
  · simp only [phasePosition, Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [phasePosition, ↓reduceIte]
    omega

def phaseEquiv (m : ℕ) : (Fin m × Bool) ≃ NonzeroPhase m where
  toFun := phaseEmbedding m
  invFun := phaseInverse m
  left_inv := phaseInverse_embedding m
  right_inv := phaseEmbedding_inverse m

theorem phase_complement (m : ℕ) (i : Fin m) :
    ((2*m-i.val : ℕ) : ZMod (2*m+1)) = -((i.val+1 : ℕ) : ZMod (2*m+1)) := by
  have hi := i.isLt
  have he : 2*m-i.val = (2*m+1)-(i.val+1) := by omega
  rw [he, Nat.cast_sub (by omega : i.val+1 ≤ 2*m+1)]
  rw [ZMod.natCast_self]
  simp

theorem phaseEmbedding_neg (m : ℕ) (i : Fin m) (b : Bool) :
    (phaseEmbedding m (i, !b)).val = -(phaseEmbedding m (i, b)).val := by
  cases b with
  | false => simpa [phaseEmbedding, phasePosition] using phase_complement m i
  | true => simp [phaseEmbedding, phasePosition, phase_complement]

def negatePhase (m : ℕ) (x : NonzeroPhase m) : NonzeroPhase m :=
  ⟨-x.val, neg_ne_zero.mpr x.property⟩

theorem negatePhase_involutive (m : ℕ) : Function.Involutive (negatePhase m) := by
  intro x
  apply Subtype.ext
  simp [negatePhase]

theorem negatePhase_embedding (m : ℕ) (i : Fin m) (b : Bool) :
    negatePhase m (phaseEmbedding m (i, b)) = phaseEmbedding m (i, !b) := by
  apply Subtype.ext
  exact (phaseEmbedding_neg m i b).symm

variable {A : Type*} [Fintype A] [DecidableEq A]

def phaseAssignmentEquiv (m : ℕ) : (NonzeroPhase m → A) ≃ (Fin m × Bool → A) where
  toFun f := fun p => f (phaseEmbedding m p)
  invFun g := fun x => g (phaseInverse m x)
  left_inv f := by
    funext x
    simp [phaseEmbedding_inverse]
  right_inv g := by
    funext p
    simp [phaseInverse_embedding]

def phaseReflection (m : ℕ) (σ : A → A) (f : NonzeroPhase m → A) : NonzeroPhase m → A :=
  fun x => σ (f (negatePhase m x))

omit [Fintype A] [DecidableEq A] in
theorem phaseReflection_involutive (m : ℕ) (σ : A → A) (hσ : Function.Involutive σ) :
    Function.Involutive (phaseReflection m σ) := by
  intro f
  funext x
  change σ (σ (f (negatePhase m (negatePhase m x)))) = f x
  rw [negatePhase_involutive m x]
  exact hσ (f x)

omit [Fintype A] [DecidableEq A] in
theorem phaseReflection_conjugate (m : ℕ) (σ : A → A) (f : NonzeroPhase m → A) :
    phaseAssignmentEquiv m (phaseReflection m σ f) =
      pairedReflection m σ (phaseAssignmentEquiv m f) := by
  funext p
  rcases p with ⟨i, b⟩
  simp only [phaseAssignmentEquiv, phaseReflection, pairedReflection, Equiv.coe_fn_mk]
  rw [negatePhase_embedding]

def phaseFixedEquiv (m : ℕ) (σ : A → A) :
    {f : NonzeroPhase m → A // phaseReflection m σ f = f} ≃
      {g : Fin m × Bool → A // pairedReflection m σ g = g} where
  toFun f := ⟨phaseAssignmentEquiv m f.val, by
    rw [← phaseReflection_conjugate, f.property]⟩
  invFun g := ⟨(phaseAssignmentEquiv m).symm g.val, by
    apply (phaseAssignmentEquiv m).injective
    rw [phaseReflection_conjugate]
    simpa using g.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (phaseAssignmentEquiv m).left_inv f.val
  right_inv g := by
    apply Subtype.ext
    exact (phaseAssignmentEquiv m).right_inv g.val

theorem phaseReflection_fixed_card (m : ℕ) (σ : A → A) (hσ : Function.Involutive σ) :
    (Finset.univ.filter (fun f : NonzeroPhase m → A => phaseReflection m σ f = f)).card =
      Fintype.card A ^ m := by
  classical
  have hc := Fintype.card_congr ((phaseFixedEquiv m σ).trans (pairedFixedEquiv m σ hσ))
  have hf : Fintype.card {f : NonzeroPhase m → A // phaseReflection m σ f = f} =
      (Finset.univ.filter (fun f : NonzeroPhase m → A => phaseReflection m σ f = f)).card :=
    Fintype.card_of_subtype _ (by intro f; simp)
  rw [hf] at hc
  simpa using hc

theorem phaseReflection_nonfixed_pairs (m : ℕ) (σ : A → A) (hσ : Function.Involutive σ) :
    (involutionPairs (phaseReflection m σ)).card =
      (Fintype.card A ^ (2*m) - Fintype.card A ^ m) / 2 := by
  classical
  have hphase : Fintype.card (NonzeroPhase m) = 2*m := by
    have hc := Fintype.card_congr (phaseEquiv m)
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hc
    omega
  rw [involutionPairs_card _ (phaseReflection_involutive m σ hσ),
    phaseReflection_fixed_card m σ hσ]
  simp only [Fintype.card_fun, hphase]

end CorralFormalization.PhysicalCorral
