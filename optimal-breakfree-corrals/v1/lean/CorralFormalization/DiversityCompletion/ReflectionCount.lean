import CorralFormalization.ConstructionSupport.PhysicalRows

/-! Exact fixed-point count for a reflection acting on m pairs of supports,
with any involution on the alphabet. A separate geometric proof must
identify the actual nonzero support phases and their reflected letters. -/

namespace CorralFormalization.PhysicalCorral

variable {A : Type*} [Fintype A] [DecidableEq A]

def pairedReflection (m : ℕ) (σ : A → A) (f : Fin m × Bool → A) : Fin m × Bool → A :=
  fun p => σ (f (p.1, !p.2))

omit [Fintype A] [DecidableEq A] in
theorem pairedReflection_involutive (m : ℕ) (σ : A → A) (hσ : Function.Involutive σ) :
    Function.Involutive (pairedReflection m σ) := by
  intro f
  funext p
  rcases p with ⟨i, b⟩
  cases b with
  | false => simpa [pairedReflection] using hσ (f (i, false))
  | true => simpa [pairedReflection] using hσ (f (i, true))

def pairedFixedEquiv (m : ℕ) (σ : A → A) (hσ : Function.Involutive σ) :
    {f : Fin m × Bool → A // pairedReflection m σ f = f} ≃ (Fin m → A) where
  toFun f := fun i => f.val (i, false)
  invFun g := ⟨fun p => if p.2 then σ (g p.1) else g p.1, by
    funext p
    rcases p with ⟨i, b⟩
    cases b with
    | false => simpa [pairedReflection] using hσ (g i)
    | true => simp [pairedReflection]⟩
  left_inv f := by
    apply Subtype.ext
    funext p
    rcases p with ⟨i, b⟩
    cases b with
    | false => rfl
    | true => simpa [pairedReflection] using congrFun f.property (i, true)
  right_inv g := by
    funext i
    rfl

theorem pairedReflection_fixed_card (m : ℕ) (σ : A → A) (hσ : Function.Involutive σ) :
    (Finset.univ.filter (fun f : Fin m × Bool → A => pairedReflection m σ f = f)).card =
      Fintype.card A ^ m := by
  classical
  have hc := Fintype.card_congr (pairedFixedEquiv m σ hσ)
  have hf : Fintype.card {f : Fin m × Bool → A // pairedReflection m σ f = f} =
      (Finset.univ.filter (fun f : Fin m × Bool → A => pairedReflection m σ f = f)).card :=
    Fintype.card_of_subtype _ (by intro f; simp)
  rw [hf] at hc
  simpa using hc

/-- The exact numerical contribution of m paired phases. -/
theorem pairedReflection_nonfixed_pairs (m : ℕ) (σ : A → A)
    (hσ : Function.Involutive σ) :
    (involutionPairs (pairedReflection m σ)).card =
      (Fintype.card A ^ (2 * m) - Fintype.card A ^ m) / 2 := by
  classical
  rw [involutionPairs_card _ (pairedReflection_involutive m σ hσ),
    pairedReflection_fixed_card m σ hσ]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [Nat.mul_comm m 2]

end CorralFormalization.PhysicalCorral
