import CorralFormalization.EndpointProof.Factor.Allocation.VirtualClosure

/-!
# Choose router settings only after the exact physical closing matching

The endpoint-to-input permutation is built from the actual exact-matching matching,
the virtual terminal bijection, the ordinary endpoint enumeration and the
fixed router. This does not yet expand the resulting single cycle.
-/

open scoped Classical
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointRouter EndpointMatching.AbsorptionAssembly
open Equiv Equiv.Perm
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}

def PhysicalRouter.inputEquiv {sample : AugmentedSample G m}
    {special : Fin 3 → Finset G} {W D : Finset G} {ℓ : ℕ}
    (R : PhysicalRouter sample special W D ℓ) : Fin ℓ ≃ special 0 :=
  Equiv.ofBijective (fun i => ⟨R.input i, R.input_mem i⟩) (by
    constructor
    · intro i j hij
      exact R.input_injective (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := R.input_covers x.val x.property
      exact ⟨i, Subtype.ext hi⟩)

/-- The matching and virtual terminal links define the actual closing
permutation. The fixed router then supplies a later setting with one cycle. -/
theorem PhysicalRouter.choose_settings_after_matching
    {sample : AugmentedSample G m} {special : Fin 3 → Finset G}
    {W D : Finset G} {ℓ : ℕ} (R : PhysicalRouter sample special W D ℓ)
    (E Y X C : Finset G) (hY : Y ⊆ E) (hX : X ⊆ special 0)
    (hXY : X.card = Y.card) (endAtOutput : Fin ℓ ≃ E)
    (M : PhysicalDifferenceMatching (E \ Y) (special 0 \ X) C) :
    ∃ virtual : Y ≃ X, ∃ full : E ≃ special 0, ∃ closing : Perm (Fin ℓ),
      (∀ i, R.input (closing i) = (full (endAtOutput i)).val) ∧
      (∀ y : E, ∀ hy : y.val ∈ Y, (full y).val = (virtual ⟨y.val, hy⟩).val) ∧
      (∀ y : E, ∀ hy : y.val ∉ Y,
        (M.color ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩).val = (full y).val-y.val) ∧
      ∃ a b : List (Fin ℓ × Fin ℓ),
        a.Sublist (firstLayer ℓ) ∧ b.Sublist (secondLayer ℓ) ∧
        (closing * (switchProduct b * switchProduct a)).IsCycleOn Set.univ ∧
        (∀ i, (installedRoutes R.first R.second a b i).first = R.input i ∧
          (installedRoutes R.first R.second a b i).last =
            R.output ((switchProduct b * switchProduct a) i)) := by
  have hc : Fintype.card Y = Fintype.card X := by simpa using hXY.symm
  let virtual : Y ≃ X := Fintype.equivOfCardEq hc
  let full : E ≃ special 0 := extendPhysicalClosing E (special 0) Y X C hY hX virtual M
  let closing : Perm (Fin ℓ) := (endAtOutput.trans full).trans R.inputEquiv.symm
  obtain ⟨a,b,ha,hb,hcycle,hends⟩ := R.later_closing closing
  refine ⟨virtual, full, closing, ?_, ?_, ?_, a, b, ha, hb, hcycle, hends⟩
  · intro i
    have h := R.inputEquiv.apply_symm_apply (full (endAtOutput i))
    exact congrArg Subtype.val h
  · intro y hy
    exact extendPhysicalClosing_marked E (special 0) Y X C hY hX virtual M y hy
  · intro y hy
    exact extendPhysicalClosing_real_difference E (special 0) Y X C hY hX virtual M y hy

end
end EndpointFactor.Allocation
