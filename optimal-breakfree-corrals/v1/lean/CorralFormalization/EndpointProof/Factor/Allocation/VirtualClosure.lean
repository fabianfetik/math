import CorralFormalization.EndpointProof.Factor.Allocation.ExactClosing

/-!
# Adjoining every virtual terminal edge to the actual exact-matching matching

The true matching covers `ends \ Y → starts \ X`. A finite bijection
`Y ≃ X` adds exactly the virtual edges; no colour is assigned to them.
-/

open scoped Classical
namespace EndpointFactor.Allocation
open EndpointMatching.AbsorptionAssembly
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]

def markedSubtypeEquiv (E Y : Finset G) (hY : Y ⊆ E) :
    {x : E // x.val ∈ Y} ≃ Y where
  toFun x := ⟨x.val.val, x.property⟩
  invFun y := ⟨⟨y.val, hY y.property⟩, y.property⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl

def unmarkedSubtypeEquiv (E Y : Finset G) :
    {x : E // x.val ∉ Y} ≃ ↥(E \ Y) where
  toFun x := ⟨x.val.val, Finset.mem_sdiff.mpr ⟨x.val.property, x.property⟩⟩
  invFun y := ⟨⟨y.val, (Finset.mem_sdiff.mp y.property).1⟩,
    (Finset.mem_sdiff.mp y.property).2⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl

/-- Split the actual endpoint set into marked and unmarked endpoints. -/
def endpointPartition (E Y : Finset G) (hY : Y ⊆ E) : E ≃ Y ⊕ ↥(E \ Y) :=
  (Equiv.sumCompl (fun x : E => x.val ∈ Y)).symm.trans
    (Equiv.sumCongr (markedSubtypeEquiv E Y hY) (unmarkedSubtypeEquiv E Y))

theorem endpointPartition_marked (E Y : Finset G) (hY : Y ⊆ E) (x : E)
    (hx : x.val ∈ Y) : endpointPartition E Y hY x = Sum.inl ⟨x.val, hx⟩ := by
  have h : (Equiv.sumCompl (fun z : E => z.val ∈ Y)).symm x = Sum.inl ⟨x, hx⟩ :=
    Equiv.sumCompl_symm_apply_of_pos (p := fun z : E => z.val ∈ Y) (a := x) hx
  rw [endpointPartition, Equiv.trans_apply, h]
  rfl

theorem endpointPartition_unmarked (E Y : Finset G) (hY : Y ⊆ E) (x : E)
    (hx : x.val ∉ Y) : endpointPartition E Y hY x =
      Sum.inr ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩ := by
  have h : (Equiv.sumCompl (fun z : E => z.val ∈ Y)).symm x = Sum.inr ⟨x, hx⟩ :=
    Equiv.sumCompl_symm_apply_of_neg (p := fun z : E => z.val ∈ Y) (a := x) hx
  rw [endpointPartition, Equiv.trans_apply, h]
  rfl

/-- The completed endpoint bijection, with the real and virtual parts kept
separate at the type level. -/
def extendPhysicalClosing (E S Y X C : Finset G) (hY : Y ⊆ E) (hX : X ⊆ S)
    (virtual : Y ≃ X) (M : PhysicalDifferenceMatching (E \ Y) (S \ X) C) : E ≃ S :=
  (endpointPartition E Y hY).trans
    ((Equiv.sumCongr virtual M.endpoint).trans (endpointPartition S X hX).symm)

theorem extendPhysicalClosing_marked (E S Y X C : Finset G)
    (hY : Y ⊆ E) (hX : X ⊆ S) (virtual : Y ≃ X)
    (M : PhysicalDifferenceMatching (E \ Y) (S \ X) C) (y : E) (hy : y.val ∈ Y) :
    (extendPhysicalClosing E S Y X C hY hX virtual M y).val = (virtual ⟨y.val, hy⟩).val := by
  let v := virtual ⟨y.val, hy⟩
  have heq : extendPhysicalClosing E S Y X C hY hX virtual M y = ⟨v.val, hX v.property⟩ := by
    apply (endpointPartition S X hX).injective
    conv_rhs => rw [endpointPartition_marked S X hX ⟨v.val, hX v.property⟩ v.property]
    simp only [extendPhysicalClosing, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [endpointPartition_marked E Y hY y hy]
    rfl
  exact congrArg Subtype.val heq

theorem extendPhysicalClosing_unmarked (E S Y X C : Finset G)
    (hY : Y ⊆ E) (hX : X ⊆ S) (virtual : Y ≃ X)
    (M : PhysicalDifferenceMatching (E \ Y) (S \ X) C) (y : E) (hy : y.val ∉ Y) :
    (extendPhysicalClosing E S Y X C hY hX virtual M y).val =
      (M.endpoint ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩).val := by
  let v := M.endpoint ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩
  have hvS := (Finset.mem_sdiff.mp v.property).1
  have hvX := (Finset.mem_sdiff.mp v.property).2
  have heq : extendPhysicalClosing E S Y X C hY hX virtual M y = ⟨v.val, hvS⟩ := by
    apply (endpointPartition S X hX).injective
    conv_rhs => rw [endpointPartition_unmarked S X hX ⟨v.val, hvS⟩ hvX]
    simp only [extendPhysicalClosing, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [endpointPartition_unmarked E Y hY y hy]
    rfl
  exact congrArg Subtype.val heq

/-- Every real closing edge has exactly its own exact-matching colour; virtual edges
are only characterized as the bijection between `Y` and `X`. -/
theorem extendPhysicalClosing_real_difference (E S Y X C : Finset G)
    (hY : Y ⊆ E) (hX : X ⊆ S) (virtual : Y ≃ X)
    (M : PhysicalDifferenceMatching (E \ Y) (S \ X) C) (y : E) (hy : y.val ∉ Y) :
    (M.color ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩).val =
      (extendPhysicalClosing E S Y X C hY hX virtual M y).val - y.val := by
  rw [extendPhysicalClosing_unmarked E S Y X C hY hX virtual M y hy]
  exact M.difference _

/-- Equal finite terminal-set sizes provide the required virtual bijection. -/
theorem exists_extendedPhysicalClosing (E S Y X C : Finset G)
    (hY : Y ⊆ E) (hX : X ⊆ S) (hXY : X.card = Y.card)
    (M : PhysicalDifferenceMatching (E \ Y) (S \ X) C) :
    ∃ virtual : Y ≃ X, ∃ full : E ≃ S,
      (∀ y : E, ∀ hy : y.val ∈ Y, full y = ⟨(virtual ⟨y.val, hy⟩).val,
        hX (virtual ⟨y.val, hy⟩).property⟩) ∧
      (∀ y : E, ∀ hy : y.val ∉ Y,
        (M.color ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩).val = (full y).val-y.val) := by
  have hc : Fintype.card Y = Fintype.card X := by simpa using hXY.symm
  let virtual : Y ≃ X := Fintype.equivOfCardEq hc
  let full := extendPhysicalClosing E S Y X C hY hX virtual M
  refine ⟨virtual, full, ?_, ?_⟩
  · intro y hy
    exact Subtype.ext (extendPhysicalClosing_marked E S Y X C hY hX virtual M y hy)
  · intro y hy
    exact extendPhysicalClosing_real_difference E S Y X C hY hX virtual M y hy

end
end EndpointFactor.Allocation
