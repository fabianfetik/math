import CorralFormalization.EndpointProof.Router.Installation.Counts
import CorralFormalization.EndpointProof.Router.Installation.Ports

/-! # The actual event installs two concrete geometry tables

The only premise concerning the random sample is the previously proved
`ReservoirEvent`. The explicit port legality premise is discharged for the
paper's alternating layers in `Paper.lean`.
-/
namespace EndpointRouter
open EndpointLayeredSample
open scoped BigOperators Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G]

/-- Local reservoir membership is retained at every used table slot. -/
def TwoLayerGood {n : ℕ} {L₁ L₂ : MatchingLayer (Fin n)} {input middle output : Fin n → G}
    (RV RC : Set G) (first : LayerGeometry L₁ input middle)
    (second : LayerGeometry L₂ middle output) : Prop :=
  (∀ u, (first.unitPrimitive u).Good RV RC (L₁.unitQuery input middle u)) ∧
  (∀ u, (second.unitPrimitive u).Good RV RC (L₂.unitQuery middle output u))

/-- A complete fixed installation, before any closing permutation is known. -/
theorem ReservoirEvent.install_geometry {n : ℕ} (u : ℝ) (ω : Bool × G → Bool)
    (h : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) ω)
    (L₁ L₂ : MatchingLayer (Fin n)) (input middle output : Fin n → G) (F : Finset G)
    (hports : Function.Injective (routerPort input middle output))
    (hlegal₁ : ∀ v, (L₁.unitQuery input middle v).Legal)
    (hlegal₂ : ∀ v, (L₂.unitQuery middle output v).Legal)
    (hledger : ((F.card + 22*n : ℕ) : ℝ) ≤ explicitRouterDensity u * (Fintype.card G : ℝ)/4) :
    ∃ first : LayerGeometry L₁ input middle,
      ∃ second : LayerGeometry L₂ middle output,
        TwoLayerSupport first second ∧
        TwoLayerGood (vertexReservoir ω) (colorReservoir ω) first second ∧
        (∀ v, Disjoint (twoLayerUnitSupport first second v) F) := by
  let query : Sum L₁.Unit L₂.Unit → Query G :=
    Sum.elim (L₁.unitQuery input middle) (L₂.unitQuery middle output)
  have hqlegal (v) : (query v).Legal := by
    cases v with
    | inl v => exact hlegal₁ v
    | inr v => exact hlegal₂ v
  have hbudget : (F ∪ routerPorts input middle output).card +
      ∑ v, 9*(query v).arity ≤ routerTrialBudget u (Fintype.card G) := by
    have h₁ := Finset.card_union_le F (routerPorts input middle output)
    have h₂ : (routerPorts input middle output).card ≤ 3*n := by
      exact (Finset.card_image_le).trans_eq (by simp [Fintype.card_prod])
    have h₃ := explicitLedger_le_installerBudget u (Fintype.card G) F.card n hledger
    rw [MatchingLayer.twoLayer_weight_sum]
    omega
  obtain ⟨primitive,hgood,hpair,havoid⟩ :=
    h.indexed_install u _ ω query (F ∪ routerPorts input middle output) hqlegal hbudget
  have hg₁ : ∀ v, (primitive (.inl v)).Good (vertexReservoir ω) (colorReservoir ω) (L₁.unitQuery input middle v) := fun v => hgood (.inl v)
  have hg₂ : ∀ v, (primitive (.inr v)).Good (vertexReservoir ω) (colorReservoir ω) (L₂.unitQuery middle output v) := fun v => hgood (.inr v)
  let first := LayerGeometry.fromPrimitives (fun v => primitive (.inl v)) hg₁
  let second := LayerGeometry.fromPrimitives (fun v => primitive (.inr v)) hg₂
  have hsupport (v) : twoLayerUnitSupport first second v = (primitive v).support := by
    cases v with
    | inl v => exact LayerGeometry.fromPrimitives_unitSupport _ _ v
    | inr v => exact LayerGeometry.fromPrimitives_unitSupport _ _ v
  refine ⟨first,second,⟨hports,?_,?_⟩,?_,?_⟩
  · intro i j hij
    rw [hsupport,hsupport]
    exact hpair hij
  · intro v
    rw [hsupport]
    exact (havoid v).mono_right Finset.subset_union_right
  · constructor
    · intro v
      simpa only [first,LayerGeometry.fromPrimitives_unitPrimitive] using hg₁ v
    · intro v
      simpa only [second,LayerGeometry.fromPrimitives_unitPrimitive] using hg₂ v
  · intro v
    rw [hsupport]
    exact (havoid v).mono_right Finset.subset_union_left

end
end EndpointRouter
