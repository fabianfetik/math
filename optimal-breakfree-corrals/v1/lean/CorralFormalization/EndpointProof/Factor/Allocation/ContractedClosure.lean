import CorralFormalization.EndpointProof.Factor.Allocation.FinalSettings
import CorralFormalization.EndpointProof.Factor.RouterAttachment.Closing

/-!
# The actual one-cycle contracted closure

The fixed router, attached paths and exact matching produce a single cycle
on track indices. The physical expansion and cutting of virtual edges are
still separate from this declaration.
-/

open scoped Classical BigOperators
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointRouter EndpointFactor.OrdinaryFragments
open EndpointFactor.RouterAttachment EndpointMatching.AbsorptionAssembly
open Equiv Equiv.Perm
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
variable {dist : Densities m} {sample : AugmentedSample G m}
variable {W D X Y : Finset G} {ℓ w d : ℕ}

def Family.endEquiv (F : Family G) : F.Index ≃ F.ends :=
  Equiv.ofBijective (fun i => ⟨F.last i, (F.mem_ends _).mpr ⟨i, rfl⟩⟩) (by
    constructor
    · intro i j hij
      exact F.last_injective (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := (F.mem_ends x.val).mp x.property
      exact ⟨i, Subtype.ext hi⟩)

/-- Follow the ordinary path beginning at the given fixed router output,
then enumerate its actual end in the attached family. -/
def preparedEndAtOutput (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y) : Fin ℓ ≃ O.after.ends :=
  (RouterAttachment.PhysicalRouter.outputKeyEquiv P.router O.after
    (RouterAttachment.outcome_starts P A hLayer O)).trans (Family.endEquiv O.after)

structure ContractedClosure
    (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y) where
  matching : PhysicalDifferenceMatching (O.after.ends \ Y) (P.special 0 \ X)
    (remainingBank P.bank O.joins P.ordinaryPool A.colors)
  virtual : Y ≃ X
  full : O.after.ends ≃ P.special 0
  closing : Perm (Fin ℓ)
  closing_link : ∀ i, P.router.input (closing i) =
    (full (preparedEndAtOutput P A hLayer O i)).val
  virtual_link : ∀ y : O.after.ends, ∀ hy : y.val ∈ Y,
    (full y).val = (virtual ⟨y.val, hy⟩).val
  real_link : ∀ y : O.after.ends, ∀ hy : y.val ∉ Y,
    (matching.color ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩).val =
      (full y).val-y.val
  firstOn : List (Fin ℓ × Fin ℓ)
  secondOn : List (Fin ℓ × Fin ℓ)
  first_valid : firstOn.Sublist (firstLayer ℓ)
  second_valid : secondOn.Sublist (secondLayer ℓ)
  one_cycle : (closing * (switchProduct secondOn * switchProduct firstOn)).IsCycleOn Set.univ
  router_endpoints : ∀ i,
    (installedRoutes P.router.first P.router.second firstOn secondOn i).first = P.router.input i ∧
    (installedRoutes P.router.first P.router.second firstOn secondOn i).last =
      P.router.output ((switchProduct secondOn * switchProduct firstOn) i)

/-- The actual prepared target, original checksum, and common-sample exact-matching
produce the matching, virtual links and one-cycle track permutation. -/
theorem exists_contractedClosure
    (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (hColors : ∀ i, A.color i ⊆ P.ordinaryColour i)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y)
    (hE : ExactMatchingEvent dist (forgetAugmented sample))
    (hXYcard : X.card = Y.card) (hDcard : D.card+X.card = W.card)
    (hDzero : (0 : G) ∉ D)
    (hchecksum : (∑ c ∈ D, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x)
    (hedit : (physicalEditDistance (vertexSet (forgetAugmented sample) (lastVertex m))
      (vertexSet (forgetAugmented sample) (firstVertex m))
      (colourSet (forgetAugmented sample) (specialColour m))
      (O.after.ends \ Y) (P.special 0 \ X)
      (remainingBank P.bank O.joins P.ordinaryPool A.colors) : ℝ) ≤
        explicitDelta dist.q*Fintype.card G) :
    Nonempty (ContractedClosure P A hLayer O) := by
  obtain ⟨M⟩ := RouterAttachment.exactClosing_of_prepared P A hLayer hColors O
    hE hXYcard hDcard hDzero hchecksum hedit
  obtain ⟨virtual, full, closing, hlink, hvirtual, hreal, a, b, ha, hb, hcycle, hends⟩ :=
    P.router.choose_settings_after_matching O.after.ends Y X
      (remainingBank P.bank O.joins P.ordinaryPool A.colors)
      O.prescribed_ends P.starts_in_special hXYcard (preparedEndAtOutput P A hLayer O) M
  exact ⟨{
    matching := M
    virtual := virtual
    full := full
    closing := closing
    closing_link := hlink
    virtual_link := hvirtual
    real_link := hreal
    firstOn := a
    secondOn := b
    first_valid := ha
    second_valid := hb
    one_cycle := hcycle
    router_endpoints := hends }⟩

end
end EndpointFactor.Allocation
