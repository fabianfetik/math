import CorralFormalization.EndpointProof.Factor.RouterAttachment.Prepared
import CorralFormalization.EndpointProof.Factor.Allocation.ExactClosing

/-!
# exact-matching receives the constructed router-prepended physical family

The router setting is still free. Empty settings supply an actual family
for the checksum receiver, and the proved fixed inventories show that its
closing target is independent of that provisional setting.
-/

open scoped Classical BigOperators
namespace EndpointFactor.RouterAttachment
open OrdinaryFragments Allocation EndpointRouter EndpointLayeredSample
open EndpointMatching.AbsorptionAssembly
noncomputable section
universe u
variable {G : Type u} [Fintype G] [AddCommGroup G]
variable {m ℓ w d : ℕ} {dist : Densities m} {sample : AugmentedSample G m}
variable {W D X Y : Finset G}

/-- The exact closing matching follows from the actual prepared and
attached data, original target checksum/cardinality, and proved edit ledger.
There is no assumed physical family, endpoint disjointness or residual
checksum in this statement. -/
theorem exactClosing_of_prepared
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
    Nonempty (PhysicalDifferenceMatching (O.after.ends \ Y) (P.special 0 \ X)
      (remainingBank P.bank O.joins P.ordinaryPool A.colors)) := by
  let F := preparedFamily P A hLayer hColors O [] [] (List.nil_sublist _) (List.nil_sublist _)
  exact P.exactClosing_of_physical_family A O F hE
    (preparedFamily_vertices P A hLayer hColors O [] [] (List.nil_sublist _) (List.nil_sublist _))
    (preparedFamily_starts P A hLayer hColors O [] [] (List.nil_sublist _) (List.nil_sublist _))
    (preparedFamily_ends P A hLayer hColors O [] [] (List.nil_sublist _) (List.nil_sublist _))
    (preparedFamily_colors P A hLayer hColors O [] [] (List.nil_sublist _) (List.nil_sublist _))
    (closing_endpoints_disjoint P A hLayer O) hXYcard hDcard hDzero hchecksum hedit

end
end EndpointFactor.RouterAttachment
