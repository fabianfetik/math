import CorralFormalization.EndpointProof.Factor.Allocation.UniformOrdinary

/-!
# Receiver for the actual prepared/attached family

Once the router-prepended physical family has the displayed inventories,
the existing exact matching theorem derives its checksum internally from
the original target checksum. This module does not construct that family.
-/

open scoped BigOperators Classical
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointMatching.AbsorptionAssembly
open EndpointFactor.OrdinaryFragments EndpointFactor.FragmentChecksum
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
variable {dist : Densities m} {sample : AugmentedSample G m}
variable {W D X Y : Finset G} {ℓ w d : ℕ}

theorem PreparedTarget.remainingBank_subset_target
    (P : PreparedTarget dist sample W D X Y ℓ w d) (A : LayerData G (m+1) ℓ)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y) :
    remainingBank P.bank O.joins P.ordinaryPool A.colors ⊆ D := by
  rw [O.remaining_exact]
  intro x hx
  have hp := (Finset.mem_sdiff.mp hx).1
  rcases Finset.mem_union.mp hp with hpool | hbank
  · exact P.ordinaryPool_subset hpool
  · exact P.bank_subset hbank

/-- The actual final physical matching, conditional only on the already
constructed router-prepended family satisfying its stated full inventories
and disjoint endpoints. No independent checksum or cardinality for the
matching target is assumed. -/
theorem PreparedTarget.exactClosing_of_physical_family
    (P : PreparedTarget dist sample W D X Y ℓ w d) (A : LayerData G (m+1) ℓ)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y) (F : Family G)
    (hE : ExactMatchingEvent dist (forgetAugmented sample))
    (hvertices : F.vertices = W) (hstarts : F.starts = P.special 0)
    (hends : F.ends = O.after.ends)
    (hcolors : F.colors = D \ remainingBank P.bank O.joins P.ordinaryPool A.colors)
    (hdisjoint : Disjoint (O.after.ends \ Y) (P.special 0 \ X))
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
  have hX : X ⊆ F.starts := by simpa [hstarts] using P.starts_in_special
  have hY : Y ⊆ F.ends := by simpa [hends] using O.prescribed_ends
  have hdisjoint' : Disjoint (F.ends \ Y) (F.starts \ X) := by
    simpa [hstarts, hends] using hdisjoint
  have hedit' : (physicalEditDistance (vertexSet (forgetAugmented sample) (lastVertex m))
      (vertexSet (forgetAugmented sample) (firstVertex m))
      (colourSet (forgetAugmented sample) (specialColour m))
      (F.ends \ Y) (F.starts \ X)
      (remainingBank P.bank O.joins P.ordinaryPool A.colors) : ℝ) ≤
        (1 / 10^6 : ℝ) * CorralFormalization.EndpointProof.RateBudget.SamplingConstants.kappa dist.q *
          Fintype.card G := by
    simpa [hstarts, hends, explicitDelta] using hedit
  have h := closingMatching_of_target_inventory hE F.lists W F.starts F.ends F.colors D X Y
    (remainingBank P.bank O.joins P.ordinaryPool A.colors) F.lists_nonempty F.lists_simple
    F.lists_rainbow (F.lists_vertices.trans hvertices) F.lists_starts F.lists_ends F.lists_colors
    hX hY (P.remainingBank_subset_target A O) hcolors hXYcard hDcard hdisjoint' hDzero hchecksum hedit'
  simpa [hstarts, hends] using h

end
end EndpointFactor.Allocation
