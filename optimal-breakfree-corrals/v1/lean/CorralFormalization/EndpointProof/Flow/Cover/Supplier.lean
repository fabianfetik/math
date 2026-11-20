import CorralFormalization.EndpointProof.Flow.Cover.Partition

/-!
# Exact six-root supplier contract for the paired-cover iteration

The contract is conditional.  It demands a genuine matching, actual Q
membership and complete numerical inverse support freshness; it does not
assert that such a supplier has already been constructed.
-/

open scoped Classical BigOperators

namespace EndpointFlow.Cover

open EndpointSelector EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- Concrete output of one legal six-root query. -/
structure SixRootOutput (Q : Vertex G → Prop)
    (O X : Finset (Vertex G)) (F : Finset G) where
  added : Finset (Vertex G)
  output : Finset (Vertex G)
  added_Q : ∀ v ∈ added, Q v
  added_paired : ∀ v ∈ added, (v.1,-v.2) ∈ added
  added_nonzero : ∀ v ∈ added, v.2 ≠ 0
  added_balanced : Balanced added
  added_card_le : added.card ≤ 18
  output_subset : output ⊆ added
  output_onePerPart : OnePerPart output
  roots_fresh : Disjoint (numericalSupport added) (numericalSupport (O ∪ X))
  avoids : Disjoint (numericalSupport added) F
  matching : MatchingOn (((O ∪ X) ∪ added) \ output)

/-- One common Q supplier, before every later pair of disjoint nonzero
one-per-part input triples and every later numerical forbidden support. -/
def SixRootSupplier (Q : Vertex G → Prop) (budget : ℕ) : Prop :=
  ∀ (O X : Finset (Vertex G)) (F : Finset G),
    OnePerPart O → OnePerPart X → Disjoint O X →
    (∀ v ∈ O, v.2 ≠ 0) → (∀ v ∈ X, v.2 ≠ 0) → F.card ≤ budget →
    Nonempty (SixRootOutput Q O X F)

/-- A supplied gadget has exactly the coordinate-sum law required for iteration.
It follows from its actual matching and pairing, rather than an extra premise. -/
theorem SixRootOutput.output_coordinate_sum (hodd : Odd (Fintype.card G))
    {Q : Vertex G → Prop} {O X : Finset (Vertex G)} {F : Finset G}
    (A : SixRootOutput Q O X F) :
    (∑ v ∈ A.output, v.2) = ∑ v ∈ O ∪ X, v.2 := by
  let P : PartialCover Q (O ∪ X) := {
    added := A.added
    output := A.output
    added_Q := A.added_Q
    added_paired := A.added_paired
    added_nonzero := A.added_nonzero
    original_added_disjoint := (disjoint_of_numericalSupport A.roots_fresh).symm
    output_subset := A.output_subset.trans Finset.subset_union_right
    matching := A.matching }
  exact P.output_coordinate_sum hodd

end
end EndpointFlow.Cover
