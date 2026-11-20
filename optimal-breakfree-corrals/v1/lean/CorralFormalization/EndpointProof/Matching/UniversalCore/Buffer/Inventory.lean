import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.Sections
import CorralFormalization.EndpointProof.Matching.UniversalCore.PairedCoverInventory

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore.Buffer
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The three actual inverse-pair labels contributed by one buffer. -/
def pick (t : Parameters G) (i : Fin 3) : Finset (Vertex G) :=
  pairOf (i,coordinate t i)

omit [Fintype G] in
theorem coordinate_sum_zero (t : Parameters G) :
    coordinate t 0 + coordinate t 1 + coordinate t 2 = 0 := by
  rcases t with ⟨u,v⟩
  simp [coordinate]

/-- A valid buffer has the two actual zero-sum matching edges used by the
universal core, not merely an abstract support count. -/
theorem matching_of_valid (hodd : Odd (Fintype.card G))
    (t : Parameters G) (hv : GeometricallyValid t) :
    Nonempty (Matching (Finset.univ.biUnion (pick t))) := by
  have h0 : coordinate t 0 ≠ -coordinate t 0 := ne_neg_of_odd hodd (hv.1 0)
  have h1 : coordinate t 1 ≠ -coordinate t 1 := ne_neg_of_odd hodd (hv.1 1)
  have h2 : coordinate t 2 ≠ -coordinate t 2 := ne_neg_of_odd hodd (hv.1 2)
  apply matching_of_buffer_triple (pick t) (coordinate t 0) (coordinate t 1) (coordinate t 2)
    h0 h1 h2 (coordinate_sum_zero t)
  all_goals rfl

omit [Fintype G] in
theorem positive_coordinate_mem_support (t : Parameters G) (i : Fin 3) :
    coordinate t i ∈ pairSupport t := by
  exact Finset.mem_image.mpr ⟨(i,false),Finset.mem_univ _,rfl⟩

omit [Fintype G] in
theorem negative_coordinate_mem_support (t : Parameters G) (i : Fin 3) :
    -coordinate t i ∈ pairSupport t := by
  exact Finset.mem_image.mpr ⟨(i,true),Finset.mem_univ _,rfl⟩

/-- Every pair of a Q-successful buffer avoiding U belongs to the exact
Q-pair inventory installed in the existing sampled-core construction. -/
theorem pick_mem_availablePairInventory (Q : Vertex G → Prop) (U : Finset G)
    (t : Parameters G) (ht : t ∈ goodCandidates Q) (havoid : Disjoint (pairSupport t) U)
    (i : Fin 3) : pick t i ∈ availablePairInventory Q U i := by
  have hlabels := (Finset.mem_filter.mp ht).2
  have hpos : coordinate t i ∉ U := by
    intro hU
    exact Finset.disjoint_left.mp havoid (positive_coordinate_mem_support t i) hU
  have hneg : -coordinate t i ∉ U := by
    intro hU
    exact Finset.disjoint_left.mp havoid (negative_coordinate_mem_support t i) hU
  exact Finset.mem_image.mpr ⟨coordinate t i,Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hlabels i,hpos,hneg⟩,rfl⟩

omit [Fintype G] in
theorem pick_eq_implies_support_intersection (t u : Parameters G) (i j : Fin 3)
    (heq : pick t i = pick u j) :
    ∃ x : G, x ∈ pairSupport t ∧ x ∈ pairSupport u := by
  refine ⟨coordinate t i,positive_coordinate_mem_support t i,?_⟩
  have hmem : (i,coordinate t i) ∈ pick u j := by
    rw [← heq]
    simp [pick,pairOf]
  simp only [pick,pairOf,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hmem
  rcases hmem with ⟨hij,hcoord⟩ | ⟨hij,hcoord⟩
  · rw [hcoord]
    exact positive_coordinate_mem_support u j
  · rw [hcoord]
    exact negative_coordinate_mem_support u j

omit [Fintype G] in
theorem disjoint_support_picks_ne (t u : Parameters G)
    (hdis : Disjoint (pairSupport t) (pairSupport u)) (i j : Fin 3) : pick t i ≠ pick u j := by
  intro heq
  obtain ⟨x,hx,hy⟩ := pick_eq_implies_support_intersection t u i j heq
  exact Finset.disjoint_left.mp hdis hx hy

end
end EndpointMatching.UniversalCore.Buffer
