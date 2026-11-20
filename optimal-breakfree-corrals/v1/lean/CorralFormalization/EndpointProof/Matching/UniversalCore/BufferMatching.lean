import CorralFormalization.EndpointProof.Matching.UniversalCore.PairInventory
open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- A single zero-sum edge is a matching on itself. -/
def oneEdgeMatching (E : Finset (Vertex G)) (hE : Hyperedge E) : Matching E where
  edges := {E}
  valid := by
    intro T hT
    have hT' : T = E := Finset.mem_singleton.mp hT
    subst T
    exact hE
  disjoint := by simp
  cover := by simp

/-- A zero-sum triple and its inverse give a matching on the three inverse
pairs used as an absorber buffer. The non-self-inverse inputs hold in odd order. -/
theorem zeroSum_buffer_matching (a b c : G)
    (ha : a ≠ -a) (hb : b ≠ -b) (hc : c ≠ -c) (hzero : a + b + c = 0) :
    Nonempty (Matching
      ({(0,a),(0,-a)} ∪ {(1,b),(1,-b)} ∪ {(2,c),(2,-c)})) := by
  let E : Finset (Vertex G) := {(0,a),(1,b),(2,c)}
  let F : Finset (Vertex G) := {(0,-a),(1,-b),(2,-c)}
  have hE : Hyperedge E := ⟨a,b,c,hzero,rfl⟩
  have hF : Hyperedge F := ⟨-a,-b,-c,by rw [← neg_add, ← neg_add, hzero, neg_zero],rfl⟩
  have hd : Disjoint E F := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;>
      simp [F, Prod.mk.injEq, ha, hb, hc] at hw
  let M := unionMatching (oneEdgeMatching E hE) (oneEdgeMatching F hF) hd
  have hvertices : E ∪ F =
      ({(0,a),(0,-a)} ∪ {(1,b),(1,-b)} ∪ {(2,c),(2,-c)} : Finset (Vertex G)) := by
    ext v
    simp only [E, F, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  exact ⟨hvertices ▸ M⟩

/-- The concrete triple supplies the matching required by the universal
core assembly, after identifying its three pair labels. -/
theorem matching_of_buffer_triple (pick : Fin 3 → Finset (Vertex G))
    (a b c : G) (ha : a ≠ -a) (hb : b ≠ -b) (hc : c ≠ -c)
    (hzero : a + b + c = 0)
    (h0 : pick 0 = {(0,a),(0,-a)})
    (h1 : pick 1 = {(1,b),(1,-b)})
    (h2 : pick 2 = {(2,c),(2,-c)}) :
    Nonempty (Matching (Finset.univ.biUnion pick)) := by
  have heq : Finset.univ.biUnion pick = pick 0 ∪ pick 1 ∪ pick 2 := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨p, hp⟩
      fin_cases p <;> simp_all
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  rw [heq, h0, h1, h2]
  exact zeroSum_buffer_matching a b c ha hb hc hzero

end
end EndpointMatching.UniversalCore
