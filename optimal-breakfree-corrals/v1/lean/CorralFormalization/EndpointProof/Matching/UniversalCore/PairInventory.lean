import CorralFormalization.EndpointProof.Matching.UniversalCore.BufferSelection
import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.DisjointAssembly

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
noncomputable section

open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly

variable {G : Type*} [AddCommGroup G]

theorem legalPair_vertex_part {p : Fin 3} {T : Finset (Vertex G)}
    (hT : LegalPair p T) {v : Vertex G} (hv : v ∈ T) : v.1 = p := by
  obtain ⟨a, _, rfl⟩ := hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> rfl

theorem legalPairs_disjoint {p q : Fin 3} {T T' : Finset (Vertex G)}
    (hT : LegalPair p T) (hT' : LegalPair q T') (hne : T ≠ T') :
    Disjoint T T' := by
  by_cases hpq : p = q
  · subst q
    exact disjoint_of_support (legalPair_support_disjoint hT hT' hne)
  · apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact hpq ((legalPair_vertex_part hT hv).symm.trans (legalPair_vertex_part hT' hv'))

/-- Distinct tagged parts cannot share a legal inverse-pair label. -/
theorem legalPair_families_disjoint (Q : Fin 3 → Finset (Finset (Vertex G)))
    (hlegal : ∀ p T, T ∈ Q p → LegalPair p T) :
    ∀ p q, p ≠ q → Disjoint (Q p) (Q q) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro T hTp hTq
  obtain ⟨a, _, ha⟩ := hlegal p T hTp
  have hv : (p, a) ∈ T := by rw [ha]; simp
  have hpart := legalPair_vertex_part (hlegal q T hTq) hv
  exact hpq hpart

/-- Every selected buffer is matched, and distinct buffer pair labels
occupy disjoint actual tagged vertices. -/
theorem matching_of_selected_buffers {ι : Type*} [DecidableEq ι]
    (Q : Fin 3 → Finset (Finset (Vertex G)))
    (buffers : Finset ι) (pick : ι → Fin 3 → Finset (Vertex G))
    (hlegal : ∀ p T, T ∈ Q p → LegalPair p T)
    (hBmem : ∀ i ∈ buffers, ∀ p, pick i p ∈ Q p)
    (hunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hmatch : ∀ i ∈ buffers,
      Nonempty (Matching (Finset.univ.biUnion (pick i))))
    (C : Finset ι) (hC : C ⊆ buffers) :
    Nonempty (Matching ((bufferPairs C pick).biUnion id)) := by
  classical
  have hdis : ∀ i ∈ C, ∀ j ∈ C, i ≠ j →
      Disjoint (Finset.univ.biUnion (pick i)) (Finset.univ.biUnion (pick j)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨p, _, hvp⟩ := Finset.mem_biUnion.mp hvi
    obtain ⟨q, _, hvq⟩ := Finset.mem_biUnion.mp hvj
    have hp := hlegal p (pick i p) (hBmem i (hC hi) p)
    have hq := hlegal q (pick j q) (hBmem j (hC hj) q)
    exact Finset.disjoint_left.mp (legalPairs_disjoint hp hq
      (hunique i (hC hi) j (hC hj) hij p q)) hvp hvq
  obtain ⟨M⟩ := matching_biUnion C (fun i => Finset.univ.biUnion (pick i))
    hdis (fun i hi => hmatch i (hC hi))
  have hset : C.biUnion (fun i => Finset.univ.biUnion (pick i)) =
      (bufferPairs C pick).biUnion id := by
    ext v
    simp only [bufferPairs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    aesop
  exact ⟨hset ▸ M⟩

omit [AddCommGroup G] in
/-- The union of a subfamily of pairs from one part lies in the full Q
inventory. -/
theorem part_pairs_inside_all (Q : Fin 3 → Finset (Finset (Vertex G)))
    (p : Fin 3) {Y : Finset (Finset (Vertex G))} (hY : Y ⊆ Q p) :
    Y.biUnion id ⊆ (Finset.univ.biUnion Q).biUnion id := by
  intro v hv
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr
    ⟨T, Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hY hT⟩, hvT⟩

/-- Distinct legal pair labels have disjoint vertex sets, so disjoint
families of labels from Q have disjoint physical inventories. -/
theorem qpair_families_vertices_disjoint
    (Q : Fin 3 → Finset (Finset (Vertex G)))
    (hlegal : ∀ p T, T ∈ Q p → LegalPair p T)
    {A B : Finset (Finset (Vertex G))}
    (hA : A ⊆ Finset.univ.biUnion Q) (hB : B ⊆ Finset.univ.biUnion Q)
    (hAB : Disjoint A B) : Disjoint (A.biUnion id) (B.biUnion id) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvA hvB
  obtain ⟨T, hTA, hvT⟩ := Finset.mem_biUnion.mp hvA
  obtain ⟨T', hTB, hvT'⟩ := Finset.mem_biUnion.mp hvB
  obtain ⟨p, _, hTp⟩ := Finset.mem_biUnion.mp (hA hTA)
  obtain ⟨q, _, hTq⟩ := Finset.mem_biUnion.mp (hB hTB)
  have hne : T ≠ T' := by
    intro he
    subst T'
    exact Finset.disjoint_left.mp hAB hTA hTB
  exact Finset.disjoint_left.mp
    (legalPairs_disjoint (hlegal p T hTp) (hlegal q T' hTq) hne) hvT hvT'

/-- The exact physical vertex inventory fixed before any later residual. -/
def coreVertices (Q : Fin 3 → Finset (Finset (Vertex G)))
    (I : Fin 3 → Finset (Vertex G)) : Finset (Vertex G) :=
  (Finset.univ.biUnion I) ∪ (Finset.univ.biUnion Q).biUnion id
end
end EndpointMatching.UniversalCore
