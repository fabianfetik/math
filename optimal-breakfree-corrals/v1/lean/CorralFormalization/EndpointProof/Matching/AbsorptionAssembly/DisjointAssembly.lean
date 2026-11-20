import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.FiniteAssembly

/-!
Finite assembly of actual tagged zero-sum matchings. These lemmas assemble
already supplied local matchings; they do not prove the selection graph,
local supplier, or fixed-cardinality compiler.
-/

open scoped Classical BigOperators

namespace EndpointMatching.AbsorptionAssembly
open EndpointFlow.AbelianTransport
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- Finite disjoint unions of actual zero-sum matchings. -/
theorem matching_biUnion {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (V : ι → Finset (Vertex G))
    (hdis : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → Disjoint (V i) (V j))
    (hmatch : ∀ i ∈ D, Nonempty (Matching (V i))) :
    Nonempty (Matching (D.biUnion V)) := by
  classical
  revert hdis hmatch
  induction D using Finset.induction_on with
  | empty =>
      intro _ _
      simpa using (show Nonempty (Matching (∅ : Finset (Vertex G))) from
      ⟨emptyMatching⟩)
  | @insert i D hi ih =>
      intro hdis hmatch
      obtain ⟨Mi⟩ := hmatch i (Finset.mem_insert_self _ _)
      have hDdis : ∀ j ∈ D, ∀ k ∈ D, j ≠ k → Disjoint (V j) (V k) := by
        intro j hj k hk hne
        exact hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
      have hDmatch : ∀ j ∈ D, Nonempty (Matching (V j)) := by
        intro j hj
        exact hmatch j (Finset.mem_insert_of_mem hj)
      obtain ⟨MD⟩ := ih hDdis hDmatch
      have hid : Disjoint (V i) (D.biUnion V) := by
        apply Finset.disjoint_left.mpr
        intro v hvi hvD
        obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvD
        have hij : i ≠ j := by
          intro he
          exact hi (he.symm ▸ hj)
        exact Finset.disjoint_left.mp
          (hdis i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hij) hvi hvj
      exact ⟨by simpa only [Finset.biUnion_insert] using unionMatching Mi MD hid⟩

/-- A concrete route chooses one pair at each installed slot. This lemma
unions the actual local matchings, retaining the exact vertex inventory. -/
theorem assemble_slots {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (I T : ι → Finset (Vertex G))
    (hII : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → Disjoint (I i) (I j))
    (hIT : ∀ i ∈ D, ∀ j ∈ D, Disjoint (I i) (T j))
    (hTT : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → Disjoint (T i) (T j))
    (hmatch : ∀ i ∈ D, Nonempty (Matching (I i ∪ T i))) :
    Nonempty (Matching ((D.biUnion I) ∪ D.biUnion T)) := by
  classical
  have hdis : ∀ i ∈ D, ∀ j ∈ D, i ≠ j →
      Disjoint (I i ∪ T i) (I j ∪ T j) := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    rcases Finset.mem_union.mp hv with hv | hv <;>
      rcases Finset.mem_union.mp hv' with hv' | hv'
    · exact Finset.disjoint_left.mp (hII i hi j hj hne) hv hv'
    · exact Finset.disjoint_left.mp (hIT i hi j hj) hv hv'
    · exact Finset.disjoint_left.mp (hIT j hj i hi) hv' hv
    · exact Finset.disjoint_left.mp (hTT i hi j hj hne) hv hv'
  have hset : D.biUnion (fun i => I i ∪ T i) =
      (D.biUnion I) ∪ D.biUnion T := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_union]
    aesop
  rw [← hset]
  exact matching_biUnion D (fun i => I i ∪ T i) hdis hmatch

end
end EndpointMatching.AbsorptionAssembly
