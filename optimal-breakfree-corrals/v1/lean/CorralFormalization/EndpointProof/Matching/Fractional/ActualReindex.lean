import CorralFormalization.EndpointProof.Matching.Fractional.BalancedChart
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Canonical
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Correction

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.RobustWeights
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [Fintype G] in
theorem hyperedge_exists_each_part (E : Finset (Vertex G)) (hE : Hyperedge E) (p : Fin 3) :
    ∃ g : G, (p,g) ∈ E := by
  obtain ⟨x,y,z,_,rfl⟩ := hE
  fin_cases p
  · exact ⟨x, by simp⟩
  · exact ⟨y, by simp⟩
  · exact ⟨z, by simp⟩

omit [Fintype G] in
/-- Each actual allowed edge contains precisely one local vertex per role. -/
theorem allowedEdge_onePerPart {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (e : AllowedEdge W F) (p : Fin 3) :
    ∃! v : W, v ∈ localEdge e ∧ v.val.1 = p := by
  obtain ⟨g,hg⟩ := hyperedge_exists_each_part (actualEdge e) (actualEdge_valid e) p
  obtain ⟨w,hw,hweq⟩ := Finset.mem_image.mp hg
  have hwrole : w.val.1 = p := congrArg Prod.fst hweq
  refine ⟨w,⟨hw,hwrole⟩,?_⟩
  intro v ⟨hv,hvrole⟩
  have hvE : v.val ∈ actualEdge e := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have hwE : w.val ∈ actualEdge e := Finset.mem_image.mpr ⟨w,hw,rfl⟩
  have hvEq : v.val = (p,v.val.2) := Prod.ext hvrole rfl
  have hwEq : w.val = (p,w.val.2) := Prod.ext hwrole rfl
  have hgEq := hyperedge_same_role_unique (actualEdge_valid e) (hvEq ▸ hvE) (hwEq ▸ hwE)
  apply Subtype.ext
  exact Prod.ext (hvrole.trans hwrole.symm) hgEq

/-- The matrix proof's common-index representation of an actual allowed edge. -/
def allowedEdgeIndex (W : Finset (Vertex G)) (hW : Balanced W)
    (F : Finset (Finset (Vertex G))) (e : AllowedEdge W F) (p : Fin 3) : CommonIndex W :=
  (balancedChart W hW (Classical.choose (allowedEdge_onePerPart e p))).2

theorem allowedEdgeIndex_mem (W : Finset (Vertex G)) (hW : Balanced W)
    (F : Finset (Finset (Vertex G))) (e : AllowedEdge W F) (v : W) :
    v ∈ localEdge e ↔ (balancedChart W hW v).2 =
      allowedEdgeIndex W hW F e (balancedChart W hW v).1 := by
  let p := v.val.1
  let w : W := Classical.choose (allowedEdge_onePerPart e p)
  have hw : w ∈ localEdge e ∧ w.val.1 = p := (Classical.choose_spec (allowedEdge_onePerPart e p)).1
  have hu : ∀ y : W, y ∈ localEdge e ∧ y.val.1 = p → y = w :=
    (Classical.choose_spec (allowedEdge_onePerPart e p)).2
  have hpart : (balancedChart W hW v).1 = p := balancedChart_part W hW v
  have hwpart : (balancedChart W hW w).1 = p := (balancedChart_part W hW w).trans hw.2
  constructor
  · intro hv
    have hvw : v = w := hu v ⟨hv,rfl⟩
    rw [hvw]
    change (balancedChart W hW w).2 = (balancedChart W hW
      (Classical.choose (allowedEdge_onePerPart e ((balancedChart W hW w).1)))).2
    rw [hwpart]
  · intro hv
    have hv' : (balancedChart W hW v).2 = (balancedChart W hW w).2 := by
      simpa [allowedEdgeIndex, hpart, p, w] using hv
    have hvw : v = w := (balancedChart W hW).injective (Prod.ext (hpart.trans hwpart.symm) hv')
    simpa [hvw] using hw.1

/-- Full membership equivalence: no vertices or edges are added in transport. -/
theorem allowedEdge_chart_membership (W : Finset (Vertex G)) (hW : Balanced W)
    (F : Finset (Finset (Vertex G))) (e : AllowedEdge W F) (v : W) :
    v ∈ localEdge e ↔ balancedChart W hW v ∈ edgeSet (allowedEdgeIndex W hW F) e := by
  rw [mem_edgeSet]
  exact allowedEdgeIndex_mem W hW F e v

/-- Reindexing transports an actual unit-load certificate without changing
any edge weight or its numerical bounds. -/
theorem fractionalPerfect_of_reindexed_weights (W : Finset (Vertex G)) (hW : Balanced W)
    (F : Finset (Finset (Vertex G))) (D : ℕ) (w : AllowedEdge W F → ℝ)
    (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ))
    (hload : ∀ v : Fin 3 × CommonIndex W,
      (∑ e, if v ∈ edgeSet (allowedEdgeIndex W hW F) e then w e else 0) = 1) :
    FractionalPerfect W F D := by
  refine ⟨w,hw,?_⟩
  intro v
  have h := hload (balancedChart W hW v)
  simpa only [← allowedEdge_chart_membership] using h

end
end EndpointMatching.UniversalCore
