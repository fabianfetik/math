import CorralFormalization.EndpointProof.Matching.Fractional.ActualReindex

open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.RobustWeights
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

abbrev FullAllowedEdge (W : Finset (Vertex G)) := AllowedEdge W ∅

def forbiddenEdgeIndices (W : Finset (Vertex G)) (F : Finset (Finset (Vertex G))) :
    Finset (FullAllowedEdge W) :=
  Finset.univ.filter (fun e => actualEdge e ∈ F)

abbrev RetainedFullEdge (W : Finset (Vertex G)) (F : Finset (Finset (Vertex G))) :=
  ↥((Finset.univ : Finset (FullAllowedEdge W)) \ forbiddenEdgeIndices W F)

/-- Removing the indexed forbidden edges is exactly the same family as the
actual allowed-edge type; all underlying tagged vertices are unchanged. -/
def retainedEquivAllowed (W : Finset (Vertex G)) (F : Finset (Finset (Vertex G))) :
    RetainedFullEdge W F ≃ AllowedEdge W F where
  toFun e := ⟨e.val.val, e.val.property.1, by
    change actualEdge e.val ∉ F
    have hn := (Finset.mem_sdiff.mp e.property).2
    simpa [forbiddenEdgeIndices] using hn⟩
  invFun e := ⟨⟨e.val, e.property.1, by simp⟩, by
    have he : actualEdge (⟨e.val, e.property.1, by simp⟩ : FullAllowedEdge W) ∉ F := by
      exact actualEdge_allowed e
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simpa [forbiddenEdgeIndices] using he⟩⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/-- Weight and vertex incidence are identical after restricting the actual
edge set by a later ban. -/
theorem retained_chart_membership (W : Finset (Vertex G)) (hW : Balanced W)
    (F : Finset (Finset (Vertex G))) (e : RetainedFullEdge W F) (v : W) :
    v ∈ localEdge (retainedEquivAllowed W F e) ↔
      balancedChart W hW v ∈ edgeSet
        (fun z : RetainedFullEdge W F => allowedEdgeIndex W hW ∅ z.val) e := by
  rw [mem_edgeSet]
  change v ∈ localEdge e.val ↔ (balancedChart W hW v).2 =
    allowedEdgeIndex W hW ∅ e.val (balancedChart W hW v).1
  exact allowedEdgeIndex_mem W hW ∅ e.val v

/-- Exact transfer of every retained-edge weight, any pointwise weight
condition, and every vertex-load equation to the actual allowed edges. -/
theorem retained_weights_transport (W : Finset (Vertex G)) (hW : Balanced W)
    (F : Finset (Finset (Vertex G))) (P : ℝ → Prop) (w : RetainedFullEdge W F → ℝ)
    (hw : ∀ e, P (w e))
    (hload : ∀ v : Fin 3 × CommonIndex W,
      (∑ e : RetainedFullEdge W F, if v ∈ edgeSet
        (fun z : RetainedFullEdge W F => allowedEdgeIndex W hW ∅ z.val) e then w e else 0) = 1) :
    ∃ w' : AllowedEdge W F → ℝ, (∀ e, P (w' e)) ∧
      ∀ v : W, (∑ e, if v ∈ localEdge e then w' e else 0) = 1 := by
  let equiv := retainedEquivAllowed W F
  refine ⟨fun e => w (equiv.symm e), fun e => hw (equiv.symm e), ?_⟩
  intro v
  have h := hload (balancedChart W hW v)
  have hsum : (∑ e : RetainedFullEdge W F, if balancedChart W hW v ∈ edgeSet
      (fun z : RetainedFullEdge W F => allowedEdgeIndex W hW ∅ z.val) e then w e else 0) =
      ∑ e : AllowedEdge W F, if v ∈ localEdge e then w (equiv.symm e) else 0 := by
    apply Fintype.sum_equiv equiv
    intro e
    have hm := retained_chart_membership W hW F e v
    simp only [← hm, Equiv.symm_apply_apply]
    rfl
  rw [hsum] at h
  exact h

/-- The transport in the integer-cap convention consumed by AKS rounding. -/
theorem fractionalPerfect_of_retained_weights (W : Finset (Vertex G)) (hW : Balanced W)
    (F : Finset (Finset (Vertex G))) (D : ℕ) (w : RetainedFullEdge W F → ℝ)
    (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ))
    (hload : ∀ v : Fin 3 × CommonIndex W,
      (∑ e : RetainedFullEdge W F, if v ∈ edgeSet
        (fun z : RetainedFullEdge W F => allowedEdgeIndex W hW ∅ z.val) e then w e else 0) = 1) :
    FractionalPerfect W F D :=
  retained_weights_transport W hW F (fun x => 0 ≤ x ∧ x ≤ 1 / (D : ℝ)) w hw hload

/-- The inverse-problem supplier's real upper weight 3/(2d) meets the
integer degree convention 1/D whenever 0<D≤2d/3. -/
theorem positive_weights_meet_integer_cap (d : ℝ) (D : ℕ) (hd : 0 < d)
    (hD0 : 0 < D) (hD : (D : ℝ) ≤ 2*d/3) :
    3/(2*d) ≤ 1/(D : ℝ) := by
  apply (div_le_div_iff₀ (by positivity : 0 < 2*d) (by exact_mod_cast hD0)).2
  nlinarith

end
end EndpointMatching.UniversalCore
