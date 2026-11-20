import CorralFormalization.EndpointProof.Matching.Fractional.ActualReindexBan
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.RawEstimates

open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.RobustWeights
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Number of later banned actual edges incident to a particular tagged
vertex, whether or not those banned edges lie in the current target. -/
def actualBannedDegree (F : Finset (Finset (Vertex G))) (v : Vertex G) : ℕ :=
  (F.filter (fun E => v ∈ E)).card

/-- The concrete banned full-edge indices incident to a chart vertex inject
into the actual later ban at that vertex. -/
theorem indexed_banned_degree_le_actual (W : Finset (Vertex G)) (hW : Balanced W)
    (F : Finset (Finset (Vertex G))) (v : W) :
    familyDegree (allowedEdgeIndex W hW ∅) (forbiddenEdgeIndices W F) (balancedChart W hW v) ≤
      actualBannedDegree F v.val := by
  let S := (forbiddenEdgeIndices W F).filter
    (fun e => (balancedChart W hW v).2 = allowedEdgeIndex W hW ∅ e (balancedChart W hW v).1)
  have hsub : S.image actualEdge ⊆ F.filter (fun E => v.val ∈ E) := by
    intro E hE
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hE
    have heF : e ∈ forbiddenEdgeIndices W F := (Finset.mem_filter.mp he).1
    have hban : actualEdge e ∈ F := by simpa [forbiddenEdgeIndices] using heF
    have hi := (Finset.mem_filter.mp he).2
    have hv : v ∈ localEdge e := (allowedEdgeIndex_mem W hW ∅ e v).2 hi
    exact Finset.mem_filter.mpr ⟨hban,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩
  change S.card ≤ (F.filter (fun E => v.val ∈ E)).card
  calc
    S.card = (S.image actualEdge).card := (Finset.card_image_of_injective _ (actualEdge_injective W ∅)).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Quantitative robust matrix estimates on the correctly reindexed *actual*
target imply actual interval-bounded perfect weights on its actual allowed
edge family. The displayed Gram and norm inequalities remain explicit analytic
premises; there is no fractional or integral matching premise. -/
theorem actual_interval_weights_of_raw_matrix_estimates
    (W : Finset (Vertex G)) (hW : Balanced W) [Nonempty (CommonIndex W)]
    (F : Finset (Finset (Vertex G))) (d X : ℝ) (hd : 0 < d) (hX : X ≤ 2*d)
    (diagError editError rawError : Matrix (Fin 3 × CommonIndex W) (Fin 3 × CommonIndex W) ℝ)
    (hdecomp : gram (allowedEdgeIndex W hW ∅) = idealGram d + (diagError + editError) + rawError)
    (hdiag : ‖diagError‖ ≤ 3*X/10000) (hedit : ‖editError‖ ≤ X/10000)
    (hraw : ‖rawError‖ ≤ 5*X)
    (hsquare : ‖normalizeError d rawError * normalizeError d rawError‖ ≤ 33/100000)
    (hdegree : ∀ v, |(familyDegree (allowedEdgeIndex W hW ∅) Finset.univ v : ℝ) - d| ≤ 3*X/10000)
    (hban : ∀ v : W, (actualBannedDegree F v.val : ℝ) ≤ X/2000) :
    ∃ w : AllowedEdge W F → ℝ, (∀ e, 1/(2*d) ≤ w e ∧ w e ≤ 3/(2*d)) ∧
      ∀ v : W, (∑ e, if v ∈ localEdge e then w e else 0) = 1 := by
  have hban' : ∀ v : Fin 3 × CommonIndex W,
      (familyDegree (allowedEdgeIndex W hW ∅) (forbiddenEdgeIndices W F) v : ℝ) ≤ X/2000 := by
    intro v
    let u : W := (balancedChart W hW).symm v
    have hindex := indexed_banned_degree_le_actual W hW F u
    have hindex' : (familyDegree (allowedEdgeIndex W hW ∅) (forbiddenEdgeIndices W F)
      (balancedChart W hW u) : ℝ) ≤ actualBannedDegree F u.val := by exact_mod_cast hindex
    have hu : balancedChart W hW u = v := Equiv.apply_symm_apply (balancedChart W hW) v
    rw [hu] at hindex'
    exact hindex'.trans (hban u)
  obtain ⟨w,hw,hload⟩ := exists_robust_weights_of_unscaled_errors
    (allowedEdgeIndex W hW ∅) d X hd hX diagError editError rawError
    hdecomp hdiag hedit hraw hsquare hdegree (forbiddenEdgeIndices W F) hban'
  exact retained_weights_transport W hW F (fun x => 1/(2*d) ≤ x ∧ x ≤ 3/(2*d)) w hw hload

/-- The same actual weights also satisfy the integer cap used by the
quantitative AKS matching bridge. -/
theorem actual_fractionalPerfect_of_raw_matrix_estimates
    (W : Finset (Vertex G)) (hW : Balanced W) [Nonempty (CommonIndex W)]
    (F : Finset (Finset (Vertex G))) (d X : ℝ) (hd : 0 < d) (hX : X ≤ 2*d)
    (Dnat : ℕ) (hD0 : 0 < Dnat) (hD : (Dnat : ℝ) ≤ 2*d/3)
    (diagError editError rawError : Matrix (Fin 3 × CommonIndex W) (Fin 3 × CommonIndex W) ℝ)
    (hdecomp : gram (allowedEdgeIndex W hW ∅) = idealGram d + (diagError + editError) + rawError)
    (hdiag : ‖diagError‖ ≤ 3*X/10000) (hedit : ‖editError‖ ≤ X/10000)
    (hraw : ‖rawError‖ ≤ 5*X)
    (hsquare : ‖normalizeError d rawError * normalizeError d rawError‖ ≤ 33/100000)
    (hdegree : ∀ v, |(familyDegree (allowedEdgeIndex W hW ∅) Finset.univ v : ℝ) - d| ≤ 3*X/10000)
    (hban : ∀ v : W, (actualBannedDegree F v.val : ℝ) ≤ X/2000) :
    FractionalPerfect W F Dnat := by
  obtain ⟨w,hw,hload⟩ := actual_interval_weights_of_raw_matrix_estimates
    W hW F d X hd hX diagError editError rawError hdecomp hdiag hedit hraw hsquare hdegree hban
  have hcap := positive_weights_meet_integer_cap d Dnat hd hD0 hD
  refine ⟨w, ?_, hload⟩
  intro e
  exact ⟨le_trans (by positivity : 0 ≤ 1/(2*d)) (hw e).1, (hw e).2.trans hcap⟩

end
end EndpointMatching.UniversalCore
