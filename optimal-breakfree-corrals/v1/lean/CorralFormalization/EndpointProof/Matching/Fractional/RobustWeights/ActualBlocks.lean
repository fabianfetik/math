import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Blocks
import CorralFormalization.EndpointProof.Matching.Fractional.ActualReindex

/-!
# Actual target block matrices

The coordinates are read from the inverse balanced chart of the actual
tagged target.  The edge type is the canonical set of all actual target
hyperedges.  No parallel surrogate hypergraph is introduced.
-/

open scoped Classical BigOperators Matrix Matrix.Norms.Operator symmDiff

namespace EndpointMatching.Fractional.RobustWeights

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore EndpointMatching.Fractional.ActualRemainder
open EndpointFractionalRawEvent
noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G]

def completedTriple (v u : Vertex G) : Finset (Vertex G) :=
  {v, u, (thirdRole v.1 u.1, -(v.2 + u.2))}

theorem completedTriple_hyperedge (v u : Vertex G) (hrole : v.1 ≠ u.1) :
    Hyperedge (completedTriple v u) := by
  rcases v with ⟨r, a⟩
  rcases u with ⟨s, b⟩
  fin_cases r <;> fin_cases s <;> simp only [ne_eq] at hrole
  all_goals first | contradiction | skip
  · exact ⟨a, b, -(a + b), by abel, by simp [completedTriple, thirdRole]⟩
  · exact ⟨a, -(a + b), b, by abel, by ext x; simp [completedTriple, thirdRole] <;> tauto⟩
  · exact ⟨b, a, -(a + b), by abel, by ext x; simp [completedTriple, thirdRole] <;> tauto⟩
  · exact ⟨-(a + b), a, b, by abel, by ext x; simp [completedTriple, thirdRole] <;> tauto⟩
  · exact ⟨b, -(a + b), a, by abel, by ext x; simp [completedTriple, thirdRole] <;> tauto⟩
  · exact ⟨-(a + b), b, a, by abel, by ext x; simp [completedTriple, thirdRole] <;> tauto⟩

theorem hyperedge_eq_completedTriple {H : Finset (Vertex G)} (hH : Hyperedge H)
    (v u : Vertex G) (hv : v ∈ H) (hu : u ∈ H) (hrole : v.1 ≠ u.1) :
    H = completedTriple v u := by
  by_contra hne
  have hlin := hyperedge_inter_card_le_one hH (completedTriple_hyperedge v u hrole) hne
  have hv' : v ∈ H ∩ completedTriple v u := Finset.mem_inter.mpr ⟨hv, by simp [completedTriple]⟩
  have hu' : u ∈ H ∩ completedTriple v u := Finset.mem_inter.mpr ⟨hu, by simp [completedTriple]⟩
  exact hrole (congrArg Prod.fst (Finset.card_le_one.mp hlin v hv' u hu'))

def actualCoordinate (W : Finset (Vertex G)) (hW : Balanced W)
    (v : Fin 3 × CommonIndex W) : G := ((balancedChart W hW).symm v).val.2

@[simp] theorem actualChart_part (W : Finset (Vertex G)) (hW : Balanced W)
    (v : Fin 3 × CommonIndex W) : ((balancedChart W hW).symm v).val.1 = v.1 := by
  rcases v with ⟨r,i⟩
  exact balancedChart_symm_part W hW r i

def signedCoordinateSet (W : Finset (Vertex G)) (r : Fin 3) : Finset G :=
  (slice W r).image Prod.snd

theorem signedCoordinateSet_mem (W : Finset (Vertex G)) (r : Fin 3) (g : G) :
    g ∈ signedCoordinateSet W r ↔ (r,g) ∈ W := by
  simp only [signedCoordinateSet, Finset.mem_image, slice, Finset.mem_filter]
  constructor
  · rintro ⟨⟨s,a⟩, ⟨hw,hr⟩, hcoord⟩
    simp only [Prod.fst, Prod.snd] at hr hcoord
    subst s
    subst a
    exact hw
  · intro h
    exact ⟨(r,g), ⟨h,rfl⟩, rfl⟩

theorem actualCoordinate_injective (W : Finset (Vertex G)) (hW : Balanced W) (r : Fin 3) :
    Function.Injective (fun i => actualCoordinate W hW (r,i)) := by
  intro i j hij
  have hv : ((balancedChart W hW).symm (r,i)).val = ((balancedChart W hW).symm (r,j)).val := by
    apply Prod.ext
    · simp
    · exact hij
  have heq : (r,i) = (r,j) := (balancedChart W hW).symm.injective (Subtype.ext hv)
  exact congrArg Prod.snd heq

theorem exists_actual_edge_of_completion (W : Finset (Vertex G)) (v u : W)
    (hrole : v.val.1 ≠ u.val.1)
    (hcomp : (thirdRole v.val.1 u.val.1, -(v.val.2 + u.val.2)) ∈ W) :
    ∃ e : AllowedEdge W ∅, v ∈ localEdge e ∧ u ∈ localEdge e := by
  let H := completedTriple v.val u.val
  have hH : H ⊆ W := by
    intro z hz
    simp only [H, completedTriple, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact v.property
    · exact u.property
    · exact hcomp
  let L : Finset W := Finset.univ.filter (fun z => z.val ∈ H)
  have himage : L.image (fun z : W => z.val) = H := by
    ext z
    constructor
    · rintro hz
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hw).2
    · intro hz
      exact Finset.mem_image.mpr ⟨⟨z,hH hz⟩, by simp [L,hz], rfl⟩
  let e : AllowedEdge W ∅ := ⟨L, by rw [himage]; exact ⟨completedTriple_hyperedge _ _ hrole, by simp⟩⟩
  refine ⟨e, ?_, ?_⟩ <;> simp [e, localEdge, L, H, completedTriple]

theorem actual_common_edge_unique (W : Finset (Vertex G)) (v u : W)
    (hrole : v.val.1 ≠ u.val.1) (e f : AllowedEdge W ∅)
    (hev : v ∈ localEdge e) (heu : u ∈ localEdge e)
    (hfv : v ∈ localEdge f) (hfu : u ∈ localEdge f) : e = f := by
  apply actualEdge_injective W ∅
  rw [hyperedge_eq_completedTriple (actualEdge_valid e) v.val u.val
      (Finset.mem_image.mpr ⟨v,hev,rfl⟩) (Finset.mem_image.mpr ⟨u,heu,rfl⟩) hrole,
    hyperedge_eq_completedTriple (actualEdge_valid f) v.val u.val
      (Finset.mem_image.mpr ⟨v,hfv,rfl⟩) (Finset.mem_image.mpr ⟨u,hfu,rfl⟩) hrole]

/-- The actual unbanned pair codegree is the third-role membership bit. -/
theorem actual_pair_sum (W : Finset (Vertex G)) (v u : W)
    (hrole : v.val.1 ≠ u.val.1) :
    (∑ e : AllowedEdge W ∅, if v ∈ localEdge e ∧ u ∈ localEdge e then (1 : ℝ) else 0) =
      setBit (signedCoordinateSet W (thirdRole v.val.1 u.val.1)) (-(v.val.2 + u.val.2)) := by
  by_cases hc : (thirdRole v.val.1 u.val.1, -(v.val.2 + u.val.2)) ∈ W
  · obtain ⟨e, hev, heu⟩ := exists_actual_edge_of_completion W v u hrole hc
    have hbit : setBit (signedCoordinateSet W (thirdRole v.val.1 u.val.1))
        (-(v.val.2 + u.val.2)) = 1 := by
      exact if_pos ((signedCoordinateSet_mem _ _ _).mpr hc)
    rw [hbit, Finset.sum_eq_single e]
    · simp [hev, heu]
    · intro f _ hfe
      by_cases hf : v ∈ localEdge f ∧ u ∈ localEdge f
      · exact (hfe (actual_common_edge_unique W v u hrole f e hf.1 hf.2 hev heu)).elim
      · simp [hf]
    · simp
  · have hbit : setBit (signedCoordinateSet W (thirdRole v.val.1 u.val.1))
        (-(v.val.2 + u.val.2)) = 0 := by
      exact if_neg (fun h => hc ((signedCoordinateSet_mem _ _ _).mp h))
    rw [hbit]
    apply Finset.sum_eq_zero
    intro e _
    have hnot : ¬(v ∈ localEdge e ∧ u ∈ localEdge e) := by
      rintro ⟨hev, heu⟩
      have hshape := hyperedge_eq_completedTriple (actualEdge_valid e) v.val u.val
        (Finset.mem_image.mpr ⟨v,hev,rfl⟩) (Finset.mem_image.mpr ⟨u,heu,rfl⟩) hrole
      apply hc
      apply actualEdge_inside e
      rw [hshape]
      simp [completedTriple]
    simp [hnot]

theorem actual_incidence_apply (W : Finset (Vertex G)) (hW : Balanced W)
    (v : Fin 3 × CommonIndex W) (e : AllowedEdge W ∅) :
    incidence (allowedEdgeIndex W hW ∅) v e =
      if (balancedChart W hW).symm v ∈ localEdge e then 1 else 0 := by
  have hm := allowedEdgeIndex_mem W hW ∅ e ((balancedChart W hW).symm v)
  simp only [Equiv.apply_symm_apply] at hm
  exact if_congr hm.symm rfl rfl

/-- The canonical edge type gives the actual off-diagonal Gram blocks
without a pair-codegree premise. -/
theorem actual_gram_cross (W : Finset (Vertex G)) (hW : Balanced W)
    (v u : Fin 3 × CommonIndex W) (hrole : v.1 ≠ u.1) :
    gram (allowedEdgeIndex W hW ∅) v u =
      setBit (signedCoordinateSet W (thirdRole v.1 u.1))
        (requiredCoordinate (actualCoordinate W hW) v u) := by
  have hrole' : ((balancedChart W hW).symm v).val.1 ≠
      ((balancedChart W hW).symm u).val.1 := by simpa using hrole
  calc
    gram (allowedEdgeIndex W hW ∅) v u =
        ∑ e : AllowedEdge W ∅, if (balancedChart W hW).symm v ∈ localEdge e ∧
          (balancedChart W hW).symm u ∈ localEdge e then (1 : ℝ) else 0 := by
      simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, actual_incidence_apply]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hv : (balancedChart W hW).symm v ∈ localEdge e <;>
        by_cases hu : (balancedChart W hW).symm u ∈ localEdge e <;> simp [hv, hu]
    _ = _ := by
      simpa only [actualChart_part, actualCoordinate, requiredCoordinate] using
        actual_pair_sum W ((balancedChart W hW).symm v) ((balancedChart W hW).symm u) hrole'

def actualDegreeMatrix (W : Finset (Vertex G)) (hW : Balanced W) (d : ℝ) :=
  degreeDiagonal (allowedEdgeIndex W hW ∅) d

def actualEditMatrix (W : Finset (Vertex G)) (hW : Balanced W) (R : Fin 3 → Finset G) :=
  editMatrix (actualCoordinate W hW) (signedCoordinateSet W) R

def actualRawMatrix (W : Finset (Vertex G)) (hW : Balanced W) (R : Fin 3 → Finset G) (q : ℝ) :=
  offDiagonal (actualCoordinate W hW) R q

/-- Constructive actual `M = ideal + D + Ed + N₀`, with no structural or
weight supplier premise.  Raw masks, later edits and actual degrees remain
separate named matrices. -/
theorem actual_gram_decomposition (W : Finset (Vertex G)) (hW : Balanced W)
    [Nonempty (CommonIndex W)] (R : Fin 3 → Finset G) (q : ℝ) :
    gram (allowedEdgeIndex W hW ∅) = idealGram (q * (Fintype.card (CommonIndex W) : ℝ)) +
      (actualDegreeMatrix W hW (q * (Fintype.card (CommonIndex W) : ℝ)) +
        actualEditMatrix W hW R) + actualRawMatrix W hW R q := by
  exact gram_eq_ideal_add_degree_edit_raw _ _ _ _ _ (actual_gram_cross W hW)

/-- The true membership edits pay only their signed inventory distance. -/
theorem actualEditMatrix_norm_le (W : Finset (Vertex G)) (hW : Balanced W)
    (R : Fin 3 → Finset G) :
    ‖actualEditMatrix W hW R‖ ≤ editDistance (signedCoordinateSet W) R :=
  editMatrix_norm_le _ (actualCoordinate_injective W hW) _ _

end
end EndpointMatching.Fractional.RobustWeights
