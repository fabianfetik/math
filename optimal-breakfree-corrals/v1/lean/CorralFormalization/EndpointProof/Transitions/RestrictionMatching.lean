import CorralFormalization.EndpointProof.Transitions.VertexDeletion

/-! Restriction to actual surviving vertices, with no virtual vertices and
with all matching and uncovered-cardinality translations proved. -/

open scoped Classical BigOperators

namespace EndpointTransitions

noncomputable section

open EndpointMatching.Fractional.Rounding

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

def restrictedEdge (edges : E → Finset V) (W : Finset V) (e : E) : Finset W :=
  (edges e).subtype (fun v => v ∈ W)

@[simp] theorem mem_restrictedEdge (edges : E → Finset V) (W : Finset V)
    (e : E) (v : W) : v ∈ restrictedEdge edges W e ↔ v.val ∈ edges e := by
  exact Finset.mem_subtype

theorem restrictedEdge_card_le (edges : E → Finset V) (W : Finset V) (e : E) :
    (restrictedEdge edges W e).card ≤ (edges e).card := by
  rw [restrictedEdge,Finset.card_subtype]
  exact Finset.card_filter_le _ _

theorem restrictedEdge_card_of_subset (edges : E → Finset V) (W : Finset V)
    (e : E) (he : edges e ⊆ W) : (restrictedEdge edges W e).card = (edges e).card := by
  rw [restrictedEdge,Finset.card_subtype]
  congr 1
  exact Finset.filter_true_of_mem (fun x hx => he hx)

theorem restrictedEdge_linear (edges : E → Finset V) (hlinear : IsLinear edges)
    (W : Finset V) : IsLinear (restrictedEdge edges W) := by
  intro e f hef
  apply Finset.card_le_one.mpr
  intro v hv w hw
  apply Subtype.ext
  exact Finset.card_le_one.mp (hlinear e f hef)
    v.val (by simpa only [Finset.mem_inter,mem_restrictedEdge] using hv)
    w.val (by simpa only [Finset.mem_inter,mem_restrictedEdge] using hw)

theorem restricted_weightedLoad (edges : E → Finset V) (W : Finset V)
    (w : E → ℝ) (v : W) :
    weightedLoad (restrictedEdge edges W) w v = weightedLoad edges w v.val := by
  unfold weightedLoad
  apply Finset.sum_congr rfl
  intro e _
  simp only [mem_restrictedEdge]

/-- Complete finite reduction from a genuine weighted hypergraph on the
target `T` to a matching after deleting actual exceptional vertices `B`.
The source is needed only for the actual surviving vertex subtype. -/
theorem weighted_matching_after_deletion (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (T B : Finset V) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1)
    (hsupported : ∀ e, 0 < w e → edges e ⊆ T)
    (μ ε D b : ℝ) (hμ : 0 < μ) (hμone : μ ≤ 1) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hwindow : 2*(b+(B.card : ℝ)+3) ≤ μ*(D-(b+(B.card : ℝ)+3)))
    (hcodegree : 1 < μ*(D-(b+(B.card : ℝ)+3)))
    (hload : ∀ v ∈ T, v ∉ B → |weightedLoad edges w v-D| ≤ b)
    (hsource : PippengerInput ↥(T \ B) μ ε) :
    ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
      (M.biUnion edges ⊆ T) ∧
      (T.card : ℝ)-3*(M.card : ℝ) ≤ (B.card : ℝ)+ε*(T.card : ℝ) := by
  let W := T \ B
  letI : DecidableEq W := Classical.decEq _
  let p := prunedWeight edges w B
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 := by
    intro e
    dsimp [p,prunedWeight]
    split_ifs <;> first | exact hw e | norm_num
  have hpos (e : E) (he : 0 < p e) : 0 < w e ∧ edges e ⊆ W := by
    have heB : Disjoint (edges e) B := by
      by_contra h
      simp [p,prunedWeight,h] at he
    have hew : 0 < w e := by simpa only [p,prunedWeight,if_pos heB] using he
    refine ⟨hew,?_⟩
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hsupported e hew hv, fun hvB =>
      Finset.disjoint_left.mp heB hv hvB⟩
  have hu : ∀ e, 0 < p e → (restrictedEdge edges W e).card = 3 := by
    intro e he
    rw [restrictedEdge_card_of_subset edges W e (hpos e he).2]
    exact huniform e
  have hload' (v : W) : |weightedLoad (restrictedEdge edges W) p v-D| ≤ b+B.card := by
    rw [restricted_weightedLoad]
    have hvT := (Finset.mem_sdiff.mp v.property).1
    have hvB := (Finset.mem_sdiff.mp v.property).2
    exact (abs_sub_le _ (weightedLoad edges w v.val) _).trans
      (add_le_add (weightedLoad_pruning_bound edges hlinear w hw B v.val hvB)
        (hload v.val hvT hvB) |>.trans_eq (add_comm _ _))
  obtain ⟨M,hM,hsupp,hrest⟩ := weighted_supported_near_perfect_matching
    (restrictedEdge edges W) (fun e => (restrictedEdge_card_le edges W e).trans (huniform e).le)
    p hp hu (restrictedEdge_linear edges hlinear W) μ ε D (b+B.card)
    hμ hμone (by positivity) (by simpa only [add_assoc] using hwindow)
    (by simpa only [add_assoc] using hcodegree) hload' hsource
  have hMS (e : E) (he : e ∈ M) : edges e ⊆ W := (hpos e (hsupp e he)).2
  have hMfull : IsMatching edges M := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    let vv : W := ⟨v,hMS e he hve⟩
    exact Finset.disjoint_left.mp (hM he hf hef)
      ((mem_restrictedEdge edges W e vv).mpr hve)
      ((mem_restrictedEdge edges W f vv).mpr hvf)
  have hcoverT : M.biUnion edges ⊆ T := by
    intro v hv
    obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_sdiff.mp (hMS e he hve)).1
  have hcovered : (M.biUnion (restrictedEdge edges W)).card = 3*M.card := by
    rw [Finset.card_biUnion hM]
    calc
      _ = ∑ _e ∈ M, (3 : ℕ) := Finset.sum_congr rfl (fun e he => hu e (hsupp e he))
      _ = _ := by simp [Nat.mul_comm]
  have hpartition : (uncovered (restrictedEdge edges W) M).card+3*M.card = W.card := by
    have hh := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (M.biUnion (restrictedEdge edges W)))
    simpa only [uncovered,hcovered,Finset.card_univ,Fintype.card_coe] using hh
  have hpartition' : ((uncovered (restrictedEdge edges W) M).card : ℝ)+3*(M.card : ℝ) = W.card := by
    exact_mod_cast hpartition
  have hrest' : ((uncovered (restrictedEdge edges W) M).card : ℝ) ≤ ε*(W.card : ℝ) := by
    simpa only [Fintype.card_coe] using hrest
  have hWle : (W.card : ℝ) ≤ T.card := by
    exact_mod_cast Finset.card_le_card (show W ⊆ T from Finset.sdiff_subset)
  have hdeleted : (T.card : ℝ) ≤ (W.card : ℝ)+(B.card : ℝ) := by
    have hcard := Finset.card_sdiff_add_card_inter T B
    have hinter := Finset.card_le_card (Finset.inter_subset_right (s₁ := T) (s₂ := B))
    have hnat : T.card ≤ W.card+B.card := by dsimp [W]; omega
    exact_mod_cast hnat
  refine ⟨M,hMfull,fun e he => (hpos e (hsupp e he)).1,hcoverT,?_⟩
  have heps := mul_le_mul_of_nonneg_left hWle hε
  linarith

end
end EndpointTransitions
