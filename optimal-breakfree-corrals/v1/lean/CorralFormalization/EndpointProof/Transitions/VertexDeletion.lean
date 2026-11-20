import CorralFormalization.EndpointProof.Transitions.PippengerRounding

/-! The weighted-degree cost of deleting actual vertices from a linear
hypergraph.  The exceptional vertices themselves are not counted twice. -/

open scoped Classical BigOperators

namespace EndpointTransitions

noncomputable section

open EndpointMatching.Fractional.Rounding

variable {V E : Type*} [Fintype V] [Fintype E]

def weightedLoad (edges : E → Finset V) (w : E → ℝ) (v : V) : ℝ :=
  ∑ e, if v ∈ edges e then w e else 0

def prunedWeight (edges : E → Finset V) (w : E → ℝ) (B : Finset V) (e : E) : ℝ :=
  if Disjoint (edges e) B then w e else 0

def lostEdges (edges : E → Finset V) (B : Finset V) (v : V) : Finset E :=
  Finset.univ.filter (fun e => v ∈ edges e ∧ ¬ Disjoint (edges e) B)

/-- At an undeleted vertex, distinct lost edges meet the deleted vertex
set in disjoint nonempty sets.  Thus at most `|B|` incident edges are lost. -/
theorem lostEdges_card_le (edges : E → Finset V) (hlinear : IsLinear edges)
    (B : Finset V) (v : V) (hv : v ∉ B) : (lostEdges edges B v).card ≤ B.card := by
  have hnonempty (e : E) (he : e ∈ lostEdges edges B v) : (edges e ∩ B).Nonempty := by
    have he' := (Finset.mem_filter.mp he).2
    obtain ⟨x, hx, hxB⟩ := Finset.not_disjoint_iff.mp he'.2
    exact ⟨x, Finset.mem_inter.mpr ⟨hx,hxB⟩⟩
  have hdis : (lostEdges edges B v : Set E).PairwiseDisjoint (fun e => edges e ∩ B) := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro x hxe hxf
    have hve := ((Finset.mem_filter.mp he).2).1
    have hvf := ((Finset.mem_filter.mp hf).2).1
    have hxe' := Finset.mem_inter.mp hxe
    have hxf' := Finset.mem_inter.mp hxf
    have hident := Finset.card_le_one.mp (hlinear e f hef)
      v (Finset.mem_inter.mpr ⟨hve,hvf⟩)
      x (Finset.mem_inter.mpr ⟨hxe'.1,hxf'.1⟩)
    exact hv (hident.symm ▸ hxe'.2)
  calc
    (lostEdges edges B v).card = ∑ _e ∈ lostEdges edges B v, (1 : ℕ) := by simp
    _ ≤ ∑ e ∈ lostEdges edges B v, (edges e ∩ B).card := by
      apply Finset.sum_le_sum
      intro e he
      exact Finset.one_le_card.mpr (hnonempty e he)
    _ = ((lostEdges edges B v).biUnion (fun e => edges e ∩ B)).card :=
      (Finset.card_biUnion hdis).symm
    _ ≤ B.card := Finset.card_le_card (by
      intro x hx
      obtain ⟨e, _, hxe⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hxe).2)

theorem weightedLoad_pruning_identity (edges : E → Finset V) (w : E → ℝ)
    (B : Finset V) (v : V) :
    weightedLoad edges w v-weightedLoad edges (prunedWeight edges w B) v =
      ∑ e ∈ lostEdges edges B v, w e := by
  rw [weightedLoad, weightedLoad, ← Finset.sum_sub_distrib]
  simp only [lostEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hve : v ∈ edges e <;> by_cases heB : Disjoint (edges e) B <;>
    simp [prunedWeight, hve, heB]

/-- ordinary transition lemma's post-deletion weighted-degree loss.  This is deterministic and
holds for any later deleted vertex set. -/
theorem weightedLoad_pruning_bound (edges : E → Finset V) (hlinear : IsLinear edges)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1)
    (B : Finset V) (v : V) (hv : v ∉ B) :
    |weightedLoad edges (prunedWeight edges w B) v-weightedLoad edges w v| ≤ B.card := by
  rw [abs_sub_comm, weightedLoad_pruning_identity]
  have hnonneg : 0 ≤ ∑ e ∈ lostEdges edges B v, w e :=
    Finset.sum_nonneg (fun e _ => (hw e).1)
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ ∑ _e ∈ lostEdges edges B v, (1 : ℝ) := Finset.sum_le_sum (fun e _ => (hw e).2)
    _ = ((lostEdges edges B v).card : ℝ) := by simp
    _ ≤ B.card := by exact_mod_cast lostEdges_card_le edges hlinear B v hv

end
end EndpointTransitions
