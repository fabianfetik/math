import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PermutationExistenceUnion
import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PermutationExistenceNumerics

/-!
# Existence of the degree-16 robust selection graph

This completes the elementary random-permutation construction in Lemma E.T
for every `s ≥ 1`. Every probability estimate is supplied by a proved finite
count, and both expansion conditions are conclusions. The slightly weaker
numerical estimate `81/101 < 1` replaces `7/11 < 1` without changing any graph
parameters.
-/

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence

noncomputable section

theorem smallExpansionFailure_probability_le_geometric (s : ℕ) (hs : 0 < s) :
    uniformProbability (smallExpansionFailure s) ≤
      ∑ a ∈ Finset.Icc 1 s, (27 / 128 : ℝ) ^ a := by
  apply (smallExpansionFailure_probability_le s hs).trans
  apply Finset.sum_le_sum
  intro a ha
  exact left_binomial_geometric_bound s a (Finset.mem_Icc.mp ha).1
    (Finset.mem_Icc.mp ha).2

theorem rightExpansionFailure_probability_le_geometric (s : ℕ) (hs : 0 < s) :
    uniformProbability (rightExpansionFailure s) ≤
      2 * ∑ b ∈ Finset.Icc 1 (2 * s), (27 / 128 : ℝ) ^ b := by
  apply (rightExpansionFailure_probability_le s hs).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  exact right_binomial_geometric_bound s b (Finset.mem_Icc.mp hb).1
    (Finset.mem_Icc.mp hb).2

/-- A uniform bound for either expansion failure, on one common finite
sample space and for every positive block size. -/
theorem expansion_failure_probability_le (s : ℕ) (hs : 0 < s) :
    uniformProbability (fun σ : PermutationFamily s =>
      smallExpansionFailure s σ ∨ rightExpansionFailure s σ) ≤ 81 / 101 := by
  calc
    _ ≤ uniformProbability (smallExpansionFailure s) +
        uniformProbability (rightExpansionFailure s) := uniformProbability_or_le _ _
    _ ≤ (∑ a ∈ Finset.Icc 1 s, (27 / 128 : ℝ) ^ a) +
        2 * ∑ b ∈ Finset.Icc 1 (2 * s), (27 / 128 : ℝ) ^ b :=
      add_le_add (smallExpansionFailure_probability_le_geometric s hs)
        (rightExpansionFailure_probability_le_geometric s hs)
    _ ≤ 27 / 101 + 2 * (27 / 101 : ℝ) :=
      add_le_add (geometric_Icc_bound s)
        (mul_le_mul_of_nonneg_left (geometric_Icc_bound (2 * s)) (by norm_num))
    _ = _ := by norm_num

/-- The two graph expansions are supplied unconditionally by the finite
probabilistic construction; they are not hypotheses of this theorem. -/
theorem exists_good_permutation_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ σ : PermutationFamily s,
      (∀ A : Finset (Fin (3 * s)), A.card ≤ s →
        A.card ≤ ((A.biUnion (permutationNeighbors s σ)) ∩ fixedPorts s).card) ∧
      (∀ B : Finset (Fin (4 * s)), B.card ≤ 2 * s →
        B.card ≤ (rightNeighbors (permutationNeighbors s σ) B).card) := by
  have hfailure : uniformProbability (fun σ : PermutationFamily s =>
      smallExpansionFailure s σ ∨ rightExpansionFailure s σ) < 1 :=
    (expansion_failure_probability_le s (by omega)).trans_lt (by norm_num)
  obtain ⟨σ, hσ⟩ := exists_not_of_uniformProbability_lt_one _ hfailure
  refine ⟨σ, ?_, ?_⟩
  · intro A hA
    by_contra hbad
    exact hσ (Or.inl ⟨A, hA, by omega⟩)
  · intro B hB
    by_contra hbad
    exact hσ (Or.inr ⟨B, hB, by omega⟩)

/-- Lemma E.T at the exact interface consumed by the selector compiler:
there is a robust selection graph of left degree at most 16 for every s≥1. -/
theorem selectionGraph_nonempty (s : ℕ) (hs : 1 ≤ s) :
    Nonempty (ContiguousSelectionGraph s 16) := by
  obtain ⟨σ, hsmall, hright⟩ := exists_good_permutation_family s hs
  exact ⟨graph_of_good_permutations s hs σ hsmall hright⟩

/-- The same robust graph also has right degree at most twelve, so its
maximum degree across both sides is at most sixteen. -/
theorem exists_selectionGraph_with_right_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ graph : ContiguousSelectionGraph s 16,
      ∀ w : Fin (4 * s), (rightNeighbors graph.neighbors {w}).card ≤ 12 := by
  obtain ⟨σ, hsmall, hright⟩ := exists_good_permutation_family s hs
  refine ⟨graph_of_good_permutations s hs σ hsmall hright, ?_⟩
  exact permutationNeighbors_right_degree s σ

/-- A deterministic choice preserving both left and right degree bounds. -/
def selectionGraph (s : ℕ) (hs : 1 ≤ s) : ContiguousSelectionGraph s 16 :=
  Classical.choose (exists_selectionGraph_with_right_degree s hs)

theorem selectionGraph_right_degree (s : ℕ) (hs : 1 ≤ s) (w : Fin (4 * s)) :
    (rightNeighbors (selectionGraph s hs).neighbors {w}).card ≤ 12 :=
  Classical.choose_spec (exists_selectionGraph_with_right_degree s hs) w

end

end EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence
