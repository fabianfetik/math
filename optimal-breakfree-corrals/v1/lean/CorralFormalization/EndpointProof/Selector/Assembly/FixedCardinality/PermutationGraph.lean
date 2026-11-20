import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.Expansion
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Classical BigOperators
namespace EndpointSelector.FixedCardinality.GraphExpansion
noncomputable section

/-- The E.T graph, merging repeated edges of four blockwise permutations. -/
def permutationNeighbors (s : ℕ)
    (σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s))
    (i : Fin (3 * s)) : Finset (Fin (4 * s)) :=
  let left := (finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s)).symm i
  Finset.univ.biUnion (fun b : Fin 4 =>
    Finset.univ.image (fun k : Fin 4 =>
      (finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)) (b, σ left.1 b k left.2)))

/-- Each left vertex has at most 4·4 neighbors. -/
theorem permutationNeighbors_left_degree (s : ℕ)
    (σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s)) (i : Fin (3 * s)) :
    (permutationNeighbors s σ i).card ≤ 16 := by
  classical
  unfold permutationNeighbors
  calc
    _ ≤ ∑ b : Fin 4, (Finset.univ.image (fun k : Fin 4 =>
        (finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s))
          (b, σ ((finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s)).symm i).1 b k
             ((finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s)).symm i).2))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _b : Fin 4, 4 := by
      apply Finset.sum_le_sum
      intro b _
      exact Finset.card_image_le.trans (by simp)
    _ = 16 := by norm_num

/-- The reverse neighbors are among three blocks times four inverse maps. -/
def inverseNeighborCandidates (s : ℕ)
    (σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s))
    (w : Fin (4 * s)) : Finset (Fin (3 * s)) :=
  let right := (finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)).symm w
  Finset.univ.biUnion (fun a : Fin 3 =>
    Finset.univ.image (fun k : Fin 4 =>
      (finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s))
        (a, (σ a right.1 k).symm right.2)))

theorem inverseNeighborCandidates_card (s : ℕ)
    (σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s)) (w : Fin (4 * s)) :
    (inverseNeighborCandidates s σ w).card ≤ 12 := by
  classical
  unfold inverseNeighborCandidates
  calc
    _ ≤ ∑ a : Fin 3, (Finset.univ.image (fun k : Fin 4 =>
      (finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s))
        (a, (σ a ((finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)).symm w).1 k).symm
          ((finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)).symm w).2))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a : Fin 3, 4 := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.card_image_le.trans (by simp)
    _ = 12 := by norm_num

theorem permutationNeighbors_right_degree (s : ℕ)
    (σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s)) (w : Fin (4 * s)) :
    (rightNeighbors (permutationNeighbors s σ) {w}).card ≤ 12 := by
  classical
  apply (Finset.card_le_card ?_).trans (inverseNeighborCandidates_card s σ w)
  intro i hi
  obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hi).2
  have hzw : z = w := Finset.mem_singleton.mp (Finset.mem_inter.mp hz).2
  subst z
  have hw : w ∈ permutationNeighbors s σ i := (Finset.mem_inter.mp hz).1
  let left := (finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s)).symm i
  let right := (finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)).symm w
  change w ∈ Finset.univ.biUnion (fun b : Fin 4 =>
    Finset.univ.image (fun k : Fin 4 =>
      (finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)) (b, σ left.1 b k left.2))) at hw
  obtain ⟨b, _, k, _, hwb⟩ := by simpa only [Finset.mem_biUnion, Finset.mem_image] using hw
  have hpair : (b, σ left.1 b k left.2) = right := by
    have h := congrArg (finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)).symm hwb
    simpa only [Equiv.symm_apply_apply] using h
  have hb : b = right.1 := congrArg Prod.fst hpair
  have hv : σ left.1 b k left.2 = right.2 := congrArg Prod.snd hpair
  subst b
  have hv' : left.2 = (σ left.1 right.1 k).symm right.2 := by
    apply (σ left.1 right.1 k).injective
    simpa using hv
  change i ∈ Finset.univ.biUnion (fun a : Fin 3 =>
    Finset.univ.image (fun k : Fin 4 =>
      (finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s))
        (a, (σ a right.1 k).symm right.2)))
  apply Finset.mem_biUnion.mpr
  refine ⟨left.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩⟩
  rw [← hv']
  exact (Equiv.apply_symm_apply (finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s)) i)

/-- The final numerical geometric-series bound in (T5). This arithmetic
identity does not establish the preceding estimates of the bad events. -/
theorem expansion_union_bound_arithmetic :
    (3 : ℝ) * (∑' j : ℕ, (7 / 40 : ℝ) ^ (j + 1)) = 7 / 11 ∧
      (7 / 11 : ℝ) < 1 := by
  constructor
  · have h : (∑' j : ℕ, (7 / 40 : ℝ) ^ (j + 1)) =
        (7 / 40 : ℝ) * (∑' j : ℕ, (7 / 40 : ℝ) ^ j) := by
      simp_rw [pow_succ']
      rw [tsum_mul_left]
    rw [h, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  · norm_num

/-- An E.T permutation family satisfying the two stated expansions gives
an actual robust selection graph; existence of such a family is separate. -/
def graph_of_good_permutations (s : ℕ) (hs : 1 ≤ s)
    (σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s))
    (hsmall : ∀ A : Finset (Fin (3 * s)), A.card ≤ s →
      A.card ≤ ((A.biUnion (permutationNeighbors s σ)) ∩ fixedPorts s).card)
    (hright : ∀ B : Finset (Fin (4 * s)), B.card ≤ 2 * s →
      B.card ≤ (rightNeighbors (permutationNeighbors s σ) B).card) :
    ContiguousSelectionGraph s 16 :=
  contiguousGraph_of_expansion s 16 hs (permutationNeighbors s σ)
    (permutationNeighbors_left_degree s σ) hsmall hright

end
end EndpointSelector.FixedCardinality.GraphExpansion
