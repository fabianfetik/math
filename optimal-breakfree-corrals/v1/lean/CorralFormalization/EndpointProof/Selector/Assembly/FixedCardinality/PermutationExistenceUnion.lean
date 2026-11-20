import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PermutationExistenceGraphEvents

/-!
# Union bounds for failure of the two graph expansions

These bounds range over actual vertex subsets. The sample space remains the
48 independently uniform block permutations throughout.
-/

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence

noncomputable section

abbrev PermutationFamily (s : ℕ) := Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s)

def smallExpansionFailure (s : ℕ) (σ : PermutationFamily s) : Prop :=
  ∃ A : Finset (Fin (3 * s)), A.card ≤ s ∧
    ((A.biUnion (permutationNeighbors s σ)) ∩ fixedPorts s).card < A.card

def rightExpansionFailure (s : ℕ) (σ : PermutationFamily s) : Prop :=
  ∃ B : Finset (Fin (4 * s)), B.card ≤ 2 * s ∧
    (rightNeighbors (permutationNeighbors s σ) B).card < B.card

/-- The complete finite union bound preceding the binomial simplification
in (T3). No expansion or probabilistic estimate is an input hypothesis. -/
theorem smallExpansionFailure_probability_le (s : ℕ) (hs : 0 < s) :
    uniformProbability (smallExpansionFailure s) ≤
      ∑ a ∈ Finset.Icc 1 s,
        ((3 * s).choose a : ℝ) * (2 * s).choose (a - 1) *
          ((a : ℝ) / (2 * s)) ^ (8 * a) := by
  let E := fun (a : ℕ) (A : Finset (Fin (3 * s)))
      (T : Finset (Fin (4 * s))) (σ : PermutationFamily s) =>
    (A.biUnion (permutationNeighbors s σ)) ∩ fixedPorts s ⊆ T
  have hcover : ∀ σ, smallExpansionFailure s σ →
      ∃ a ∈ Finset.Icc 1 s,
        ∃ A ∈ (Finset.univ : Finset (Fin (3 * s))).powersetCard a,
          ∃ T ∈ (fixedPorts s).powersetCard (a - 1), E a A T σ := by
    intro σ hσ
    obtain ⟨A, hAs, hfail⟩ := hσ
    have ha : 1 ≤ A.card := by omega
    have hneed : A.card - 1 ≤ (fixedPorts s).card := by
      rw [fixedPorts_card]
      omega
    obtain ⟨T, hNT, hTF, hTcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.inter_subset_right :
        (A.biUnion (permutationNeighbors s σ)) ∩ fixedPorts s ⊆ fixedPorts s)
      (by omega : ((A.biUnion (permutationNeighbors s σ)) ∩ fixedPorts s).card ≤
        A.card - 1) hneed
    exact ⟨A.card, Finset.mem_Icc.mpr ⟨ha, hAs⟩, A,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩,
      T, Finset.mem_powersetCard.mpr ⟨hTF, hTcard⟩, hNT⟩
  calc
    _ ≤ uniformProbability (fun σ => ∃ a ∈ Finset.Icc 1 s,
        ∃ A ∈ (Finset.univ : Finset (Fin (3 * s))).powersetCard a,
          ∃ T ∈ (fixedPorts s).powersetCard (a - 1), E a A T σ) :=
      uniformProbability_mono _ _ hcover
    _ ≤ ∑ a ∈ Finset.Icc 1 s,
        uniformProbability (fun σ =>
          ∃ A ∈ (Finset.univ : Finset (Fin (3 * s))).powersetCard a,
            ∃ T ∈ (fixedPorts s).powersetCard (a - 1), E a A T σ) :=
      uniformProbability_exists_finset _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      have h := uniformProbability_double_exists_le
        ((Finset.univ : Finset (Fin (3 * s))).powersetCard a)
        ((fixedPorts s).powersetCard (a - 1)) (E a)
        (((a : ℝ) / (2 * s)) ^ (8 * a)) ?_
      · simpa only [Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin, fixedPorts_card] using h
      · intro A hA T hT
        obtain ⟨_, hAcard⟩ := Finset.mem_powersetCard.mp hA
        obtain ⟨hTF, hTcard⟩ := Finset.mem_powersetCard.mp hT
        have hTle : T.card ≤ A.card := by omega
        simpa only [E, hAcard] using left_fixed_graph_event_bound s hs A T hTF hTle

/-- The complete finite union bound preceding the binomial simplification
in (T4), on exactly the same sample space as the left failure. -/
theorem rightExpansionFailure_probability_le (s : ℕ) (hs : 0 < s) :
    uniformProbability (rightExpansionFailure s) ≤
      ∑ b ∈ Finset.Icc 1 (2 * s),
        ((4 * s).choose b : ℝ) * (3 * s).choose (b - 1) *
          ((b : ℝ) / (3 * s)) ^ (12 * b) := by
  let E := fun (_b : ℕ) (B : Finset (Fin (4 * s)))
      (A : Finset (Fin (3 * s))) (σ : PermutationFamily s) =>
    rightNeighbors (permutationNeighbors s σ) B ⊆ A
  have hcover : ∀ σ, rightExpansionFailure s σ →
      ∃ b ∈ Finset.Icc 1 (2 * s),
        ∃ B ∈ (Finset.univ : Finset (Fin (4 * s))).powersetCard b,
          ∃ A ∈ (Finset.univ : Finset (Fin (3 * s))).powersetCard (b - 1),
            E b B A σ := by
    intro σ hσ
    obtain ⟨B, hBs, hfail⟩ := hσ
    have hb : 1 ≤ B.card := by omega
    have hneed : B.card - 1 ≤ (Finset.univ : Finset (Fin (3 * s))).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨A, hNA, _, hAcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (rightNeighbors (permutationNeighbors s σ) B))
      (by omega : (rightNeighbors (permutationNeighbors s σ) B).card ≤ B.card - 1)
      hneed
    exact ⟨B.card, Finset.mem_Icc.mpr ⟨hb, hBs⟩, B,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩,
      A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAcard⟩, hNA⟩
  calc
    _ ≤ uniformProbability (fun σ => ∃ b ∈ Finset.Icc 1 (2 * s),
        ∃ B ∈ (Finset.univ : Finset (Fin (4 * s))).powersetCard b,
          ∃ A ∈ (Finset.univ : Finset (Fin (3 * s))).powersetCard (b - 1),
            E b B A σ) := uniformProbability_mono _ _ hcover
    _ ≤ ∑ b ∈ Finset.Icc 1 (2 * s), uniformProbability (fun σ =>
        ∃ B ∈ (Finset.univ : Finset (Fin (4 * s))).powersetCard b,
          ∃ A ∈ (Finset.univ : Finset (Fin (3 * s))).powersetCard (b - 1),
            E b B A σ) := uniformProbability_exists_finset _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b hb
      have h := uniformProbability_double_exists_le
        ((Finset.univ : Finset (Fin (4 * s))).powersetCard b)
        ((Finset.univ : Finset (Fin (3 * s))).powersetCard (b - 1)) (E b)
        (((b : ℝ) / (3 * s)) ^ (12 * b)) ?_
      · simpa only [Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin] using h
      · intro B hB A hA
        obtain ⟨_, hBcard⟩ := Finset.mem_powersetCard.mp hB
        obtain ⟨_, hAcard⟩ := Finset.mem_powersetCard.mp hA
        have hAle : A.card ≤ B.card := by omega
        simpa only [E, hBcard] using right_fixed_graph_event_bound s hs B A hAle

end

end EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence
