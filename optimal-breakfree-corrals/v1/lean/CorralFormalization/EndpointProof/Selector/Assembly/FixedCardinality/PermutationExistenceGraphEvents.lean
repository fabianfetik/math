import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PermutationExistenceBlocks
import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PermutationGraph

/-!
# The permutation events are the actual graph events

The block predicates used by the probability estimates are equivalent to
containment of neighborhoods in the simple graph `permutationNeighbors`.
Merging repeated edges causes no change to these events.
-/

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence

noncomputable section

/-- Coordinates of a vertex subset in one of its equal-sized blocks. -/
def blockPart {q : ℕ} (s : ℕ) (S : Finset (Fin (q * s)))
    (a : Fin q) : Finset (Fin s) :=
  Finset.univ.filter (fun x =>
    (finProdFinEquiv : Fin q × Fin s ≃ Fin (q * s)) (a, x) ∈ S)

@[simp]
theorem mem_blockPart {q s : ℕ} {S : Finset (Fin (q * s))} {a : Fin q} {x : Fin s} :
    x ∈ blockPart s S a ↔
      (finProdFinEquiv : Fin q × Fin s ≃ Fin (q * s)) (a, x) ∈ S := by
  simp [blockPart]

/-- Block cardinalities partition the original vertex set, even for zero
block size or zero number of blocks. -/
theorem sum_card_blockPart {q : ℕ} (s : ℕ) (S : Finset (Fin (q * s))) :
    (∑ a, (blockPart s S a).card) = S.card := by
  let e := (finProdFinEquiv : Fin q × Fin s ≃ Fin (q * s))
  have hset : S = Finset.univ.biUnion (fun a : Fin q =>
      (blockPart s S a).image (fun x => e (a, x))) := by
    ext v
    constructor
    · intro hv
      refine Finset.mem_biUnion.mpr ⟨(e.symm v).1, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨(e.symm v).2, ?_, e.apply_symm_apply v⟩⟩
      apply mem_blockPart.mpr
      change e ((e.symm v).1, (e.symm v).2) ∈ S
      simpa only [Prod.eta, e.apply_symm_apply] using hv
    · intro hv
      obtain ⟨a, _, x, hx, rfl⟩ := by
        simpa only [Finset.mem_biUnion, Finset.mem_image] using hv
      exact mem_blockPart.mp hx
  have hdis : ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint
      (fun a => (blockPart s S a).image (fun x => e (a, x))) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro v hvA hvB
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hvA
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hvB
    exact hab (congrArg Prod.fst (e.injective (hx.trans hy.symm)))
  calc
    _ = ∑ a : Fin q, ((blockPart s S a).image (fun x => e (a, x))).card := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.card_image_of_injective]
      intro x y h
      exact congrArg Prod.snd (e.injective h)
    _ = (Finset.univ.biUnion (fun a : Fin q =>
          (blockPart s S a).image (fun x => e (a, x)))).card :=
      (Finset.card_biUnion hdis).symm
    _ = S.card := congrArg Finset.card hset.symm

/-- Containment of all graph neighbors is exactly simultaneous containment
under each of the block permutations. -/
theorem neighborhood_subset_iff_block_images (s : ℕ)
    (σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s))
    (A : Finset (Fin (3 * s))) (T : Finset (Fin (4 * s))) :
    A.biUnion (permutationNeighbors s σ) ⊆ T ↔
      ∀ a b k, (blockPart s A a).image (σ a b k) ⊆ blockPart s T b := by
  constructor
  · intro h a b k y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    apply mem_blockPart.mpr
    apply h
    apply Finset.mem_biUnion.mpr
    refine ⟨(finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s)) (a, x),
      mem_blockPart.mp hx, ?_⟩
    simp only [permutationNeighbors, Equiv.symm_apply_apply]
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
  · intro h w hw
    obtain ⟨i, hiA, hw⟩ := Finset.mem_biUnion.mp hw
    let left := (finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s)).symm i
    obtain ⟨b, _, k, _, hw⟩ := by
      simpa only [permutationNeighbors, Finset.mem_biUnion, Finset.mem_image] using hw
    subst w
    have hx : left.2 ∈ blockPart s A left.1 := by
      apply mem_blockPart.mpr
      simpa only [left, Prod.eta, Equiv.apply_symm_apply] using hiA
    exact mem_blockPart.mp (h left.1 b k (Finset.mem_image.mpr ⟨left.2, hx, rfl⟩))

/-- Right-to-left neighborhood containment is exactly the inverse block
permutation event used for (T4). -/
theorem rightNeighbors_subset_iff_inverse_block_images (s : ℕ)
    (σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s))
    (B : Finset (Fin (4 * s))) (A : Finset (Fin (3 * s))) :
    rightNeighbors (permutationNeighbors s σ) B ⊆ A ↔
      ∀ a b k, (blockPart s B b).image (σ a b k).symm ⊆ blockPart s A a := by
  constructor
  · intro h a b k x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    apply mem_blockPart.mpr
    apply h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨(finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)) (b, y),
      Finset.mem_inter.mpr ⟨?_, mem_blockPart.mp hy⟩⟩
    simp only [permutationNeighbors, Equiv.symm_apply_apply]
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩⟩
    simp
  · intro h i hi
    obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hi).2
    have hwB := (Finset.mem_inter.mp hw).2
    have hwN := (Finset.mem_inter.mp hw).1
    let left := (finProdFinEquiv : Fin 3 × Fin s ≃ Fin (3 * s)).symm i
    obtain ⟨b, _, k, _, hw⟩ := by
      simpa only [permutationNeighbors, Finset.mem_biUnion, Finset.mem_image] using hwN
    have hy : σ left.1 b k left.2 ∈ blockPart s B b := by
      apply mem_blockPart.mpr
      rw [← hw] at hwB
      simpa only [left] using hwB
    have hx := h left.1 b k (Finset.mem_image.mpr
      ⟨σ left.1 b k left.2, hy, (σ left.1 b k).symm_apply_apply left.2⟩)
    have hx' := mem_blockPart.mp hx
    simpa only [left, Prod.eta, Equiv.apply_symm_apply] using hx'

/-- The fixed-set probability estimate in (T4), now stated for the actual
simple selection graph with all 48 independent permutations. -/
theorem right_fixed_graph_event_bound (s : ℕ) (hs : 0 < s)
    (B : Finset (Fin (4 * s))) (A : Finset (Fin (3 * s)))
    (hA : A.card ≤ B.card) :
    uniformProbability (fun σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s) =>
      rightNeighbors (permutationNeighbors s σ) B ⊆ A) ≤
      ((B.card : ℝ) / (3 * s)) ^ (12 * B.card) := by
  have hevent :
      uniformProbability (fun σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s) =>
        rightNeighbors (permutationNeighbors s σ) B ⊆ A) =
      uniformProbability (fun σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s) =>
        ∀ a b k, (blockPart s B b).image (σ a b k).symm ⊆ blockPart s A a) :=
    uniformProbability_congr _ _ (fun σ =>
      rightNeighbors_subset_iff_inverse_block_images s σ B A)
  rw [hevent]
  exact right_fixed_block_event_bound s B.card hs (blockPart s B) (blockPart s A)
    (sum_card_blockPart s B) (by simpa only [sum_card_blockPart] using hA)

@[simp]
theorem mem_fixedPorts_block {s : ℕ} (b : Fin 4) (x : Fin s) :
    (finProdFinEquiv : Fin 4 × Fin s ≃ Fin (4 * s)) (b, x) ∈ fixedPorts s ↔
      b.val < 2 := by
  simp only [fixedPorts, Finset.mem_filter, Finset.mem_univ, true_and]
  change x.val + s * b.val < 2 * s ↔ b.val < 2
  fin_cases b <;> dsimp <;> omega

/-- A fixed target set on `F`, enlarged by all unconstrained `W` vertices. -/
def fixedCover (s : ℕ) (T : Finset (Fin (4 * s))) : Finset (Fin (4 * s)) :=
  T ∪ (fixedPorts s)ᶜ

theorem fixed_neighborhood_subset_iff_cover (s : ℕ)
    (N : Fin (3 * s) → Finset (Fin (4 * s)))
    (A : Finset (Fin (3 * s))) (T : Finset (Fin (4 * s))) :
    (A.biUnion N) ∩ fixedPorts s ⊆ T ↔ A.biUnion N ⊆ fixedCover s T := by
  simp only [Finset.subset_iff, Finset.mem_inter, fixedCover, Finset.mem_union,
    Finset.mem_compl]
  constructor
  · intro h x hx
    by_cases hF : x ∈ fixedPorts s
    · exact Or.inl (h ⟨hx, hF⟩)
    · exact Or.inr hF
  · intro h x hx
    exact (h hx.1).resolve_right (not_not.mpr hx.2)

theorem blockPart_fixedCover_of_lt {s : ℕ} (T : Finset (Fin (4 * s)))
    (b : Fin 4) (hb : b.val < 2) :
    blockPart s (fixedCover s T) b = blockPart s T b := by
  ext x
  simp only [mem_blockPart, fixedCover, Finset.mem_union, Finset.mem_compl,
    mem_fixedPorts_block, hb, not_true_eq_false, or_false]

theorem blockPart_fixedCover_of_ge {s : ℕ} (T : Finset (Fin (4 * s)))
    (b : Fin 4) (hb : 2 ≤ b.val) :
    blockPart s (fixedCover s T) b = Finset.univ := by
  ext x
  simp only [mem_blockPart, fixedCover, Finset.mem_union, Finset.mem_compl,
    mem_fixedPorts_block, Finset.mem_univ, not_lt.mpr hb, not_false_eq_true,
    or_true]

theorem sum_first_two_blockPart (s : ℕ) (T : Finset (Fin (4 * s)))
    (hT : T ⊆ fixedPorts s) :
    (blockPart s T 0).card + (blockPart s T 1).card = T.card := by
  have hzero (b : Fin 4) (hb : 2 ≤ b.val) : blockPart s T b = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := hT (mem_blockPart.mp hx)
    rw [mem_fixedPorts_block] at h
    omega
  have h := sum_card_blockPart s T
  simpa only [Fin.sum_univ_four, hzero 2 (by decide), hzero 3 (by decide),
    Finset.card_empty, add_zero] using h

/-- The fixed-set estimate in (T3) on the complete 48-permutation sample
space of the actual graph. The two `W` blocks remain unconstrained. -/
theorem left_fixed_graph_event_bound (s : ℕ) (hs : 0 < s)
    (A : Finset (Fin (3 * s))) (T : Finset (Fin (4 * s)))
    (hTF : T ⊆ fixedPorts s) (hTcard : T.card ≤ A.card) :
    uniformProbability (fun σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s) =>
      (A.biUnion (permutationNeighbors s σ)) ∩ fixedPorts s ⊆ T) ≤
      ((A.card : ℝ) / (2 * s)) ^ (8 * A.card) := by
  have hevent :
      uniformProbability (fun σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s) =>
        (A.biUnion (permutationNeighbors s σ)) ∩ fixedPorts s ⊆ T) =
      uniformProbability (fun σ : Fin 3 → Fin 4 → Fin 4 → Equiv.Perm (Fin s) =>
        ∀ a b k, (blockPart s A a).image (σ a b k) ⊆ blockPart s (fixedCover s T) b) := by
    apply uniformProbability_congr
    intro σ
    exact (fixed_neighborhood_subset_iff_cover s (permutationNeighbors s σ) A T).trans
      (neighborhood_subset_iff_block_images s σ A (fixedCover s T))
  rw [hevent]
  have h := uniform_block_image_subset_le (K := Fin 4)
    (by simpa using hs : 0 < Fintype.card (Fin s)) (blockPart s A)
    (blockPart s (fixedCover s T))
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [Fintype.card_fin, sum_card_blockPart, Fin.prod_univ_four,
    blockPart_fixedCover_of_lt T 0 (by decide),
    blockPart_fixedCover_of_lt T 1 (by decide),
    blockPart_fixedCover_of_ge T 2 (by decide),
    blockPart_fixedCover_of_ge T 3 (by decide), Finset.card_univ,
    div_self hs0, mul_one] at h
  have hsum : ((blockPart s T 0).card : ℝ) + (blockPart s T 1).card ≤ A.card := by
    exact_mod_cast (show (blockPart s T 0).card + (blockPart s T 1).card ≤ A.card by
      rw [sum_first_two_blockPart s T hTF]
      exact hTcard)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hmean : (((blockPart s T 0).card : ℝ) / s +
      ((blockPart s T 1).card : ℝ) / s) / 2 ≤ (A.card : ℝ) / (2 * s) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (mul_pos (by norm_num) hs')).mpr
    field_simp
    nlinarith
  have hbase := (two_product_le_mean_square (((blockPart s T 0).card : ℝ) / s)
      (((blockPart s T 1).card : ℝ) / s)).trans
    (pow_le_pow_left₀ (by positivity) hmean 2)
  calc
    _ ≤ (((blockPart s T 0).card : ℝ) / s *
        (((blockPart s T 1).card : ℝ) / s)) ^ (A.card * 4) := h
    _ ≤ (((A.card : ℝ) / (2 * s)) ^ 2) ^ (A.card * 4) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := by rw [← pow_mul]; congr 1; omega

end

end EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence
