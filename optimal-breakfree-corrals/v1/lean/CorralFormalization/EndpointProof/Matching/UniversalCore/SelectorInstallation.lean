import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.Compiler
open scoped Classical BigOperators
namespace EndpointSelector.FixedCardinality
open EndpointFlow.AbelianTransport
open EndpointMatching.AbsorptionAssembly
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- The concrete finite data installed for one target, with the numerical
size bound kept separate from the fixed-selector interface. -/
def DegreeSixteenState (P : Vertex G → Prop)
    (Y : Finset (Finset (Vertex G))) (s : ℕ) (I : Finset (Vertex G)) : Prop :=
  (∀ v ∈ I, P v) ∧ I.card ≤ 862 * s ∧
    Disjoint (support I) (support (Y.biUnion id)) ∧
    ∀ Y₀ : Finset (Finset (Vertex G)), Y₀ ⊆ Y → Y₀.card = s →
      Nonempty (Matching (I ∪ Y₀.biUnion id))

/-- Successively build fixed-cardinality selectors with one forbidden set
and pairwise disjoint supports. Every graph is chosen before any query. -/
theorem install_degreeSixteen_selectors {ι : Type*} [DecidableEq ι]
    {P : Vertex G → Prop} {budget : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget 16)
    (D : Finset ι) (part : ι → Fin 3)
    (Y : ι → Finset (Finset (Vertex G))) (s : ι → ℕ) (U : Finset G)
    (hquery : ∀ i ∈ D, 1 ≤ s i ∧ s i ≤ (Y i).card ∧
      (Y i).card ≤ 2 * s i ∧ (∀ T ∈ Y i, LegalPair (part i) T) ∧
      Nonempty (ContiguousSelectionGraph (s i) 16))
    (hbudget : 2 * U.card +
      ∑ i ∈ D, (2 * (2 * (862 * s i)) + 1724 * s i) ≤ budget) :
    ∃ I : ι → Finset (Vertex G),
      (∀ i ∈ D, DegreeSixteenState P (Y i) (s i) (I i)) ∧
      (∀ i ∈ D, Disjoint (support (I i)) U) ∧
      (∀ i ∈ D, ∀ j ∈ D, i ≠ j →
        Disjoint (support (I i)) (support (I j))) := by
  classical
  revert hquery hbudget
  induction D using Finset.induction_on with
  | empty =>
      intro _ _
      exact ⟨fun _ => ∅, by simp, by simp, by simp⟩
  | @insert i D hi ih =>
      intro hquery hbudget
      have hqueryD : ∀ j ∈ D, 1 ≤ s j ∧ s j ≤ (Y j).card ∧
          (Y j).card ≤ 2 * s j ∧ (∀ T ∈ Y j, LegalPair (part j) T) ∧
          Nonempty (ContiguousSelectionGraph (s j) 16) := by
        intro j hj
        exact hquery j (Finset.mem_insert_of_mem hj)
      have hbudgetD : 2 * U.card +
          ∑ j ∈ D, (2 * (2 * (862 * s j)) + 1724 * s j) ≤ budget := by
        simp only [Finset.sum_insert hi] at hbudget
        omega
      obtain ⟨I, hstate, havoid, hdis⟩ := ih hqueryD hbudgetD
      let U' := U ∪ D.biUnion (fun j => support (I j))
      have hsum : (D.biUnion (fun j => support (I j))).card ≤
          ∑ j ∈ D, 2 * (862 * s j) := by
        calc
          _ ≤ ∑ j ∈ D, (support (I j)).card := Finset.card_biUnion_le
          _ ≤ ∑ j ∈ D, 2 * (862 * s j) := by
            apply Finset.sum_le_sum
            intro j hj
            exact (support_card_le (I j)).trans
              (Nat.mul_le_mul_left 2 (hstate j hj).2.1)
      have hF' : 2 * U'.card + 1724 * s i ≤ budget := by
        have hcard := Finset.card_union_le U (D.biUnion (fun j => support (I j)))
        have hsum' : 2 * (∑ j ∈ D, 2 * (862 * s j)) ≤
            ∑ j ∈ D, (2 * (2 * (862 * s j)) + 1724 * s j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j hj
          omega
        simp only [Finset.sum_insert hi] at hbudget
        dsimp [U']
        omega
      obtain ⟨hs, hYlo, hYhi, hlegal, ⟨graph⟩⟩ := hquery i (Finset.mem_insert_self _ _)
      obtain ⟨S, hsize, hSavoid⟩ :=
        fixedSelector_of_degreeSixteenGraph hP hlocal (selectionGraph_of_contiguous graph)
          (part i) (Y i) U' hs hYlo hYhi hlegal hF'
      have hSavoid' : Disjoint (support S.interior) U' :=
        hSavoid.mono_right Finset.subset_union_left
      let J := Function.update I i S.interior
      have hJi : J i = S.interior := by simp [J]
      have hJj {j : ι} (hj : j ∈ D) : J j = I j := by
        have hji : j ≠ i := by
          intro h
          subst j
          exact hi hj
        simp [J, hji]
      refine ⟨J, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [hJi]
          exact ⟨S.inside, hsize, S.roots_fresh, S.matching⟩
        · rw [hJj hj]
          exact hstate j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [hJi]
          exact hSavoid'.mono_right Finset.subset_union_left
        · rw [hJj hj]
          exact havoid j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with hjEq | hjD
        · subst j
          have hkD : k ∈ D := by
            rcases Finset.mem_insert.mp hk with he | he
            · exact (hjk he.symm).elim
            · exact he
          rw [hJi, hJj hkD]
          apply hSavoid'.mono_right
          intro x hx
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hkD, hx⟩)
        · rcases Finset.mem_insert.mp hk with hkEq | hkD
          · subst k
            rw [hJj hjD, hJi]
            apply (hSavoid'.mono_right ?_).symm
            intro x hx
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hjD, hx⟩)
          · rw [hJj hjD, hJj hkD]
            exact hdis j hjD k hkD hjk

/-- Install all three fixed selectors before the later residual is known.
The full pair inventory is included in the common forbidden support. -/
theorem three_selectors_of_localSupply_and_graphs
    {P : Vertex G → Prop} {budget K : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget 16)
    (Q : Fin 3 → Finset (Finset (Vertex G))) (U : Finset G)
    (hquery : ∀ p, 1 ≤ (Q p).card - K ∧
      (Q p).card - K ≤ (Q p).card ∧
      (Q p).card ≤ 2 * ((Q p).card - K) ∧
      (∀ T ∈ Q p, LegalPair p T) ∧
      Nonempty (ContiguousSelectionGraph ((Q p).card - K) 16))
    (hbudget : 2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
      ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
        1724 * ((Q p).card - K)) ≤ budget) :
    ∃ selectors : ∀ p, FixedSelector P (Q p) ((Q p).card - K),
      (∀ p, (selectors p).interior.card ≤ 862 * ((Q p).card - K)) ∧
      (∀ p, Disjoint (support (selectors p).interior) U) ∧
      (∀ p q, p ≠ q → Disjoint (selectors p).interior (selectors q).interior) ∧
      (∀ p, Disjoint (selectors p).interior ((Finset.univ.biUnion Q).biUnion id)) := by
  classical
  let s : Fin 3 → ℕ := fun p => (Q p).card - K
  let F := U ∪ support ((Finset.univ.biUnion Q).biUnion id)
  have hquery' : ∀ p ∈ (Finset.univ : Finset (Fin 3)), 1 ≤ s p ∧ s p ≤ (Q p).card ∧
      (Q p).card ≤ 2 * s p ∧ (∀ T ∈ Q p, LegalPair p T) ∧
      Nonempty (ContiguousSelectionGraph (s p) 16) := by
    intro p _
    exact hquery p
  obtain ⟨I, hstate, havoid, hdis⟩ :=
    install_degreeSixteen_selectors hP hlocal Finset.univ id Q s F hquery' hbudget
  let selectors : ∀ p, FixedSelector P (Q p) ((Q p).card - K) := fun p =>
    ⟨I p, (hstate p (Finset.mem_univ _)).1,
      (hstate p (Finset.mem_univ _)).2.2.1, (hstate p (Finset.mem_univ _)).2.2.2⟩
  refine ⟨selectors, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hstate p (Finset.mem_univ _)).2.1
  · intro p
    exact (havoid p (Finset.mem_univ _)).mono_right Finset.subset_union_left
  · intro p q hpq
    exact disjoint_of_support (hdis p (Finset.mem_univ _) q (Finset.mem_univ _) hpq)
  · intro p
    exact disjoint_of_support
      ((havoid p (Finset.mem_univ _)).mono_right Finset.subset_union_right)

end
end EndpointSelector.FixedCardinality
