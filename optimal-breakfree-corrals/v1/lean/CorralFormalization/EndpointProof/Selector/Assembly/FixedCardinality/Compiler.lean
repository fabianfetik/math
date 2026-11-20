import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PortRouting
import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.DisjointAssembly

open scoped Classical BigOperators

namespace EndpointSelector.FixedCardinality

open EndpointFlow.AbelianTransport
open EndpointMatching.AbsorptionAssembly

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- Compile a concrete routed port graph and local selectors into a single
fixed-cardinality selector. Fixed and variable ports are genuine tagged
sets. The graph routing is an explicit combinatorial input; it does not
assume the sought matching or selector. The numerical budget includes the
entire temporary port pool, even ports absent from the eventual interior. -/
theorem fixedSelector_of_routed_localSupply
    {ι : Type*} [DecidableEq ι] {P : Vertex G → Prop}
    {budget arity s : ℕ} (hlocal : LocalSupply P budget arity)
    (part : Fin 3) (D : Finset ι)
    (fixed varying Y : Finset (Finset (Vertex G)))
    (R : ι → Finset (Finset (Vertex G))) (U : Finset G)
    (hY : Y ⊆ varying) (hfixedVariable : Disjoint fixed varying)
    (hfixedInside : ∀ T ∈ fixed, ∀ v ∈ T, P v)
    (hfixedAvoid : Disjoint (support (fixed.biUnion id)) U)
    (hports : ∀ T ∈ fixed ∪ varying, ∀ T' ∈ fixed ∪ varying, T ≠ T' →
      Disjoint (support T) (support T'))
    (hquery : ∀ i ∈ D, (R i).Nonempty ∧ (R i).card ≤ arity ∧
      (∀ T ∈ R i, LegalPair part T) ∧ R i ⊆ fixed ∪ varying)
    (hroute : ∀ Y₀ : Finset (Finset (Vertex G)), Y₀ ⊆ Y → Y₀.card = s →
      ∃ f : ι → Finset (Vertex G), (∀ i ∈ D, f i ∈ R i) ∧
        Set.InjOn f D ∧ D.image f = fixed ∪ Y₀)
    (hbudget : (U ∪ support ((fixed ∪ varying).biUnion id)).card +
      ∑ i ∈ D, 2 * (18 * (R i).card - 2) ≤ budget) :
    ∃ S : FixedSelector P Y s,
      S.interior.card ≤
        (∑ i ∈ D, (18 * (R i).card - 2)) + (fixed.biUnion id).card ∧
      Disjoint (support S.interior) U := by
  classical
  let F := U ∪ support ((fixed ∪ varying).biUnion id)
  have hlocalQuery : ∀ i ∈ D, (R i).Nonempty ∧ (R i).card ≤ arity ∧
      ∀ T ∈ R i, LegalPair part T := by
    intro i hi
    exact ⟨(hquery i hi).1, (hquery i hi).2.1, (hquery i hi).2.2.1⟩
  obtain ⟨I, hstate, havoid, hdis⟩ :=
    install_local_selectors hlocal part D R F hlocalQuery hbudget
  have hport_support {T : Finset (Vertex G)} (hT : T ∈ fixed ∪ varying) :
      support T ⊆ F := by
    apply Finset.Subset.trans (support_mono ?_) Finset.subset_union_right
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨T, hT, hv⟩
  have hIport (i : ι) (hi : i ∈ D) {T : Finset (Vertex G)}
      (hT : T ∈ fixed ∪ varying) :
      Disjoint (support (I i)) (support T) :=
    (havoid i hi).mono_right (hport_support hT)
  have hYpool : Y.biUnion id ⊆ (fixed ∪ varying).biUnion id := by
    intro v hv
    obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr
      ⟨T, Finset.mem_union_right _ (hY hT), hvT⟩
  have hIroots (i : ι) (hi : i ∈ D) :
      Disjoint (support (I i)) (support (Y.biUnion id)) := by
    apply (havoid i hi).mono_right
    exact (support_mono hYpool).trans Finset.subset_union_right
  have hfixedRoots :
      Disjoint (support (fixed.biUnion id)) (support (Y.biUnion id)) := by
    rw [support_biUnion, support_biUnion]
    apply (Finset.disjoint_biUnion_left _ _ _).mpr
    intro T hT
    apply (Finset.disjoint_biUnion_right _ _ _).mpr
    intro T' hT'
    have hne : T ≠ T' := by
      intro he
      subst T'
      exact Finset.disjoint_left.mp hfixedVariable hT (hY hT')
    exact hports T (Finset.mem_union_left _ hT)
      T' (Finset.mem_union_right _ (hY hT')) hne
  let E := (D.biUnion I) ∪ fixed.biUnion id
  have hEinside : ∀ v ∈ E, P v := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
      exact (hstate i hi).1 v hv
    · obtain ⟨T, hT, hv⟩ := Finset.mem_biUnion.mp hv
      exact hfixedInside T hT v hv
  have hEroots : Disjoint (support E) (support (Y.biUnion id)) := by
    rw [support_union]
    apply Finset.disjoint_union_left.mpr
    refine ⟨?_, hfixedRoots⟩
    rw [support_biUnion]
    exact (Finset.disjoint_biUnion_left _ _ _).mpr hIroots
  have hEmatch : ∀ Y₀ : Finset (Finset (Vertex G)), Y₀ ⊆ Y → Y₀.card = s →
      Nonempty (Matching (E ∪ Y₀.biUnion id)) := by
    intro Y₀ hY₀ hs
    obtain ⟨f, hf, hfinj, hfimage⟩ := hroute Y₀ hY₀ hs
    have hII : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → Disjoint (I i) (I j) := by
      intro i hi j hj hne
      exact disjoint_of_support (hdis i hi j hj hne)
    have hIT : ∀ i ∈ D, ∀ j ∈ D, Disjoint (I i) (f j) := by
      intro i hi j hj
      exact disjoint_of_support (hIport i hi ((hquery j hj).2.2.2 (hf j hj)))
    have hTT : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → Disjoint (f i) (f j) := by
      intro i hi j hj hne
      apply disjoint_of_support
      apply hports (f i) ((hquery i hi).2.2.2 (hf i hi))
        (f j) ((hquery j hj).2.2.2 (hf j hj))
      intro he
      exact hne (hfinj hi hj he)
    have hmatches : ∀ i ∈ D, Nonempty (Matching (I i ∪ f i)) := by
      intro i hi
      exact (hstate i hi).2.2 (f i) (hf i hi)
    obtain ⟨M⟩ := assemble_slots D I f hII hIT hTT hmatches
    have hfsets : D.biUnion f = fixed.biUnion id ∪ Y₀.biUnion id := by
      calc
        D.biUnion f = (D.image f).biUnion id := by
          simp only [Finset.image_biUnion, id_eq]
        _ = fixed.biUnion id ∪ Y₀.biUnion id := by rw [hfimage, Finset.union_biUnion]
    refine ⟨?_⟩
    change Matching (((D.biUnion I) ∪ fixed.biUnion id) ∪ Y₀.biUnion id)
    rw [Finset.union_assoc, ← hfsets]
    exact M
  let S : FixedSelector P Y s :=
    ⟨E, hEinside, hEroots, hEmatch⟩
  refine ⟨S, ?_, ?_⟩
  · dsimp [S, E]
    calc
      _ ≤ (D.biUnion I).card + (fixed.biUnion id).card := Finset.card_union_le _ _
      _ ≤ (∑ i ∈ D, (I i).card) + (fixed.biUnion id).card :=
        Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum (fun i hi => (hstate i hi).2.1)) _
  · change Disjoint (support E) U
    rw [support_union]
    apply Finset.disjoint_union_left.mpr
    refine ⟨?_, hfixedAvoid⟩
    rw [support_biUnion]
    apply (Finset.disjoint_biUnion_left _ _ _).mpr
    intro i hi
    exact (havoid i hi).mono_right Finset.subset_union_left

/-- The fixed-cardinality compiler, from the actual local selectors and one
abstract robust selection graph. It constructs the physical fixed and dummy
ports, relabels the graph, and installs the local interiors before the
selected target subfamily is given. -/
theorem fixedSelector_of_localSupply_and_graph
    {P : Vertex G → Prop} {budget degree s : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget degree)
    (hdegree : 1 ≤ degree) (graph : SelectionGraph s degree)
    (part : Fin 3) (Y : Finset (Finset (Vertex G))) (U : Finset G)
    (hs : 1 ≤ s) (hsize₁ : s ≤ Y.card) (hsize₂ : Y.card ≤ 2 * s)
    (hlegal : ∀ T ∈ Y, LegalPair part T)
    (hbudget : U.card + 8 * s + (3 * s) * (2 * (18 * degree - 2)) ≤ budget) :
    ∃ S : FixedSelector P Y s,
      S.interior.card ≤ (3 * s) * (18 * degree - 2) + 4 * s ∧
      Disjoint (support S.interior) U := by
  classical
  have hpoolBudget : U.card + 8 * s ≤ budget := by omega
  obtain ⟨pool⟩ :=
    portPool_of_localSupply hP hlocal hdegree part Y U hs hsize₁ hsize₂ hlegal hpoolBudget
  obtain ⟨R, hR, hroute⟩ :=
    relabel_selectionGraph pool.fixed pool.varying pool.fixed_card pool.varying_card
      pool.disjoint graph
  let D : Finset (Fin (3 * s)) := Finset.univ
  have hquery : ∀ i ∈ D, (R i).Nonempty ∧ (R i).card ≤ degree ∧
      (∀ T ∈ R i, LegalPair part T) ∧ R i ⊆ pool.fixed ∪ pool.varying := by
    intro i _
    exact ⟨(hR i).1, (hR i).2.1,
      fun T hT => pool.legal T ((hR i).2.2 hT), (hR i).2.2⟩
  have hports : ∀ T ∈ pool.fixed ∪ pool.varying,
      ∀ T' ∈ pool.fixed ∪ pool.varying, T ≠ T' →
        Disjoint (support T) (support T') := by
    intro T hT T' hT' hne
    exact legalPair_support_disjoint (pool.legal T hT) (pool.legal T' hT') hne
  have hroutes : ∀ Y₀ : Finset (Finset (Vertex G)), Y₀ ⊆ Y → Y₀.card = s →
      ∃ f : Fin (3 * s) → Finset (Vertex G), (∀ i ∈ D, f i ∈ R i) ∧
        Set.InjOn f D ∧ D.image f = pool.fixed ∪ Y₀ := by
    intro Y₀ hY₀ hcard
    obtain ⟨f, hf, hfinj, himage⟩ :=
      hroute Y₀ (hY₀.trans pool.includes_targets) hcard
    refine ⟨f, ?_, ?_, himage⟩
    · intro i _
      exact hf i
    · intro i _ j _ hij
      exact hfinj hij
  have hsumBudget :
      (∑ i ∈ D, 2 * (18 * (R i).card - 2)) ≤
        (3 * s) * (2 * (18 * degree - 2)) := by
    calc
      _ ≤ ∑ _i ∈ D, 2 * (18 * degree - 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul_left 2
          (Nat.sub_le_sub_right (Nat.mul_le_mul_left 18 (hR i).2.1) 2)
      _ = _ := by simp [D, Nat.mul_comm]
  have hinstallBudget :
      (U ∪ support ((pool.fixed ∪ pool.varying).biUnion id)).card +
        ∑ i ∈ D, 2 * (18 * (R i).card - 2) ≤ budget := by
    have hcard := Finset.card_union_le U
      (support ((pool.fixed ∪ pool.varying).biUnion id))
    have hpool := pool.support_card
    omega
  obtain ⟨S, hScard, hSavoid⟩ :=
    fixedSelector_of_routed_localSupply hlocal part D pool.fixed pool.varying Y R U
      pool.includes_targets pool.disjoint pool.fixed_inside pool.fixed_avoids
      hports hquery hroutes hinstallBudget
  have hsumSize :
      (∑ i ∈ D, (18 * (R i).card - 2)) ≤
        (3 * s) * (18 * degree - 2) := by
    calc
      _ ≤ ∑ _i ∈ D, (18 * degree - 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.sub_le_sub_right (Nat.mul_le_mul_left 18 (hR i).2.1) 2
      _ = _ := by simp [D, Nat.mul_comm]
  have hfixedSize : (pool.fixed.biUnion id).card ≤ 4 * s := by
    calc
      _ ≤ ∑ T ∈ pool.fixed, T.card := Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ pool.fixed, 2 := by
        apply Finset.sum_le_sum
        intro T hT
        exact legalPair_card_le (pool.legal T (Finset.mem_union_left _ hT))
      _ = 4 * s := by simp [pool.fixed_card, Nat.mul_comm]; omega
  exact ⟨S, by omega, hSavoid⟩

/-- These identities express the exact temporary-pool and final-interior
coefficients, with all subtractions justified by positive degree. -/
theorem selector_size_identity {degree s : ℕ} (hdegree : 1 ≤ degree) :
    (3 * s) * (18 * degree - 2) + 4 * s = (54 * degree - 2) * s := by
  have h₁ : 18 * degree - 2 + 2 = 18 * degree := Nat.sub_add_cancel (by omega)
  have h₂ : 54 * degree - 2 + 2 = 54 * degree := Nat.sub_add_cancel (by omega)
  have h₃ := congrArg (fun x : ℕ => x * s) h₁
  have h₄ := congrArg (fun x : ℕ => x * s) h₂
  simp only [Nat.add_mul] at h₃ h₄
  nlinarith [h₃, h₄]

theorem selector_budget_identity {degree s : ℕ} (hdegree : 1 ≤ degree) :
    8 * s + (3 * s) * (2 * (18 * degree - 2)) = (108 * degree - 4) * s := by
  have h₁ : 18 * degree - 2 + 2 = 18 * degree := Nat.sub_add_cancel (by omega)
  have h₂ : 108 * degree - 4 + 4 = 108 * degree := Nat.sub_add_cancel (by omega)
  have h₃ := congrArg (fun x : ℕ => x * s) h₁
  have h₄ := congrArg (fun x : ℕ => x * s) h₂
  simp only [Nat.add_mul] at h₃ h₄
  nlinarith [h₃, h₄]

/-- The general written compiler bound for a contiguous-index selection
graph. No upper degree bound is needed beyond the stated local supply. -/
theorem fixedSelector_of_contiguous_graph
    {P : Vertex G → Prop} {budget degree s : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget degree)
    (hdegree : 1 ≤ degree) (graph : ContiguousSelectionGraph s degree)
    (part : Fin 3) (Y : Finset (Finset (Vertex G))) (U : Finset G)
    (hs : 1 ≤ s) (hsize₁ : s ≤ Y.card) (hsize₂ : Y.card ≤ 2 * s)
    (hlegal : ∀ T ∈ Y, LegalPair part T)
    (hbudget : 2 * U.card + (108 * degree - 4) * s ≤ budget) :
    ∃ S : FixedSelector P Y s,
      S.interior.card ≤ (54 * degree - 2) * s ∧
      Disjoint (support S.interior) (U ∪ U.image Neg.neg) := by
  classical
  let V := U ∪ U.image Neg.neg
  have hV : V.card ≤ 2 * U.card := by
    have h := Finset.card_union_le U (U.image Neg.neg)
    have himage := Finset.card_image_le (s := U) (f := Neg.neg)
    dsimp [V]
    omega
  have hb : V.card + 8 * s + (3 * s) * (2 * (18 * degree - 2)) ≤ budget := by
    have heq := selector_budget_identity (s := s) hdegree
    omega
  obtain ⟨S, hsize, havoid⟩ :=
    fixedSelector_of_localSupply_and_graph hP hlocal hdegree
      (selectionGraph_of_contiguous graph) part Y V hs hsize₁ hsize₂ hlegal hb
  refine ⟨S, ?_, havoid⟩
  rw [selector_size_identity hdegree] at hsize
  exact hsize

/-- Degree-eight specialization. The abstract degree-eight graph is still
an explicit premise; its existence is not asserted by this theorem. -/
theorem fixedSelector_of_degreeEightGraph
    {P : Vertex G → Prop} {budget s : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget 8)
    (graph : SelectionGraph s 8)
    (part : Fin 3) (Y : Finset (Finset (Vertex G))) (U : Finset G)
    (hs : 1 ≤ s) (hsize₁ : s ≤ Y.card) (hsize₂ : Y.card ≤ 2 * s)
    (hlegal : ∀ T ∈ Y, LegalPair part T)
    (hbudget : 2 * U.card + 860 * s ≤ budget) :
    ∃ S : FixedSelector P Y s, S.interior.card ≤ 430 * s ∧
      Disjoint (support S.interior) (U ∪ U.image Neg.neg) := by
  classical
  let V := U ∪ U.image Neg.neg
  have hV : V.card ≤ 2 * U.card := by
    have h := Finset.card_union_le U (U.image Neg.neg)
    have himage := Finset.card_image_le (s := U) (f := Neg.neg)
    dsimp [V]
    omega
  have hb : V.card + 8 * s + (3 * s) * (2 * (18 * 8 - 2)) ≤ budget := by
    norm_num
    omega
  obtain ⟨S, hsize, havoid⟩ :=
    fixedSelector_of_localSupply_and_graph hP hlocal (by omega) graph
      part Y V hs hsize₁ hsize₂ hlegal hb
  refine ⟨S, ?_, havoid⟩
  norm_num at hsize
  omega

/-- Degree-sixteen specialization, applicable at any positive s if a
corresponding graph is supplied. Its graph existence is also a premise. -/
theorem fixedSelector_of_degreeSixteenGraph
    {P : Vertex G → Prop} {budget s : ℕ}
    (hP : PairReservoir P) (hlocal : LocalSupply P budget 16)
    (graph : SelectionGraph s 16)
    (part : Fin 3) (Y : Finset (Finset (Vertex G))) (U : Finset G)
    (hs : 1 ≤ s) (hsize₁ : s ≤ Y.card) (hsize₂ : Y.card ≤ 2 * s)
    (hlegal : ∀ T ∈ Y, LegalPair part T)
    (hbudget : 2 * U.card + 1724 * s ≤ budget) :
    ∃ S : FixedSelector P Y s, S.interior.card ≤ 862 * s ∧
      Disjoint (support S.interior) (U ∪ U.image Neg.neg) := by
  classical
  let V := U ∪ U.image Neg.neg
  have hV : V.card ≤ 2 * U.card := by
    have h := Finset.card_union_le U (U.image Neg.neg)
    have himage := Finset.card_image_le (s := U) (f := Neg.neg)
    dsimp [V]
    omega
  have hb : V.card + 8 * s + (3 * s) * (2 * (18 * 16 - 2)) ≤ budget := by
    norm_num
    omega
  obtain ⟨S, hsize, havoid⟩ :=
    fixedSelector_of_localSupply_and_graph hP hlocal (by omega) graph
      part Y V hs hsize₁ hsize₂ hlegal hb
  refine ⟨S, ?_, havoid⟩
  norm_num at hsize
  omega

/-- The compiler specializes to the actual sampled P reservoir on the very
same augmentation. The graph remains an explicit hypothesis. -/
theorem fixedSelector_of_colouredSelectors_degreeEight [Fintype G]
    {budget s : ℕ} (ω : EndpointFullProduct.FullSample G)
    (hlocal : ColouredSelectors ω budget) (graph : SelectionGraph s 8)
    (part : Fin 3) (Y : Finset (Finset (Vertex G))) (U : Finset G)
    (hs : 1 ≤ s) (hsize₁ : s ≤ Y.card) (hsize₂ : Y.card ≤ 2 * s)
    (hlegal : ∀ T ∈ Y, LegalPair part T)
    (hbudget : 2 * U.card + 860 * s ≤ budget) :
    ∃ S : FixedSelector (ReservoirVertex ω false) Y s,
      S.interior.card ≤ 430 * s ∧
      Disjoint (support S.interior) (U ∪ U.image Neg.neg) :=
  fixedSelector_of_degreeEightGraph
    (pairReservoir_of_reservoirVertex ω false)
    (localSupply_of_colouredSelectors ω budget 8 (by omega) hlocal)
    graph part Y U hs hsize₁ hsize₂ hlegal hbudget

/-- The written contiguous-index graph is accepted through the checked
port-index equivalence. The graph itself remains an explicit premise. -/
theorem fixedSelector_of_contiguous_degreeEight [Fintype G]
    {budget s : ℕ} (ω : EndpointFullProduct.FullSample G)
    (hlocal : ColouredSelectors ω budget) (graph : ContiguousSelectionGraph s 8)
    (part : Fin 3) (Y : Finset (Finset (Vertex G))) (U : Finset G)
    (hs : 1 ≤ s) (hsize₁ : s ≤ Y.card) (hsize₂ : Y.card ≤ 2 * s)
    (hlegal : ∀ T ∈ Y, LegalPair part T)
    (hbudget : 2 * U.card + 860 * s ≤ budget) :
    ∃ S : FixedSelector (ReservoirVertex ω false) Y s,
      S.interior.card ≤ 430 * s ∧
      Disjoint (support S.interior) (U ∪ U.image Neg.neg) :=
  fixedSelector_of_colouredSelectors_degreeEight ω hlocal
    (selectionGraph_of_contiguous graph) part Y U hs hsize₁ hsize₂ hlegal hbudget

/-- The fixed-cardinality compiler and the existing Q-cover supplies use
one and the same augmentation. Graph existence remains explicit. -/
def OriginalAdmitsFixedSelectorsAndCovers [Fintype G]
    (budget qBudget : ℕ) (sample : EndpointFullProduct.OriginalSample G) : Prop :=
  ∃ ω : EndpointFullProduct.FullSample G,
    EndpointFullProduct.originalProcess ω = sample ∧
    ColouredSelectors ω budget ∧
    SixRootSupplier (ReservoirVertex ω true) qBudget ∧
    PairedCoversAvailable ω qBudget ∧
    ∀ (s : ℕ), 16384 ≤ s → ∀ (part : Fin 3)
      (Y : Finset (Finset (Vertex G))) (U : Finset G),
      s ≤ Y.card → Y.card ≤ 2 * s → (∀ T ∈ Y, LegalPair part T) →
      2 * U.card + 860 * s ≤ budget →
      ∃ S : FixedSelector (ReservoirVertex ω false) Y s,
        S.interior.card ≤ 430 * s ∧
        Disjoint (support S.interior) (U ∪ U.image Neg.neg)

theorem fixedSelectors_and_covers_of_joint_augmentation [Fintype G]
    {budget qBudget : ℕ} {sample : EndpointFullProduct.OriginalSample G}
    (hgood : OriginalAdmitsSelectorsSixRootsAndCovers budget qBudget sample)
    (hgraphs : ∀ s : ℕ, 16384 ≤ s → Nonempty (SelectionGraph s 8)) :
    OriginalAdmitsFixedSelectorsAndCovers budget qBudget sample := by
  obtain ⟨ω, hω, hlocal, hflow, hcover⟩ := hgood
  refine ⟨ω, hω, hlocal, hflow, hcover, ?_⟩
  intro s hs part Y U hsize₁ hsize₂ hlegal hbudget
  obtain ⟨graph⟩ := hgraphs s hs
  exact fixedSelector_of_colouredSelectors_degreeEight ω hlocal graph part Y U
    (by omega) hsize₁ hsize₂ hlegal hbudget

open MeasureTheory
open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

/-- Conditional on the purely combinatorial degree-eight graph theorem,
the existing original-sample probability bound already supplies the fixed
selectors and the earlier Q-cover data on one augmentation. This is not an
existence theorem for a universal absorbing core. -/
theorem original_fixedSelectors_and_covers_probability_abelian
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hgraphs : ∀ s : ℕ, 16384 ≤ s → Nonempty (SelectionGraph s 8)) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G]
      (_hodd : Odd (Fintype.card G)) (_hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {sample : OriginalSample G | ¬ OriginalAdmitsFixedSelectorsAndCovers
          (selectorExternalBudget (p q) (Fintype.card G))
          (flowBudget (tau q) (Fintype.card G)) sample} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ :=
    original_selectors_sixRoots_and_covers_probability_abelian q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hN G hodd hn)
  intro sample hbad hgood
  exact hbad (fixedSelectors_and_covers_of_joint_augmentation hgood hgraphs)

/-- Probability corollary with the exact contiguous graph convention used
in the written degree-eight claim. -/
theorem original_fixedSelectors_and_covers_probability_of_contiguous
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hgraphs : ∀ s : ℕ, 16384 ≤ s → Nonempty (ContiguousSelectionGraph s 8)) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G]
      (_hodd : Odd (Fintype.card G)) (_hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {sample : OriginalSample G | ¬ OriginalAdmitsFixedSelectorsAndCovers
          (selectorExternalBudget (p q) (Fintype.card G))
          (flowBudget (tau q) (Fintype.card G)) sample} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  apply original_fixedSelectors_and_covers_probability_abelian q hq0 hq1
  intro s hs
  obtain ⟨graph⟩ := hgraphs s hs
  exact ⟨selectionGraph_of_contiguous graph⟩
end
end EndpointSelector.FixedCardinality
