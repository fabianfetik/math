import CorralFormalization.EndpointProof.Matching.UniversalCore.PairInventory

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly
noncomputable section
variable {G : Type*} [AddCommGroup G]

set_option maxHeartbeats 1200000 in
/-- Construct the universal absorbing core from fixed selectors, prechosen
disjoint buffers, and a later query-dependent paired cover. The cover is
strictly weaker than the conclusion: it matches S only after adding a
possibly S-dependent subfamily of the fixed Q inventory. -/
theorem fixed_core_absorbs_of_pair_covers
    {ι : Type*} [DecidableEq ι] (P : Vertex G → Prop)
    (Q : Fin 3 → Finset (Finset (Vertex G))) (K capacity : ℕ)
    (selectors : ∀ p : Fin 3, FixedSelector P (Q p) ((Q p).card - K))
    (buffers : Finset ι) (pick : ι → Fin 3 → Finset (Vertex G))
    (hlegal : ∀ p T, T ∈ Q p → LegalPair p T)
    (hEdis : ∀ p q, p ≠ q → Disjoint (selectors p).interior (selectors q).interior)
    (hEQ : ∀ p, Disjoint (selectors p).interior ((Finset.univ.biUnion Q).biUnion id))
    (hBmem : ∀ i ∈ buffers, ∀ p, pick i p ∈ Q p)
    (hBunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hBmatch : ∀ i ∈ buffers,
      Nonempty (Matching (Finset.univ.biUnion (pick i))))
    (hcount : 3 * K ≤ buffers.card)
    (hcover : ∀ S : Finset (Vertex G),
      (∀ v ∈ S, v.2 ≠ 0) → Balanced S → (∑ v ∈ S, v.2 = 0) →
      Disjoint (coreVertices Q (fun p => (selectors p).interior)) S →
      S.card ≤ capacity →
      ∃ (T : Finset (Finset (Vertex G))) (m : ℕ),
        T ⊆ Finset.univ.biUnion Q ∧
        (∀ p, (T ∩ Q p).card = m) ∧ m ≤ K ∧
        Nonempty (Matching (S ∪ T.biUnion id))) :
    AbsorbsUpTo (coreVertices Q (fun p => (selectors p).interior)) capacity := by
  classical
  intro S hSnz hSb hSsum hAS hSsize
  obtain ⟨T, m, hTsub, hTpart, hmK, hST⟩ :=
    hcover S hSnz hSb hSsum hAS hSsize
  have hQdis := legalPair_families_disjoint Q hlegal
  obtain ⟨C, hCsub, hCcard, hFsub, hFT, hFpart, hrest⟩ :=
    pad_pair_inventory Q buffers pick T K m hQdis hBmem hBunique
      hTsub hTpart hmK hcount
  let F := bufferPairs C pick
  let Y : Fin 3 → Finset (Finset (Vertex G)) := fun p => Q p \ (T ∪ F)
  let I : Fin 3 → Finset (Vertex G) := fun p => (selectors p).interior
  let Qall := Finset.univ.biUnion Q
  let Iall := Finset.univ.biUnion I
  let Yall := Finset.univ.biUnion Y
  let Qverts := Qall.biUnion id
  let Yverts := Yall.biUnion id
  have hYsub (p : Fin 3) : Y p ⊆ Q p := Finset.sdiff_subset
  have hYallSub : Yall ⊆ Qall := by
    intro T' hT'
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hT'
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hYsub p hp⟩
  have hYcard (p : Fin 3) : (Y p).card = (Q p).card - K := hrest p
  have hYmatch (p : Fin 3) : Nonempty (Matching (I p ∪ (Y p).biUnion id)) :=
    (selectors p).matching (Y p) (hYsub p) (hYcard p)
  have hIallQ : Disjoint Iall Qverts := by
    apply (Finset.disjoint_biUnion_left _ _ _).mpr
    intro p _
    exact hEQ p
  have hYpartQ (p : Fin 3) : (Y p).biUnion id ⊆ Qverts :=
    part_pairs_inside_all Q p (hYsub p)
  have hYpartsDis (p q : Fin 3) (hpq : p ≠ q) :
      Disjoint ((Y p).biUnion id) ((Y q).biUnion id) := by
    apply qpair_families_vertices_disjoint Q hlegal
      ((hYsub p).trans (Finset.subset_biUnion_of_mem Q (Finset.mem_univ p)))
      ((hYsub q).trans (Finset.subset_biUnion_of_mem Q (Finset.mem_univ q)))
    exact (hQdis p q hpq).mono (hYsub p) (hYsub q)
  have hselDis : ∀ p ∈ (Finset.univ : Finset (Fin 3)),
      ∀ q ∈ (Finset.univ : Finset (Fin 3)), p ≠ q →
      Disjoint (I p ∪ (Y p).biUnion id) (I q ∪ (Y q).biUnion id) := by
    intro p _ q _ hpq
    apply Finset.disjoint_union_left.mpr
    constructor
    · apply Finset.disjoint_union_right.mpr
      refine ⟨hEdis p q hpq, ?_⟩
      exact (hEQ p).mono_right (hYpartQ q)
    · apply Finset.disjoint_union_right.mpr
      refine ⟨?_, hYpartsDis p q hpq⟩
      exact ((hEQ q).mono_right (hYpartQ p)).symm
  obtain ⟨MSel⟩ := matching_biUnion (Finset.univ : Finset (Fin 3))
    (fun p => I p ∪ (Y p).biUnion id) hselDis (fun p _ => hYmatch p)
  have hSelSet : Finset.univ.biUnion (fun p => I p ∪ (Y p).biUnion id) =
      Iall ∪ Yverts := by
    dsimp [Iall, Yverts, Yall]
    rw [Finset.biUnion_union, Finset.biUnion_biUnion]
  have hSel : Nonempty (Matching (Iall ∪ Yverts)) := ⟨hSelSet ▸ MSel⟩
  have hFmatch : Nonempty (Matching (F.biUnion id)) :=
    matching_of_selected_buffers Q buffers pick hlegal hBmem hBunique hBmatch C hCsub
  have hYF : Disjoint Yall F := by
    apply Finset.disjoint_left.mpr
    intro T' hT' hF'
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hT'
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_union_right _ hF')
  have hYT : Disjoint Yall T := by
    apply Finset.disjoint_left.mpr
    intro T' hY' hT'
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hY'
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_union_left _ hT')
  have hYvertsF : Disjoint Yverts (F.biUnion id) :=
    qpair_families_vertices_disjoint Q hlegal hYallSub hFsub hYF
  have hYvertsT : Disjoint Yverts (T.biUnion id) :=
    qpair_families_vertices_disjoint Q hlegal hYallSub hTsub hYT
  have hFvertsT : Disjoint (F.biUnion id) (T.biUnion id) :=
    qpair_families_vertices_disjoint Q hlegal hFsub hTsub hFT
  have hFvertsQ : F.biUnion id ⊆ Qverts := by
    intro v hv
    obtain ⟨T', hT', hvT'⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨T', hFsub hT', hvT'⟩
  have hTvertsQ : T.biUnion id ⊆ Qverts := by
    intro v hv
    obtain ⟨T', hT', hvT'⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨T', hTsub hT', hvT'⟩
  have hYvertsQ : Yverts ⊆ Qverts := by
    intro v hv
    obtain ⟨T', hT', hvT'⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨T', hYallSub hT', hvT'⟩
  have hIS : Disjoint Iall S := by
    apply hAS.mono_left
    exact Finset.subset_union_left
  have hQS : Disjoint Qverts S := by
    apply hAS.mono_left
    exact Finset.subset_union_right
  have hpartition : Qall = T ∪ F ∪ Yall := by
    ext T'
    constructor
    · intro hT'
      by_cases ht : T' ∈ T
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ ht)
      by_cases hf : T' ∈ F
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hf)
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hT'
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_univ _, Finset.mem_sdiff.mpr
          ⟨hp, by simp [ht, hf]⟩⟩)
    · intro hT'
      rcases Finset.mem_union.mp hT' with hTF | hY
      · rcases Finset.mem_union.mp hTF with hT | hF
        · exact hTsub hT
        · exact hFsub hF
      · exact hYallSub hY
  have hcoverF : Disjoint (S ∪ T.biUnion id) (F.biUnion id) := by
    apply Finset.disjoint_union_left.mpr
    exact ⟨(hQS.mono_left hFvertsQ).symm, hFvertsT.symm⟩
  obtain ⟨MST⟩ := hST
  obtain ⟨MF⟩ := hFmatch
  let M₁ := unionMatching MST MF hcoverF
  have hM₁Sel : Disjoint ((S ∪ T.biUnion id) ∪ F.biUnion id) (Iall ∪ Yverts) := by
    apply Finset.disjoint_union_left.mpr
    constructor
    · apply Finset.disjoint_union_left.mpr
      constructor
      · apply Finset.disjoint_union_right.mpr
        exact ⟨hIS.symm, (hQS.mono_left hYvertsQ).symm⟩
      · apply Finset.disjoint_union_right.mpr
        exact ⟨(hIallQ.mono_right hTvertsQ).symm, hYvertsT.symm⟩
    · apply Finset.disjoint_union_right.mpr
      exact ⟨(hIallQ.mono_right hFvertsQ).symm, hYvertsF.symm⟩
  obtain ⟨MSEL⟩ := hSel
  have htotal : ((S ∪ T.biUnion id) ∪ F.biUnion id) ∪ (Iall ∪ Yverts) =
      coreVertices Q I ∪ S := by
    ext v
    have hQpart := congrArg (fun X => X.biUnion id) hpartition
    simp only [Finset.union_biUnion] at hQpart
    have hvQ : v ∈ Qverts ↔ v ∈ T.biUnion id ∨ v ∈ F.biUnion id ∨ v ∈ Yverts := by
      change v ∈ Qall.biUnion id ↔ _
      rw [hQpart]
      simp only [Yverts, Finset.mem_union]
      tauto
    simp only [coreVertices, Finset.mem_union]
    change (((v ∈ S ∨ v ∈ T.biUnion id) ∨ v ∈ F.biUnion id) ∨
      (v ∈ Iall ∨ v ∈ Yverts)) ↔ ((v ∈ Iall ∨ v ∈ Qverts) ∨ v ∈ S)
    rw [hvQ]
    tauto
  exact ⟨htotal ▸ unionMatching M₁ MSEL hM₁Sel⟩

/-- General size accounting before any probabilistic bounds are substituted. -/
theorem coreVertices_card_le (Q : Fin 3 → Finset (Finset (Vertex G)))
    (I : Fin 3 → Finset (Vertex G))
    (hlegal : ∀ p T, T ∈ Q p → LegalPair p T) :
    (coreVertices Q I).card ≤
      (∑ p, (I p).card) + ∑ p, 2 * (Q p).card := by
  classical
  have hQ : ((Finset.univ.biUnion Q).biUnion id).card ≤ ∑ p, 2 * (Q p).card := by
    have hrewrite : (Finset.univ.biUnion Q).biUnion id =
        Finset.univ.biUnion (fun p => (Q p).biUnion id) := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
      tauto
    rw [hrewrite]
    calc
      _ ≤ ∑ p, ((Q p).biUnion id).card := Finset.card_biUnion_le
      _ ≤ ∑ p, 2 * (Q p).card := by
        apply Finset.sum_le_sum
        intro p _
        calc
          _ ≤ ∑ T ∈ Q p, T.card := Finset.card_biUnion_le
          _ ≤ ∑ _T ∈ Q p, 2 := Finset.sum_le_sum (fun T hT => legalPair_card_le (hlegal p T hT))
          _ = 2 * (Q p).card := by simp [Nat.mul_comm]
  unfold coreVertices
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_biUnion_le hQ)

omit [AddCommGroup G] in
/-- Inventory containment is inherited separately from the fixed P and Q
reservoirs; it is not hidden in the matching conclusion. -/
theorem coreVertices_inside
    (Q : Fin 3 → Finset (Finset (Vertex G))) (I : Fin 3 → Finset (Vertex G))
    (R : Vertex G → Prop)
    (hI : ∀ p v, v ∈ I p → R v)
    (hQ : ∀ p T, T ∈ Q p → ∀ v, v ∈ T → R v) :
    ∀ v ∈ coreVertices Q I, R v := by
  intro v hv
  rcases Finset.mem_union.mp hv with hvI | hvQ
  · obtain ⟨p, _, hvp⟩ := Finset.mem_biUnion.mp hvI
    exact hI p v hvp
  · obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hvQ
    obtain ⟨p, _, hTp⟩ := Finset.mem_biUnion.mp hT
    exact hQ p T hTp v hvT

theorem coreVertices_support_avoids
    (Q : Fin 3 → Finset (Finset (Vertex G))) (I : Fin 3 → Finset (Vertex G))
    (U : Finset G) (hI : ∀ p, Disjoint (support (I p)) U)
    (hQ : Disjoint (support ((Finset.univ.biUnion Q).biUnion id)) U) :
    Disjoint (support (coreVertices Q I)) U := by
  rw [coreVertices, support_union]
  apply Finset.disjoint_union_left.mpr
  refine ⟨?_, hQ⟩
  rw [support_biUnion]
  exact (Finset.disjoint_biUnion_left _ _ _).mpr (fun p _ => hI p)

/-- A universal core itself is matchable, balanced and has total sum zero. -/
theorem core_properties_of_absorbs {A : Finset (Vertex G)} {capacity : ℕ}
    (hA : AbsorbsUpTo A capacity) :
    Nonempty (Matching A) ∧ Balanced A ∧ (∑ v ∈ A, v.2 = 0) := by
  obtain ⟨M⟩ := hA.matches_empty
  exact ⟨⟨M⟩, matching_balanced M, matching_sum_eq_zero M⟩
end
end EndpointMatching.UniversalCore
