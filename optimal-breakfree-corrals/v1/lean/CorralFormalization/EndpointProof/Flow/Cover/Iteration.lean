import CorralFormalization.EndpointProof.Flow.Cover.PairedInventories

/-!
# Iteration of an actual six-root supplier

The supplier is an explicit premise.  The iteration constructs actual
partial matchings, including every freshness and budget condition, and
closes the last output by the zero-sum invariant.
-/

open scoped Classical BigOperators

namespace EndpointFlow.Cover

open EndpointSelector EndpointSelector.Assembly

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 2048

variable {G : Type*} [CommRing G] [Fintype G]

/-- The search invariant after processing a nonempty subfamily of the original
triple partition. It retains one open triple and at most eighteen additions
per merge, fresh from all original roots, including unprocessed roots. -/
theorem partial_cover_of_partition
    (Q : Vertex G → Prop) (budget : ℕ) (supply : SixRootSupplier Q budget)
    (S : Finset (Vertex G)) {r : ℕ} (B : TriplePartition S r)
    (hScard : S.card = 3*r) (hSne : S.Nonempty)
    (hSnz : ∀ v ∈ S, v.2 ≠ 0) (U : Finset G)
    (hbudget : 2*U.card+20*S.card ≤ budget) :
    ∃ P : PartialCover Q S, OnePerPart P.output ∧ Balanced P.added ∧
      P.added.card ≤ 18*(r-1) ∧
      Disjoint (numericalSupport P.added) (initialForbidden U S) := by
  let F₀ := initialForbidden U S
  have hblockSub (i : Fin r) : B.block i ⊆ S := by
    intro v hv
    rw [← B.union_eq]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩
  have hprocessedSub (s : Finset (Fin r)) : s.biUnion B.block ⊆ S := by
    intro v hv
    obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hv
    exact hblockSub i hvi
  have main : ∀ s : Finset (Fin r), s.Nonempty →
      ∃ P : PartialCover Q (s.biUnion B.block),
        OnePerPart P.output ∧ Balanced P.added ∧
          P.added.card ≤ 18*(s.card-1) ∧
          Disjoint (numericalSupport P.added) F₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro hs; exact False.elim (Finset.not_nonempty_empty hs)
    | @insert j s hjs ih =>
      intro _
      by_cases hs : s.Nonempty
      · obtain ⟨P,hO,hbal,hcard,hfresh⟩ := ih hs
        let X := B.block j
        have hXsub : X ⊆ S := hblockSub j
        have hX : Disjoint X ((s.biUnion B.block) ∪ P.added) := by
          apply Finset.disjoint_union_right.mpr
          constructor
          · apply Finset.disjoint_left.mpr
            intro v hvX hvold
            obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hvold
            have hji : j ≠ i := by intro he; subst i; exact hjs hi
            exact Finset.disjoint_left.mp (B.pairwise hji) hvX hvi
          · apply Finset.disjoint_left.mpr
            intro v hvX hvold
            have hvF : v.2 ∈ F₀ := Finset.mem_union_right _
              (coordinate_mem_numericalSupport (hXsub hvX))
            exact Finset.disjoint_left.mp hfresh (coordinate_mem_numericalSupport hvold) hvF
        have hOX : Disjoint P.output X := hX.symm.mono_left P.output_subset
        have hOnz : ∀ v ∈ P.output, v.2 ≠ 0 := by
          intro v hv
          rcases Finset.mem_union.mp (P.output_subset hv) with hv | hv
          · exact hSnz v (hprocessedSub s hv)
          · exact P.added_nonzero v hv
        let Fnext := F₀ ∪ numericalSupport P.added
        have hsc : s.card ≤ r := by simpa using Finset.card_le_univ s
        have haddedSize : P.added.card ≤ 6*S.card := by omega
        have hFnext : Fnext.card ≤ budget := by
          have h₀ := initialForbidden_card_le U S
          have h₁ := numericalSupport_paired_card_le P.added P.added_paired
          have h₂ := Finset.card_union_le F₀ (numericalSupport P.added)
          change (F₀ ∪ numericalSupport P.added).card ≤ _
          change F₀.card ≤ 2*U.card+2*S.card at h₀
          omega
        obtain ⟨A⟩ := supply P.output X Fnext hO (B.onePerPart j) hOX hOnz
          (fun v hv ↦ hSnz v (hXsub hv)) hFnext
        have hA : Disjoint A.added (((s.biUnion B.block) ∪ P.added) ∪ X) := by
          apply Finset.disjoint_left.mpr
          intro v hvA hvold
          have hvF : v.2 ∈ Fnext := by
            rcases Finset.mem_union.mp hvold with hvold | hvX
            · rcases Finset.mem_union.mp hvold with hvS | hvP
              · exact Finset.mem_union_left _ (Finset.mem_union_right _
                  (coordinate_mem_numericalSupport (hprocessedSub s hvS)))
              · exact Finset.mem_union_right _ (coordinate_mem_numericalSupport hvP)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (coordinate_mem_numericalSupport (hXsub hvX)))
          exact Finset.disjoint_left.mp A.avoids (coordinate_mem_numericalSupport hvA) hvF
        let Pnext := P.extend hX hA A.output_subset A.added_Q A.added_paired
          A.added_nonzero A.matching
        have hPA : Disjoint P.added A.added := by
          exact (hA.mono_right
            (Finset.subset_union_right.trans Finset.subset_union_left)).symm
        have hnewbal : Balanced Pnext.added := balanced_union hbal A.added_balanced hPA
        have hnewcard : Pnext.added.card ≤ 18*((insert j s).card-1) := by
          have hc := Finset.card_union_le P.added A.added
          have hAc := A.added_card_le
          have hspos := Finset.card_pos.mpr hs
          rw [Finset.card_insert_of_notMem hjs]
          change (P.added ∪ A.added).card ≤ _
          omega
        have hnewfresh : Disjoint (numericalSupport Pnext.added) F₀ := by
          change Disjoint (numericalSupport (P.added ∪ A.added)) F₀
          rw [numericalSupport_union]
          exact Finset.disjoint_union_left.mpr
            ⟨hfresh,A.avoids.mono_right Finset.subset_union_left⟩
        have hset : (s.biUnion B.block) ∪ X = (insert j s).biUnion B.block := by
          rw [Finset.biUnion_insert]
          exact Finset.union_comm _ _
        have hout : ∃ P : PartialCover Q ((s.biUnion B.block) ∪ X),
            OnePerPart P.output ∧ Balanced P.added ∧
              P.added.card ≤ 18*((insert j s).card-1) ∧
              Disjoint (numericalSupport P.added) F₀ :=
          ⟨Pnext,A.output_onePerPart,hnewbal,hnewcard,hnewfresh⟩
        exact Eq.mp (congrArg (fun W ↦ ∃ P : PartialCover Q W,
          OnePerPart P.output ∧ Balanced P.added ∧
            P.added.card ≤ 18*((insert j s).card-1) ∧
            Disjoint (numericalSupport P.added) F₀) hset) hout
      · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        have hset : B.block j = (insert j (∅ : Finset (Fin r))).biUnion B.block := by simp
        have hout : ∃ P : PartialCover Q (B.block j),
            OnePerPart P.output ∧ Balanced P.added ∧
              P.added.card ≤ 18*((insert j (∅ : Finset (Fin r))).card-1) ∧
              Disjoint (numericalSupport P.added) F₀ := by
          refine ⟨PartialCover.initial Q (B.block j),B.onePerPart j,balanced_empty,?_,?_⟩
          · simp [PartialCover.initial]
          · simp [PartialCover.initial,numericalSupport]
        exact Eq.mp (congrArg (fun W ↦ ∃ P : PartialCover Q W,
          OnePerPart P.output ∧ Balanced P.added ∧
            P.added.card ≤ 18*((insert j (∅ : Finset (Fin r))).card-1) ∧
            Disjoint (numericalSupport P.added) F₀) hset) hout
  have hrpos : 0 < r := by
    have hpos := Finset.card_pos.mpr hSne
    omega
  have huniv : (Finset.univ : Finset (Fin r)).Nonempty := Finset.card_pos.mp (by simpa using hrpos)
  have hfinal := main Finset.univ huniv
  have hfinal' : ∃ P : PartialCover Q (Finset.univ.biUnion B.block),
      OnePerPart P.output ∧ Balanced P.added ∧ P.added.card ≤ 18*(r-1) ∧
      Disjoint (numericalSupport P.added) F₀ := by
    simpa only [Finset.card_univ,Fintype.card_fin] using hfinal
  exact Eq.mp (congrArg (fun W ↦ ∃ P : PartialCover Q W,
    OnePerPart P.output ∧ Balanced P.added ∧ P.added.card ≤ 18*(r-1) ∧
    Disjoint (numericalSupport P.added) F₀) B.union_eq) hfinal'

/-- The full paired-cover output, including exact inverse-pair inventory. -/
structure PairedCoverResult (Q : Vertex G → Prop) (S : Finset (Vertex G)) (U : Finset G) where
  added : Finset (Vertex G)
  pairsPerPart : ℕ
  added_Q : ∀ v ∈ added, Q v
  added_paired : ∀ v ∈ added, (v.1,-v.2) ∈ added
  added_nonzero : ∀ v ∈ added, v.2 ≠ 0
  added_balanced : Balanced added
  original_added_disjoint : Disjoint S added
  avoids : Disjoint (numericalSupport added) (numericalClosure (U ∪ S.image Prod.snd))
  added_card_le : added.card ≤ 6*S.card
  part_card : ∀ p : Fin 3, (partSlice added p).card = 2*pairsPerPart
  pairs_le : pairsPerPart ≤ S.card
  total_card : added.card = 6*pairsPerPart
  matching : MatchingOn (S ∪ added)

/-- The empty input needs no supplier, reservoir vertex or flow. -/
def pairedCover_empty (Q : Vertex G → Prop) (U : Finset G) :
    PairedCoverResult Q ∅ U where
  added := ∅
  pairsPerPart := 0
  added_Q := by simp
  added_paired := by simp
  added_nonzero := by simp
  added_balanced := balanced_empty
  original_added_disjoint := by simp
  avoids := by simp [numericalSupport]
  added_card_le := by simp
  part_card := by simp [partSlice]
  pairs_le := by simp
  total_card := by simp
  matching := by simpa using (MatchingOn.empty (G := G))

/-- An input that is already one zero-sum triple needs no six-root query. -/
def pairedCover_oneTriple (hodd : Odd (Fintype.card G))
    (Q : Vertex G → Prop) (S : Finset (Vertex G)) (U : Finset G)
    (hone : OnePerPart S) (hsum : ∑ v ∈ S, v.2 = 0) : PairedCoverResult Q S U where
  added := ∅
  pairsPerPart := 0
  added_Q := by simp
  added_paired := by simp
  added_nonzero := by simp
  added_balanced := balanced_empty
  original_added_disjoint := by simp
  avoids := by simp [numericalSupport]
  added_card_le := by simp
  part_card := by simp [partSlice]
  pairs_le := by simp
  total_card := by simp
  matching := by simpa [PartialCover.initial] using
    (PartialCover.initial Q S).close_of_zero_sum hodd hsum hone

/-- paired cover, conditional only on the explicitly named six-root supplier.
The supplier is before S and U; the original roots may intersect U. -/
theorem paired_cover_of_sixRootSupplier
    (hodd : Odd (Fintype.card G)) (Q : Vertex G → Prop) (budget : ℕ)
    (supply : SixRootSupplier Q budget) (S : Finset (Vertex G))
    (hb : Balanced S) (hnz : ∀ v ∈ S, v.2 ≠ 0)
    (hsum : ∑ v ∈ S, v.2 = 0) (U : Finset G)
    (hbudget : 2*U.card+20*S.card ≤ budget) : Nonempty (PairedCoverResult Q S U) := by
  by_cases he : S = ∅
  · subst S
    exact ⟨pairedCover_empty Q U⟩
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  let B := balancedTriplePartition S hb
  have hScard := balanced_card S hb
  obtain ⟨P,hO,hbal,hcard,hfresh⟩ := partial_cover_of_partition Q budget supply S B
    hScard hSne hnz U hbudget
  have hsize : P.added.card ≤ 6*S.card := by omega
  obtain ⟨m,hm,hml⟩ := paired_balanced_pair_count hodd P.added hbal
    P.added_paired P.added_nonzero S.card hsize
  refine ⟨{
    added := P.added
    pairsPerPart := m
    added_Q := P.added_Q
    added_paired := P.added_paired
    added_nonzero := P.added_nonzero
    added_balanced := hbal
    original_added_disjoint := P.original_added_disjoint
    avoids := by simpa only [initialForbidden_eq] using hfresh
    added_card_le := hsize
    part_card := hm
    pairs_le := hml
    total_card := by have hh := balanced_card P.added hbal; have h0 := hm 0; omega
    matching := P.close_of_zero_sum hodd hsum hO }⟩

end
end EndpointFlow.Cover
