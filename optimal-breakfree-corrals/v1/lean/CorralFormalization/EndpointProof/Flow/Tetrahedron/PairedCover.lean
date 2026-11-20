import CorralFormalization.EndpointProof.Flow.Tetrahedron.Construction
import CorralFormalization.EndpointProof.Flow.Cover.Iteration
import CorralFormalization.EndpointProof.Matching.UniversalCore.PairedCoverInventory

open scoped Classical BigOperators
namespace EndpointFlow.Cover
open EndpointSelector EndpointSelector.Assembly
open EndpointMatching.Tetrahedron
open EndpointMatching.UniversalCore
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 2048
variable {G : Type*} [CommRing G] [Fintype G]

def matchingOn_of_additive {S : Finset (Vertex G)}
    (M : EndpointFlow.AbelianTransport.Matching S) : MatchingOn S where
  edges := M.edges
  valid := M.valid
  disjoint := M.disjoint
  cover := M.cover

theorem fourPair_partial_cover_of_partition
    (Q : Vertex G → Prop) (budget : ℕ) (supply : FourPairSupplier Q budget)
    (S : Finset (Vertex G)) {r : ℕ} (B : TriplePartition S r)
    (hScard : S.card = 3*r) (hSne : S.Nonempty)
    (hSnz : ∀ v ∈ S, v.2 ≠ 0) (U : Finset G)
    (hbudget : 2*U.card+20*S.card ≤ budget) :
    ∃ P : PartialCover Q S, OnePerPart P.output ∧ Balanced P.added ∧
      P.added.card = 24*(r-1) ∧
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
          P.added.card = 24*(s.card-1) ∧
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
        have haddedSize : P.added.card ≤ 8*S.card := by omega
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
          A.added_nonzero (matchingOn_of_additive A.matching)
        have hPA : Disjoint P.added A.added := by
          exact (hA.mono_right
            (Finset.subset_union_right.trans Finset.subset_union_left)).symm
        have hAbal : Balanced A.added := by
          intro p
          change (EndpointFlow.AbelianTransport.slice A.added p).card =
            (EndpointFlow.AbelianTransport.slice A.added 0).card
          rw [A.part_card p, A.part_card 0]
        have hnewbal : Balanced Pnext.added := balanced_union hbal hAbal hPA
        have hnewcard : Pnext.added.card = 24*((insert j s).card-1) := by
          have hc := Finset.card_union_of_disjoint hPA
          have hAc := A.added_card
          have hspos := Finset.card_pos.mpr hs
          rw [Finset.card_insert_of_notMem hjs]
          change (P.added ∪ A.added).card = _
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
              P.added.card = 24*((insert j s).card-1) ∧
              Disjoint (numericalSupport P.added) F₀ :=
          ⟨Pnext,A.output_onePerPart,hnewbal,hnewcard,hnewfresh⟩
        exact Eq.mp (congrArg (fun W ↦ ∃ P : PartialCover Q W,
          OnePerPart P.output ∧ Balanced P.added ∧
            P.added.card = 24*((insert j s).card-1) ∧
            Disjoint (numericalSupport P.added) F₀) hset) hout
      · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        have hset : B.block j = (insert j (∅ : Finset (Fin r))).biUnion B.block := by simp
        have hout : ∃ P : PartialCover Q (B.block j),
            OnePerPart P.output ∧ Balanced P.added ∧
              P.added.card = 24*((insert j (∅ : Finset (Fin r))).card-1) ∧
              Disjoint (numericalSupport P.added) F₀ := by
          refine ⟨PartialCover.initial Q (B.block j),B.onePerPart j,balanced_empty,?_,?_⟩
          · simp [PartialCover.initial]
          · simp [PartialCover.initial,numericalSupport]
        exact Eq.mp (congrArg (fun W ↦ ∃ P : PartialCover Q W,
          OnePerPart P.output ∧ Balanced P.added ∧
            P.added.card = 24*((insert j (∅ : Finset (Fin r))).card-1) ∧
            Disjoint (numericalSupport P.added) F₀) hset) hout
  have hrpos : 0 < r := by
    have hpos := Finset.card_pos.mpr hSne
    omega
  have huniv : (Finset.univ : Finset (Fin r)).Nonempty := Finset.card_pos.mp (by simpa using hrpos)
  have hfinal := main Finset.univ huniv
  have hfinal' : ∃ P : PartialCover Q (Finset.univ.biUnion B.block),
      OnePerPart P.output ∧ Balanced P.added ∧ P.added.card = 24*(r-1) ∧
      Disjoint (numericalSupport P.added) F₀ := by
    simpa only [Finset.card_univ,Fintype.card_fin] using hfinal
  exact Eq.mp (congrArg (fun W ↦ ∃ P : PartialCover Q W,
    OnePerPart P.output ∧ Balanced P.added ∧ P.added.card = 24*(r-1) ∧
    Disjoint (numericalSupport P.added) F₀) B.union_eq) hfinal'


/-- Iteration of the 24-vertex merge gives the four-thirds cover.
The uniform merge supplier is a premise, not a sampled probability theorem. -/
theorem fourThirds_cover_of_fourPairSupplier
    (hodd : Odd (Fintype.card G)) (Q : Vertex G → Prop) (budget : ℕ)
    (supply : FourPairSupplier Q budget) (S : Finset (Vertex G))
    (hb : Balanced S) (hnz : ∀ v ∈ S, v.2 ≠ 0)
    (hsum : ∑ v ∈ S, v.2 = 0) (U : Finset G)
    (hbudget : 2*U.card+20*S.card ≤ budget) :
    ∃ C : FourThirdsPairedCover Q S U,
      C.pairsPerPart = 4 * ((partSlice S 0).card - 1) := by
  by_cases he : S = ∅
  · subst S
    refine ⟨{
      added := ∅
      pairsPerPart := 0
      added_Q := by simp
      added_paired := by simp
      added_nonzero := by simp
      avoids := by simp [EndpointFlow.AbelianTransport.support]
      part_card := by simp [EndpointFlow.AbelianTransport.slice]
      pair_bound := by simp
      matching := ?_ }, ?_⟩
    · exact EndpointMatching.AbsorptionAssembly.emptyMatching
    · simp [partSlice]
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  let B := balancedTriplePartition S hb
  have hScard := balanced_card S hb
  obtain ⟨P,hO,hbal,hcard,hfresh⟩ := fourPair_partial_cover_of_partition Q budget supply S B
    hScard hSne hnz U hbudget
  have hsize : P.added.card ≤ 8*S.card := by omega
  obtain ⟨m, hm0⟩ := paired_part_card_even hodd P.added P.added_paired P.added_nonzero 0
  have hm (p : Fin 3) : (partSlice P.added p).card = 2*m := by
    have hp := hbal p
    omega
  have htotal : P.added.card = 6*m := by
    have hh := balanced_card P.added hbal
    have hp := hm 0
    omega
  have hmbound : 3*m ≤ 4*S.card := by omega
  have hexact : m = 4 * ((partSlice S 0).card - 1) := by omega
  refine ⟨{
    added := P.added
    pairsPerPart := m
    added_Q := P.added_Q
    added_paired := P.added_paired
    added_nonzero := P.added_nonzero
    avoids := ?_
    part_card := hm
    pair_bound := hmbound
    matching := EndpointFlow.AbelianTransport.matchingOfRing (P.close_of_zero_sum hodd hsum hO)
  }, ?_⟩
  · apply hfresh.mono_right
    intro x hx
    simp only [EndpointFlow.AbelianTransport.support, numericalSupport,
      initialForbidden, numericalClosure, Finset.mem_union] at hx ⊢
    tauto
  · exact hexact

theorem fourThirdsCovers_of_fourPairSupplier
    (hodd : Odd (Fintype.card G)) (Q : Vertex G → Prop) (budget : ℕ)
    (supply : FourPairSupplier Q budget) : FourThirdsCoversAvailable Q budget := by
  intro S hb hnz hsum U hbudget
  obtain ⟨C, _⟩ := fourThirds_cover_of_fourPairSupplier hodd Q budget supply S hb hnz hsum U hbudget
  exact ⟨C⟩

end
end EndpointFlow.Cover

namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
open EndpointMatching.UniversalCore
noncomputable section

/-- The same deterministic four-pair iteration applies to any finite
abelian group, using a compatible ring internally and retaining its original
additive operation. No probabilistic supplier is asserted here. -/
theorem fourThirdsCovers_of_fourPairSupplier_abelian
    (G : Type*) [ft : Fintype G] (A : AddCommGroup G)
    (hodd : Odd (Fintype.card G)) (Q : Vertex G → Prop) (budget : ℕ)
    (supply : @FourPairSupplier G A Q budget) :
    @FourThirdsCoversAvailable G A Q budget := by
  obtain ⟨ring,hcompat⟩ := exists_compatible_commRing G
  cases hcompat
  exact @EndpointFlow.Cover.fourThirdsCovers_of_fourPairSupplier G ring ft hodd Q budget supply

/-- The paper's exact 4(r−1) pair count, over the original finite abelian
additive group and under the same explicit merge-supply premise. -/
theorem fourThirds_cover_exact_abelian
    {G : Type*} [A : AddCommGroup G] [ft : Fintype G]
    (hodd : Odd (Fintype.card G)) (Q : Vertex G → Prop) (budget : ℕ)
    (supply : FourPairSupplier Q budget) (S : Finset (Vertex G))
    (hb : Balanced S) (hnz : ∀ v ∈ S, v.2 ≠ 0)
    (hsum : ∑ v ∈ S, v.2 = 0) (U : Finset G)
    (hbudget : 2*U.card + 20*S.card ≤ budget) :
    ∃ C : FourThirdsPairedCover Q S U,
      C.pairsPerPart = 4 * ((slice S 0).card - 1) := by
  obtain ⟨ring,hcompat⟩ := exists_compatible_commRing G
  cases hcompat
  exact @EndpointFlow.Cover.fourThirds_cover_of_fourPairSupplier G ring ft
    hodd Q budget supply S hb hnz hsum U hbudget

end
end EndpointMatching.Tetrahedron
