import CorralFormalization.DiversityCompletion.BaselineFromCorral
import CorralFormalization.DiversityCompletion.FixedGapPositions
import CorralFormalization.DiversityCompletion.WordBridge

namespace CorralFormalization.LatinCompletion

open LatinTransfer PhysicalCorral DiversitySymmetry

/-- Actual tails of any positive one-turn gap word, expressed by the
recursively computed integer prefix positions of its distinguished gaps. -/
theorem gapTails_physicalOffsets {W : ℕ} [NeZero W] (origin : ℕ) (g : List ℕ)
    (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum = W) (hlen : 2 ≤ g.length) (d : ℕ) :
    gapTails (physicalOffsets W origin (properPrefixSites g)) d =
      physicalOffsets W origin (gapOffsets d g) := by
  let : NeZero g.length := ⟨by omega⟩
  have hrow : physicalOffsets W origin (properPrefixSites g) =
      (Motion.rotation (origin : ZMod W)).onRow
        (physicalSites W (properPrefixSites g).toFinset) := by
    simp only [physicalOffsets, Motion.onRow, physicalSites, Finset.image_image,
      Function.comp_def, Motion.act, Nat.cast_add]
  rw [hrow, gapTails_translated_positive_word g rfl hpos hsum hlen (origin : ZMod W) d]
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, he⟩
    apply Finset.mem_image.mpr
    refine ⟨(g.take i.val).sum, List.mem_toFinset.mpr ?_, ?_⟩
    · apply (mem_gapOffsets_iff d g _).mpr
      refine ⟨i.val, i.val_lt, ?_, rfl⟩
      rw [List.getD_eq_getElem g 0 i.val_lt]
      exact hi
    · simpa only [Nat.cast_add] using he
  · intro hx
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hx
    obtain ⟨k, hk, hd, hsumk⟩ := (mem_gapOffsets_iff d g p).mp (List.mem_toFinset.mp hp)
    refine ⟨(k : ZMod g.length), ?_, ?_⟩
    · have hv : (k : ZMod g.length).val = k := ZMod.val_natCast_of_lt hk
      simpa only [hv, List.getD_eq_getElem g 0 hk] using hd
    · have hv : (k : ZMod g.length).val = k := ZMod.val_natCast_of_lt hk
      simpa only [hv, hsumk, Nat.cast_add] using he

namespace PhysicalFrame

variable {h n r : ℕ} [NeZero h] [NeZero (h * n)]

/-- Every potential gap-n tail is now an explicit fixed physical site;
the expression contains no Latin parameter. -/
def tailPositions (G : PhysicalFrame h n r) (q : ZMod h) : Finset (ZMod (h * n)) :=
  physicalOffsets (h * n) (G.origin q) (fixedGapOffsets cellA cellB n (G.pieces q))

omit [NeZero h] in
theorem gap_n_tails (G : PhysicalFrame h n r) (hr : 2 ≤ r)
    (hlarge : 100 * r * r ≤ n) (L : Family h r) (q : ZMod h) :
    gapTails (G.row L q) n = G.tailPositions q := by
  have hclen : (cells (G.pieces q)).length = r * r := by
    simpa using (G.cells_complete q).length_eq
  have hlen : 2 ≤ (word cellA cellB (choice L q) (G.pieces q)).length := by
    rw [word_length, hclen]
    nlinarith
  have hin (i : Cell r) : cellA i + choice L q i ≠ n := by
    rcases local_gap_geometry hr hlarge i.1 i.2
      ((L (q + phaseOffset h r i.1)).entry i.1 i.2) with ⟨_, _, _, _, _, ht, _, _⟩
    exact Nat.ne_of_lt ht
  have hout (i : Cell r) : cellB i - choice L q i ≠ n := by
    rcases local_gap_geometry hr hlarge i.1 i.2
      ((L (q + phaseOffset h r i.1)).entry i.1 i.2) with ⟨_, _, _, _, _, _, _, ht⟩
    exact Nat.ne_of_lt ht
  rw [row, gapTails_physicalOffsets _ _ (G.word_positive hr hlarge L q)
    (G.word_winding hr hlarge L q) hlen n,
    gapOffsets_word_eq_fixed _ _ _ n _ (fun i => (choice_lt hr hlarge L q i).le) hin hout]
  rfl

omit [NeZero h] in
theorem gap_n_tails_invariant (G : PhysicalFrame h n r) (hr : 2 ≤ r)
    (hlarge : 100 * r * r ≤ n) (L K : Family h r) (q : ZMod h) :
    gapTails (G.row L q) n = gapTails (G.row K q) n := by
  rw [G.gap_n_tails hr hlarge L q, G.gap_n_tails hr hlarge K q]

def allTailPositions (G : PhysicalFrame h n r) : Finset (ZMod (h * n)) :=
  Finset.univ.biUnion G.tailPositions

/-- The actual tail set of the unordered physical family is computed
without any additional tail-invariance premise. -/
theorem actual_family_tails (G : PhysicalFrame h n r) (hr : 2 ≤ r)
    (hlarge : 100 * r * r ≤ n) (L : Family h r) :
    (G.unlabelled L).biUnion (fun R => gapTails R n) = G.allTailPositions := by
  simp only [unlabelled, Finset.image_biUnion, allTailPositions]
  apply Finset.biUnion_congr rfl
  intro q _
  exact G.gap_n_tails hr hlarge L q

omit [NeZero h] in
theorem tailPositions_singleton (G : PhysicalFrame h n r) (hr : 2 ≤ r)
    (hlarge : 100 * r * r ≤ n) (T : FullBaseline G) (q : ZMod h) :
    ∃ x : ZMod (h * n), G.tailPositions q = {x} := by
  rw [← G.gap_n_tails hr hlarge T.latin q]
  apply gapTails_singleton_of_finiteCyclicGapInventory n (G.row T.latin q)
    (by nlinarith) (T.palette q) n (by nlinarith) le_rfl

omit [NeZero h] in
theorem tailPositions_disjoint (G : PhysicalFrame h n r) (hr : 2 ≤ r)
    (hlarge : 100 * r * r ≤ n) (T : FullBaseline G) {q t : ZMod h} (hqt : q ≠ t) :
    Disjoint (G.tailPositions q) (G.tailPositions t) := by
  apply Finset.disjoint_left.mpr
  intro x hq ht
  rw [← G.gap_n_tails hr hlarge T.latin q] at hq
  rw [← G.gap_n_tails hr hlarge T.latin t] at ht
  obtain ⟨y, hxy, _⟩ := (mem_gapTails _ _ _).mp hq
  obtain ⟨z, hxz, _⟩ := (mem_gapTails _ _ _).mp ht
  exact Finset.disjoint_left.mp (G.baseline_disjoint T hqt) hxy.1 hxz.1

theorem allTailPositions_card (G : PhysicalFrame h n r) (hr : 2 ≤ r)
    (hlarge : 100 * r * r ≤ n) (T : FullBaseline G) : G.allTailPositions.card = h := by
  rw [allTailPositions, Finset.card_biUnion]
  · have hc (q : ZMod h) : (G.tailPositions q).card = 1 := by
      obtain ⟨x, hx⟩ := G.tailPositions_singleton hr hlarge T q
      simp [hx]
    simp_rw [hc]
    simp [ZMod.card]
  · intro q _ t _ hqt
    exact G.tailPositions_disjoint hr hlarge T hqt

end PhysicalFrame

end CorralFormalization.LatinCompletion
