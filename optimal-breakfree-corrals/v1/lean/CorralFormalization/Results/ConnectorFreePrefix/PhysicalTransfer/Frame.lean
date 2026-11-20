import CorralFormalization.Results.ConnectorFreePrefix.PhysicalTransfer.Coordinates
import CorralFormalization.DiversityCompletion.TailInvariance

/-!
# Positive physical frames for the literal connector-free H4 pools

This file derives occupancy, physical cyclic palettes, and an absolute
unlabelled decoder from one positive gap frame and one physical baseline.
Those inputs are deliberately explicit; no terrace or frame existence is
asserted here.  `BodyFrame.lean` constructs them from narrow source-body data.
-/

namespace CorralFormalization.LatinCompletion.ConnectorFreePhysical

open scoped BigOperators
open LatinTransfer

/-- Positive one-winding gap geometry, with the actual H4 sites as its
locations.  The `location` equation is derived from L14 in `BodyFrame`.
There is no partition, Latin injectivity, or asymmetric-orbit field. -/
structure Frame (h n : ℕ) {r : ℕ} [NeZero r] (D : Coordinates r) where
  pieces : ZMod h → List (Piece (Cell r))
  origin : ZMod h → ℕ
  fixed_positive : ∀ q d, Piece.fixed d ∈ pieces q → 0 < d
  cells_complete : ∀ q, (cells (pieces q)).Perm (Finset.univ : Finset (Cell r)).toList
  winding : ∀ q, ((pieces q).map (Piece.weight D.cellA D.cellB)).sum = h*n
  location : ∀ q i p, (i,p) ∈ locatedCells D.cellA D.cellB (pieces q) → ∀ s : Fin r,
    ((origin q+(p+D.cellA i+s.val) : ℕ) : ZMod (h*n)) =
      D.site h n (q+D.offset h i.1,i.2,s)

namespace Frame

variable {h n r : ℕ} [NeZero r] {D : Coordinates r} (G : Frame h n D)

def row (L : Family h r) (q : ZMod h) : Finset (ZMod (h*n)) :=
  physicalOffsets (h*n) (G.origin q)
    (properPrefixSites (word D.cellA D.cellB (D.choice L q) (G.pieces q)))

def fixedRow (q : ZMod h) : Finset (ZMod (h*n)) :=
  physicalOffsets (h*n) (G.origin q) (fixedOffsets D.cellA D.cellB (G.pieces q))

theorem cellA_positive (hr : 3 ≤ r) (i : Cell r) : 0 < D.cellA i := D.a_positive hr i.1

theorem choice_lt (hr : 3 ≤ r) (L : Family h r) (q : ZMod h) (i : Cell r) :
    D.choice L q i < D.cellB i := by
  have hs := ((L (q+D.offset h i.1)).entry i.1 i.2).isLt
  dsimp [Coordinates.cellB,Coordinates.b]
  dsimp [Coordinates.choice]
  nlinarith

theorem word_positive (hr : 3 ≤ r) (L : Family h r) (q : ZMod h) :
    ∀ x ∈ word D.cellA D.cellB (D.choice L q) (G.pieces q), 0 < x :=
  LatinCompletion.word_positive D.cellA D.cellB (D.choice L q) (G.pieces q)
    (G.fixed_positive q) (cellA_positive hr) (choice_lt hr L q)

theorem word_winding (hr : 3 ≤ r) (L : Family h r) (q : ZMod h) :
    (word D.cellA D.cellB (D.choice L q) (G.pieces q)).sum = h*n :=
  (word_sum D.cellA D.cellB (D.choice L q) (G.pieces q)
    (fun i => (choice_lt hr L q i).le)).trans (G.winding q)

theorem movingRow_eq (L : Family h r) (q : ZMod h) :
    physicalOffsets (h*n) (G.origin q)
      (movingOffsets D.cellA D.cellB (D.choice L q) (G.pieces q)) =
      movingRow (D.site h n) L (D.offset h) q := by
  ext x
  rw [mem_movingRow]
  constructor
  · intro hx
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hx
    have hz' := List.mem_toFinset.mp hz
    rw [movingOffsets_locations] at hz'
    obtain ⟨⟨i,p⟩,hip,rfl⟩ := List.mem_map.mp hz'
    refine ⟨i.1,i.2,?_⟩
    exact (G.location q i p hip ((L (q+D.offset h i.1)).entry i.1 i.2)).symm.trans he
  · rintro ⟨j,t,he⟩
    have hi : (j,t) ∈ cells (G.pieces q) :=
      (G.cells_complete q).mem_iff.mpr (by simp)
    rw [← locatedCells_indices D.cellA D.cellB] at hi
    obtain ⟨⟨i,p⟩,hip,hi⟩ := List.mem_map.mp hi
    change i=(j,t) at hi
    subst i
    apply Finset.mem_image.mpr
    refine ⟨p+D.cellA (j,t)+D.choice L q (j,t),?_,?_⟩
    · apply List.mem_toFinset.mpr
      rw [movingOffsets_locations]
      exact List.mem_map.mpr ⟨((j,t),p),hip,rfl⟩
    · exact (G.location q (j,t) p hip ((L (q+D.offset h j)).entry j t)).trans he

theorem row_split (hr : 3 ≤ r) (L : Family h r) (q : ZMod h) :
    G.row L q=G.fixedRow q ∪ movingRow (D.site h n) L (D.offset h) q := by
  rw [row,physical_prefix_split _ _ _ _ _ _
    (fun i => (choice_lt hr L q i).le),G.movingRow_eq]
  rfl

theorem cell_palette (L : Family h r) (q : ZMod h) :
    ((cells (G.pieces q)).map (fun i =>
      ({D.cellA i+D.choice L q i} : Multiset ℕ)+{D.cellB i-D.choice L q i})).sum =
      rowIncidentPalette L (D.offset h) D.a D.b q := by
  let f : Cell r → Multiset ℕ := fun i =>
    {D.cellA i+D.choice L q i}+{D.cellB i-D.choice L q i}
  calc
    _ = (((Finset.univ : Finset (Cell r)).toList).map f).sum :=
      ((G.cells_complete q).map f).sum_eq
    _ = ∑ i : Cell r, f i := by
      rw [← List.sum_toFinset f (Finset.nodup_toList _)]
      simp
    _ = _ := by
      simp only [f,Coordinates.cellA,Coordinates.cellB,Coordinates.choice,
        rowIncidentPalette,block,Fintype.sum_prod_type,Finset.sum_add_distrib]

/-- Actual physical cyclic edges, including the wrap, follow from positive
local blocks and winding.  They are not a supplied edge certificate. -/
theorem inventory [NeZero (h*n)] (hr : 3 ≤ r) (L : Family h r) (q : ZMod h) :
    finiteCyclicGapInventory (h*n) ((G.row L q).image ZMod.val) =
      unchanged (G.pieces q)+rowIncidentPalette L (D.offset h) D.a D.b q := by
  rw [row,physical_frame_inventory _ _ _ _ _ _ (NeZero.pos _) (G.fixed_positive q)
    (cellA_positive hr) (choice_lt hr L q) (G.winding q),G.cell_palette]

theorem fixed_word_positive (hr : 3 ≤ r) (q : ZMod h) :
    ∀ x ∈ (G.pieces q).map (Piece.weight D.cellA D.cellB), 0 < x := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  cases p with
  | fixed d => exact G.fixed_positive q d hp
  | cell i => have := cellA_positive (D := D) hr i; change 0 < D.cellA i+D.cellB i; omega

theorem fixedRow_card (hr : 3 ≤ r) (q : ZMod h) :
    (G.fixedRow q).card=(G.pieces q).length := by
  rw [fixedRow,fixedOffsets,physical_prefix_card _ _ _ (G.fixed_word_positive hr q)
    (G.winding q),List.length_map]

theorem row_card (hr : 3 ≤ r) (L : Family h r) (q : ZMod h) :
    (G.row L q).card=(G.pieces q).length+r*r := by
  rw [row,physical_prefix_card _ _ _ (G.word_positive hr L q)
    (G.word_winding hr L q),word_length]
  have hc := (G.cells_complete q).length_eq
  simpa using congrArg ((G.pieces q).length+·) hc

theorem fixed_moving_disjoint [NeZero h] (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (L : Family h r) (q : ZMod h) :
    Disjoint (G.fixedRow q) (movingRow (D.site h n) L (D.offset h) q) := by
  apply Finset.card_union_eq_card_add_card.mp
  rw [← G.row_split hr L q,G.row_card hr L q,G.fixedRow_card hr q,
    LatinTransfer.movingRow_card _ (D.site_injective hr hn)]

/-- A baseline is exactly the unmodified physical partition and its actual
gap inventory.  It concerns one Latin family, not all possible replacements. -/
structure FullBaseline where
  latin : Family h r
  partition : ∀ x : ZMod (h*n), ∃! q, x ∈ G.row latin q
  palette : ∀ q, finiteCyclicGapInventory (h*n) ((G.row latin q).image ZMod.val) =
    Multiset.ofList (fullGapList n)

theorem baseline_disjoint (B : G.FullBaseline) {q t : ZMod h} (hqt : q ≠ t) :
    Disjoint (G.row B.latin q) (G.row B.latin t) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  obtain ⟨owner,_,huniq⟩ := B.partition x
  exact hqt ((huniq q hx).trans (huniq t ht).symm)

theorem fixedRows_disjoint (hr : 3 ≤ r) (B : G.FullBaseline)
    {q t : ZMod h} (hqt : q ≠ t) : Disjoint (G.fixedRow q) (G.fixedRow t) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  apply Finset.disjoint_left.mp (G.baseline_disjoint B hqt)
  · rw [G.row_split hr]; exact Finset.mem_union_left _ hx
  · rw [G.row_split hr]; exact Finset.mem_union_left _ ht

theorem fixedRows_avoid [NeZero h] (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (B : G.FullBaseline) (q : ZMod h) (c : ZMod h × Fin r × Fin r) :
    D.site h n c ∉ G.fixedRow q := by
  intro hfixed
  obtain ⟨t,ht⟩ := (movingRows_cover (D.site h n) B.latin (D.offset h) (D.site h n c)).mpr ⟨c,rfl⟩
  have hq : D.site h n c ∈ G.row B.latin q := by
    rw [G.row_split hr]; exact Finset.mem_union_left _ hfixed
  have htm : D.site h n c ∈ G.row B.latin t := by
    rw [G.row_split hr]; exact Finset.mem_union_right _ ht
  obtain ⟨owner,_,huniq⟩ := B.partition (D.site h n c)
  have hqt : q=t := (huniq q hq).trans (huniq t htm).symm
  subst t
  exact Finset.disjoint_left.mp (G.fixed_moving_disjoint hr hn B.latin q) hfixed ht

theorem fixedRows_cover (hr : 3 ≤ r) (B : G.FullBaseline) (x : ZMod (h*n))
    (hx : ¬ ∃ c, D.site h n c=x) : ∃ q, x ∈ G.fixedRow q := by
  obtain ⟨q,hq,_⟩ := B.partition x
  rw [G.row_split hr] at hq
  rcases Finset.mem_union.mp hq with hf | hm
  · exact ⟨q,hf⟩
  · exact False.elim (hx ((movingRows_cover (D.site h n) B.latin (D.offset h) x).mp ⟨q,hm⟩))

theorem origin_mem_fixedRow [NeZero (h*n)] (q : ZMod h) :
    (G.origin q : ZMod (h*n)) ∈ G.fixedRow q := by
  have hp : G.pieces q ≠ [] := by
    intro he
    have hw : 0=h*n := by simpa only [he,List.map_nil,List.sum_nil] using G.winding q
    exact (NeZero.ne (h*n)) hw.symm
  have hlen : 0 < ((G.pieces q).map (Piece.weight D.cellA D.cellB)).length := by
    rw [List.length_map]; exact List.length_pos_iff.mpr hp
  apply Finset.mem_image.mpr
  refine ⟨0,List.mem_toFinset.mpr ?_,by simp⟩
  exact (mem_properPrefixSites_iff _ 0).mpr ⟨0,hlen,by simp⟩

def skeleton [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (B : G.FullBaseline) : FixedSkeleton (D.site h n) where
  fixed := G.fixedRow
  disjoint := fun _q _t hqt => G.fixedRows_disjoint hr B hqt
  avoids := G.fixedRows_avoid hr hn B
  covers := G.fixedRows_cover hr B
  anchor := fun q => (G.origin q : ZMod (h*n))
  anchor_mem := G.origin_mem_fixedRow

theorem row_eq_transferred [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (B : G.FullBaseline) (L : Family h r) (q : ZMod h) :
    G.row L q=transferredRows (D.site h n) (G.skeleton hr hn B) L (D.offset h) q :=
  G.row_split hr L q

/-- Every physical site still has exactly one owner after simultaneous
Latin reassignment.  This conclusion is derived, not part of the frame. -/
theorem partition [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (B : G.FullBaseline) (L : Family h r) (x : ZMod (h*n)) :
    ∃! q, x ∈ G.row L q := by
  simp_rw [G.row_eq_transferred hr hn B]
  exact transferredRows_full_partition (D.site h n) (D.site_injective hr hn)
    (G.skeleton hr hn B) L (D.offset h) x

/-- Physical H4 membership is exactly the indicated Latin entry.  The
baseline and positive frame are the only global geometric premises. -/
theorem decode [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (hh : r*r ≤ h) (B : G.FullBaseline) (L : Family h r)
    (a : ZMod h) (j t s : Fin r) :
    D.site h n (a,t,s) ∈ G.row L (a-D.offset h j) ↔ (L a).entry j t=s := by
  rw [G.row_eq_transferred hr hn B]
  exact decode_transferredRows (D.site h n) (D.site_injective hr hn) (G.skeleton hr hn B)
    L (D.offset h) (D.offset_injective hh) a j t s

def edgeCertificate [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (B : G.FullBaseline) (L : Family h r) :
    CyclicEdgeCertificate (D.site h n) (G.skeleton hr hn B) L (D.offset h) D.a D.b where
  unchanged := fun q => unchanged (G.pieces q)
  decomposition := by
    intro q
    change finiteCyclicGapInventory (h*n)
      ((transferredRows (D.site h n) (G.skeleton hr hn B) L (D.offset h)
        (q.val : ZMod h)).image ZMod.val)=_
    rw [← G.row_eq_transferred hr hn B]
    exact G.inventory hr L (q.val : ZMod h)
  baseline := by
    intro q
    have hp := G.inventory hr B.latin q
    rw [rowIncidentPalette_eq] at hp
    exact hp.symm.trans (B.palette q)

def completed [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r) (hlarge : 200*r*r ≤ n)
    (B : G.FullBaseline) (hn : n=2*h-1) (L : Family h r) : CorralRows h n :=
  toCorralRows (D.site h n) (D.site_injective hr hlarge) (G.skeleton hr hlarge B)
    L (D.offset h) D.a D.b (optimal_width (NeZero.pos h) hn)
    (G.edgeCertificate hr hlarge B L)

theorem completed_sites [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r) (hlarge : 200*r*r ≤ n)
    (B : G.FullBaseline) (hn : n=2*h-1) (L : Family h r) (q : Fin h) :
    (G.completed hr hlarge B hn L).sites q=naturalRows (G.row L) q := by
  change naturalRows (transferredRows (D.site h n) (G.skeleton hr hlarge B) L (D.offset h)) q=_
  simp only [naturalRows,← G.row_eq_transferred hr hlarge B]

/-- Unique full occupancy is retained in the actual bounded-natural
`CorralRows` adapter, on the exact original physical width. -/
theorem completed_full_occupancy [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r)
    (hlarge : 200*r*r ≤ n) (B : G.FullBaseline) (hn : n=2*h-1)
    (L : Family h r) (x : ℕ) (hx : x < width n) :
    ∃! q, x ∈ (G.completed hr hlarge B hn L).sites q :=
  toCorralRows_full_occupancy (D.site h n) (D.site_injective hr hlarge)
    (G.skeleton hr hlarge B) L (D.offset h) D.a D.b
    (optimal_width (NeZero.pos h) hn) (G.edgeCertificate hr hlarge B L) x hx

def unlabelled [NeZero h] (L : Family h r) : Finset (Finset (ZMod (h*n))) :=
  Finset.univ.image (G.row L)

theorem unlabelled_injective [NeZero h] [NeZero (h*n)]
    (hr : 3 ≤ r) (hn : 200*r*r ≤ n) (hh : r*r ≤ h) (B : G.FullBaseline) :
    Function.Injective G.unlabelled := by
  have he (L : Family h r) : G.unlabelled L=
      unlabelledPartition (D.site h n) (G.skeleton hr hn B) (D.offset h) L := by
    simp only [unlabelled,unlabelledPartition]
    congr 1
    funext q
    exact G.row_eq_transferred hr hn B L q
  intro L K hLK
  apply unlabelledPartition_injective (D.site h n) (D.site_injective hr hn)
    (G.skeleton hr hn B) (D.offset h) (D.offset_injective hh)
  rw [← he L,← he K]
  exact hLK

end Frame
end CorralFormalization.LatinCompletion.ConnectorFreePhysical
