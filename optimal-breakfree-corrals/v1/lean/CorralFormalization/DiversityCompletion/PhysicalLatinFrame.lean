import CorralFormalization.DiversityCompletion.CyclicReplacement

namespace CorralFormalization.LatinCompletion

open scoped BigOperators
open LatinTransfer

abbrev Cell (r : ℕ) := Fin r × Fin r

def cellA {r : ℕ} (i : Cell r) : ℕ := incomingBase i.1
def cellB {r : ℕ} (i : Cell r) : ℕ := outgoingBase i.1

def choice {h r : ℕ} (L : Family h r) (q : ZMod h) (i : Cell r) : ℕ :=
  ((L (q + phaseOffset h r i.1)).entry i.1 i.2).val

/-- A concrete one-turn local gap-word frame. Fixed pieces include every
tile-cut/repair gap. Every Latin cell occurs exactly once in each row, and
its actual lifted centre coordinates are connectorPrefixCenterSite. These are local coordinates,
strict positivity and total length; no post-replacement gap inventory or
Latin injectivity is assumed. Existence of such a frame is separate. -/
structure PhysicalFrame (h n r : ℕ) where
  pieces : ZMod h → List (Piece (Cell r))
  origin : ZMod h → ℕ
  fixed_positive : ∀ q d, Piece.fixed d ∈ pieces q → 0 < d
  cells_complete : ∀ q, (cells (pieces q)).Perm (Finset.univ : Finset (Cell r)).toList
  winding : ∀ q, ((pieces q).map (Piece.weight cellA cellB)).sum = h * n
  location : ∀ q i p, (i, p) ∈ locatedCells cellA cellB (pieces q) → ∀ s : Fin r,
    ((origin q + (p + cellA i + s.val) : ℕ) : ZMod (h * n)) =
      connectorPrefixCenterSite h n r (q + phaseOffset h r i.1, i.2, s)

namespace PhysicalFrame

variable {h n r : ℕ}
variable (G : PhysicalFrame h n r)

def row (L : Family h r) (q : ZMod h) : Finset (ZMod (h * n)) :=
  physicalOffsets (h * n) (G.origin q)
    (properPrefixSites (word cellA cellB (choice L q) (G.pieces q)))

def fixedRow (q : ZMod h) : Finset (ZMod (h * n)) :=
  physicalOffsets (h * n) (G.origin q) (fixedOffsets cellA cellB (G.pieces q))

theorem cellA_positive (hr : 2 ≤ r) (i : Cell r) : 0 < cellA i := by
  dsimp [cellA, incomingBase]
  nlinarith

theorem choice_lt (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (L : Family h r) (q : ZMod h) (i : Cell r) :
    choice L q i < cellB i := by
  rcases local_gap_geometry hr hlarge i.1 i.2
    ((L (q + phaseOffset h r i.1)).entry i.1 i.2) with ⟨_, _, _, _, _, _, hp, _⟩
  change 0 < cellB i - choice L q i at hp
  omega

theorem word_positive (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (L : Family h r) (q : ZMod h) :
    ∀ x ∈ word cellA cellB (choice L q) (G.pieces q), 0 < x :=
  LatinCompletion.word_positive cellA cellB (choice L q) (G.pieces q)
    (G.fixed_positive q) (cellA_positive hr) (choice_lt hr hlarge L q)

theorem word_winding (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (L : Family h r) (q : ZMod h) :
    (word cellA cellB (choice L q) (G.pieces q)).sum = h * n :=
  (word_sum cellA cellB (choice L q) (G.pieces q)
    (fun i => (choice_lt hr hlarge L q i).le)).trans (G.winding q)

theorem movingRow_eq (L : Family h r) (q : ZMod h) :
    physicalOffsets (h * n) (G.origin q)
      (movingOffsets cellA cellB (choice L q) (G.pieces q)) =
      movingRow (connectorPrefixCenterSite h n r) L (phaseOffset h r) q := by
  ext x
  rw [mem_movingRow]
  constructor
  · intro hx
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hx
    have hz' : z ∈ movingOffsets cellA cellB (choice L q) (G.pieces q) :=
      List.mem_toFinset.mp hz
    rw [movingOffsets_locations] at hz'
    obtain ⟨⟨i, p⟩, hip, rfl⟩ := List.mem_map.mp hz'
    refine ⟨i.1, i.2, ?_⟩
    exact (G.location q i p hip ((L (q + phaseOffset h r i.1)).entry i.1 i.2)).symm.trans he
  · rintro ⟨j, u, he⟩
    have hi : (j, u) ∈ cells (G.pieces q) :=
      (G.cells_complete q).mem_iff.mpr (by simp)
    rw [← locatedCells_indices cellA cellB] at hi
    obtain ⟨⟨i, p⟩, hip, hi⟩ := List.mem_map.mp hi
    change i = (j, u) at hi
    subst i
    apply Finset.mem_image.mpr
    refine ⟨p + cellA (j, u) + choice L q (j, u), ?_, ?_⟩
    · apply List.mem_toFinset.mpr
      rw [movingOffsets_locations]
      exact List.mem_map.mpr ⟨((j, u), p), hip, rfl⟩
    · exact (G.location q (j, u) p hip ((L (q + phaseOffset h r j)).entry j u)).trans he

theorem row_split (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (L : Family h r) (q : ZMod h) :
    G.row L q = G.fixedRow q ∪ movingRow (connectorPrefixCenterSite h n r) L (phaseOffset h r) q := by
  rw [row, physical_prefix_split _ _ _ _ _ _
    (fun i => (choice_lt hr hlarge L q i).le), movingRow_eq]
  rfl

theorem cell_palette (L : Family h r) (q : ZMod h) :
    ((cells (G.pieces q)).map (fun i =>
      ({cellA i + choice L q i} : Multiset ℕ) + {cellB i - choice L q i})).sum =
      rowIncidentPalette L (phaseOffset h r) incomingBase outgoingBase q := by
  let f : Cell r → Multiset ℕ := fun i =>
    {cellA i + choice L q i} + {cellB i - choice L q i}
  calc
    _ = (((Finset.univ : Finset (Cell r)).toList).map f).sum :=
      ((G.cells_complete q).map f).sum_eq
    _ = ∑ i : Cell r, f i := by
      rw [← List.sum_toFinset f (Finset.nodup_toList _)]
      simp
    _ = _ := by
      simp only [f, cellA, cellB, choice, rowIncidentPalette, block,
        Fintype.sum_prod_type, Finset.sum_add_distrib]

/-- Actual global cyclic edges, derived from the frame rather than assumed. -/
theorem inventory [NeZero (h * n)] (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (L : Family h r) (q : ZMod h) :
    finiteCyclicGapInventory (h * n) ((G.row L q).image ZMod.val) =
      unchanged (G.pieces q) +
        rowIncidentPalette L (phaseOffset h r) incomingBase outgoingBase q := by
  rw [row, physical_frame_inventory _ _ _ _ _ _ (NeZero.pos _) (G.fixed_positive q)
    (cellA_positive hr) (choice_lt hr hlarge L q) (G.winding q), G.cell_palette]

theorem fixed_word_positive (hr : 2 ≤ r) (q : ZMod h) :
    ∀ x ∈ (G.pieces q).map (Piece.weight cellA cellB), 0 < x := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  cases p with
  | fixed d => exact G.fixed_positive q d hp
  | cell i => have := cellA_positive hr i; change 0 < cellA i + cellB i; omega

theorem fixedRow_card (hr : 2 ≤ r) (q : ZMod h) : (G.fixedRow q).card = (G.pieces q).length := by
  rw [fixedRow, fixedOffsets, physical_prefix_card _ _ _ (G.fixed_word_positive hr q)
    (G.winding q), List.length_map]

theorem row_card (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (L : Family h r) (q : ZMod h) :
    (G.row L q).card = (G.pieces q).length + r * r := by
  rw [row, physical_prefix_card _ _ _ (G.word_positive hr hlarge L q)
    (G.word_winding hr hlarge L q), word_length]
  have hc := (G.cells_complete q).length_eq
  simpa using congrArg ((G.pieces q).length + ·) hc

theorem fixed_moving_disjoint [NeZero h] (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (hres : 21 * r * r + 2 * r ≤ n)
    (L : Family h r) (q : ZMod h) :
    Disjoint (G.fixedRow q) (movingRow (connectorPrefixCenterSite h n r) L (phaseOffset h r) q) := by
  apply Finset.card_union_eq_card_add_card.mp
  rw [← G.row_split hr hlarge L q, G.row_card hr hlarge L q,
    G.fixedRow_card hr q, LatinTransfer.movingRow_card _ (connectorPrefixCenterSite_injective hres)]

end PhysicalFrame

end CorralFormalization.LatinCompletion
