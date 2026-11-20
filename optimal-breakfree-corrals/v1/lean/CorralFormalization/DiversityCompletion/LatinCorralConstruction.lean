import CorralFormalization.DiversityCompletion.PhysicalLatinFrame

namespace CorralFormalization.LatinCompletion

open LatinTransfer

namespace PhysicalFrame

variable {h n r : ℕ} [NeZero h] [NeZero (h * n)]

/-- One supplied physical baseline, at one fixed Latin family. This is not
a conclusion about all replacements: its rows are the concrete positive
gap words of the frame before Latin choices are varied. -/
structure FullBaseline (G : PhysicalFrame h n r) where
  latin : Family h r
  partition : ∀ x : ZMod (h * n), ∃! q, x ∈ G.row latin q
  palette : ∀ q, finiteCyclicGapInventory (h * n) ((G.row latin q).image ZMod.val) =
    Multiset.ofList (fullGapList n)

variable (G : PhysicalFrame h n r)

omit [NeZero h] [NeZero (h * n)] in
theorem baseline_disjoint (T : FullBaseline G) {q t : ZMod h} (hqt : q ≠ t) :
    Disjoint (G.row T.latin q) (G.row T.latin t) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  obtain ⟨owner, _, huniq⟩ := T.partition x
  exact hqt ((huniq q hx).trans (huniq t ht).symm)

omit [NeZero h] [NeZero (h * n)] in
theorem fixedRows_disjoint (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (T : FullBaseline G) {q t : ZMod h} (hqt : q ≠ t) :
    Disjoint (G.fixedRow q) (G.fixedRow t) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  apply Finset.disjoint_left.mp (G.baseline_disjoint T hqt)
  · rw [G.row_split hr hlarge]
    exact Finset.mem_union_left _ hx
  · rw [G.row_split hr hlarge]
    exact Finset.mem_union_left _ ht

omit [NeZero (h * n)] in
theorem fixedRows_avoid (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) (q : ZMod h) (c : ZMod h × Fin r × Fin r) :
    connectorPrefixCenterSite h n r c ∉ G.fixedRow q := by
  intro hfixed
  obtain ⟨t, ht⟩ := (movingRows_cover (connectorPrefixCenterSite h n r) T.latin (phaseOffset h r) (connectorPrefixCenterSite h n r c)).mpr
    ⟨c, rfl⟩
  have hq : connectorPrefixCenterSite h n r c ∈ G.row T.latin q := by
    rw [G.row_split hr hlarge]
    exact Finset.mem_union_left _ hfixed
  have htm : connectorPrefixCenterSite h n r c ∈ G.row T.latin t := by
    rw [G.row_split hr hlarge]
    exact Finset.mem_union_right _ ht
  obtain ⟨owner, _, huniq⟩ := T.partition (connectorPrefixCenterSite h n r c)
  have hqt : q = t := (huniq q hq).trans (huniq t htm).symm
  subst t
  exact Finset.disjoint_left.mp (G.fixed_moving_disjoint hr hlarge hres T.latin q) hfixed ht

omit [NeZero h] [NeZero (h * n)] in
theorem fixedRows_cover (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n) (T : FullBaseline G) (x : ZMod (h * n)) (hx : ¬ ∃ c, connectorPrefixCenterSite h n r c = x) :
    ∃ q, x ∈ G.fixedRow q := by
  obtain ⟨q, hq, _⟩ := T.partition x
  rw [G.row_split hr hlarge] at hq
  rcases Finset.mem_union.mp hq with hf | hm
  · exact ⟨q, hf⟩
  · exact False.elim (hx ((movingRows_cover (connectorPrefixCenterSite h n r) T.latin (phaseOffset h r) x).mp ⟨q, hm⟩))

omit [NeZero h] in
theorem origin_mem_fixedRow (q : ZMod h) :
    (G.origin q : ZMod (h * n)) ∈ G.fixedRow q := by
  have hp : G.pieces q ≠ [] := by
    intro he
    have hw : 0 = h * n := by
      simpa only [he, List.map_nil, List.sum_nil] using G.winding q
    exact (NeZero.ne (h * n)) hw.symm
  have hlen : 0 < ((G.pieces q).map (Piece.weight cellA cellB)).length := by
    rw [List.length_map]
    exact List.length_pos_iff.mpr hp
  apply Finset.mem_image.mpr
  refine ⟨0, List.mem_toFinset.mpr ?_, by simp⟩
  exact (mem_properPrefixSites_iff _ 0).mpr ⟨0, hlen, by simp⟩

/-- The old abstract skeleton is now constructed from concrete fixed
prefix-sites of the supplied physical frame and one real baseline. -/
def skeleton (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) : FixedSkeleton (connectorPrefixCenterSite h n r) where
  fixed := G.fixedRow
  disjoint := fun _q _t hqt => G.fixedRows_disjoint hr hlarge T hqt
  avoids := G.fixedRows_avoid hr hlarge hres T
  covers := G.fixedRows_cover hr hlarge T
  anchor := fun q => (G.origin q : ZMod (h * n))
  anchor_mem := G.origin_mem_fixedRow

theorem row_eq_transferred (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) (L : Family h r) (q : ZMod h) :
    G.row L q = transferredRows (connectorPrefixCenterSite h n r) (G.skeleton hr hlarge hres T)
      L (phaseOffset h r) q := G.row_split hr hlarge L q

/-- Both fields of the old certificate are now proved. Only the initial
baseline's palette is used; the inventory of every modified row follows
from positive local blocks and the frame's one-winding geometry. -/
def edgeCertificate (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) (L : Family h r) :
    CyclicEdgeCertificate (connectorPrefixCenterSite h n r) (G.skeleton hr hlarge hres T)
      L (phaseOffset h r) incomingBase outgoingBase where
  unchanged := fun q => unchanged (G.pieces q)
  decomposition := by
    intro q
    change finiteCyclicGapInventory (h * n)
      ((transferredRows (connectorPrefixCenterSite h n r) (G.skeleton hr hlarge hres T) L (phaseOffset h r)
        (q.val : ZMod h)).image ZMod.val) = _
    rw [← G.row_eq_transferred hr hlarge hres T]
    exact G.inventory hr hlarge L (q.val : ZMod h)
  baseline := by
    intro q
    have hp := G.inventory hr hlarge T.latin q
    rw [rowIncidentPalette_eq] at hp
    exact hp.symm.trans (T.palette q)

def completed (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) (hn : n = 2 * h - 1) (L : Family h r) : CorralRows h n :=
  toCorralRows (connectorPrefixCenterSite h n r) (connectorPrefixCenterSite_injective hres) (G.skeleton hr hlarge hres T)
    L (phaseOffset h r) incomingBase outgoingBase (optimal_width (NeZero.pos h) hn)
      (G.edgeCertificate hr hlarge hres T L)

theorem completed_sites (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) (hn : n = 2 * h - 1) (L : Family h r) (q : Fin h) :
    (G.completed hr hlarge hres T hn L).sites q = naturalRows (G.row L) q := by
  change naturalRows
    (transferredRows (connectorPrefixCenterSite h n r) (G.skeleton hr hlarge hres T) L (phaseOffset h r)) q = _
  simp only [naturalRows, ← G.row_eq_transferred hr hlarge hres T]

theorem completed_original (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) (hn : n = 2 * h - 1) (L : Family h r) :
    OriginalCorral h n := (G.completed hr hlarge hres T hn L).original (NeZero.pos h)

theorem completed_full_occupancy (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) (hn : n = 2 * h - 1) (L : Family h r)
    (x : ℕ) (hx : x < width n) :
    ∃! q, x ∈ (G.completed hr hlarge hres T hn L).sites q := by
  exact toCorralRows_full_occupancy (connectorPrefixCenterSite h n r) (connectorPrefixCenterSite_injective hres)
    (G.skeleton hr hlarge hres T) L (phaseOffset h r) incomingBase outgoingBase
      (optimal_width (NeZero.pos h) hn) (G.edgeCertificate hr hlarge hres T L) x hx

def unlabelled (L : Family h r) : Finset (Finset (ZMod (h * n))) :=
  Finset.univ.image (G.row L)

theorem unlabelled_injective (hr : 2 ≤ r) (hlarge : 100 * r * r ≤ n)
    (hres : 21 * r * r + 2 * r ≤ n) (T : FullBaseline G) (hh : 2 * r * r ≤ h) :
    Function.Injective G.unlabelled := by
  have he (L : Family h r) : G.unlabelled L =
      unlabelledPartition (connectorPrefixCenterSite h n r) (G.skeleton hr hlarge hres T) (phaseOffset h r) L := by
    simp only [unlabelled, unlabelledPartition]
    congr 1
    funext q
    exact G.row_eq_transferred hr hlarge hres T L q
  intro L K hLK
  apply connectorPrefixCenterSite_unlabelledPartition_injective (by omega) hres hh (G.skeleton hr hlarge hres T)
  rw [← he L, ← he K]
  exact hLK

end PhysicalFrame

end CorralFormalization.LatinCompletion
