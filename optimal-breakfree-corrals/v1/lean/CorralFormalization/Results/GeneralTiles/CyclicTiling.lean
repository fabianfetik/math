import CorralFormalization.DiversityCompletion.GlobalTileCorral

/-!
# Arbitrary cyclic two/three tilings

This extends the consecutive triples-then-pairs schedule of `PhaseTiling`
to every partition of the phase circle into directed intervals of sizes
two and three. The sole layout hypothesis is that those intervals partition
the phase circle. Physical supports, row palettes and the optimal corral
are all conclusions.
-/

namespace CorralFormalization.LatinCompletion.GeneralTiles

open LatinTransfer PhysicalCorral TerraceLift

inductive TileSize
  | two
  | three
  deriving DecidableEq

def TileSize.block {h : ℕ} (s : TileSize) (p : ZMod h) : Finset (ZMod h) :=
  match s with
  | .two => {p,p-1}
  | .three => {p,p-1,p-2}

/-- A cyclic tiling, with arbitrary finite tile labels. No ordering of the
two- and three-tiles and no preferred origin is imposed. -/
structure CyclicTiling (h : ℕ) (ι : Type*) [Fintype ι] where
  start : ι → ZMod h
  size : ι → TileSize
  partition : ∀ q : ZMod h, ∃! i : ι, q ∈ (size i).block (start i)

namespace CyclicTiling

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def support (L : CyclicTiling h ι) (T : CompletedTerrace n) (i : ι) :
    Finset (ZMod (h*n)) :=
  ((L.size i).block (L.start i)).biUnion T.phaseSupport

def rows (L : CyclicTiling h ι) (T : CompletedTerrace n) (i : ι) :
    Finset (Finset (ZMod (h*n))) :=
  match L.size i with
  | .two => {T.tileFirst (L.start i),T.tileTwoSecond (L.start i)}
  | .three => {T.tileFirst (L.start i),T.tileThreeSecond (L.start i),
      T.tileThreeThird (L.start i)}

def family (L : CyclicTiling h ι) (T : CompletedTerrace n) :
    Finset (Finset (ZMod (h*n))) :=
  Finset.univ.biUnion (L.rows T)

theorem support_exactly_once (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (x : ZMod (h*n)) : ∃! i, x ∈ L.support T i := by
  obtain ⟨q,hq,hquniq⟩ := T.phaseSupport_exactly_once x
  obtain ⟨i,hi,hiuniq⟩ := L.partition q
  refine ⟨i,Finset.mem_biUnion.mpr ⟨q,hi,hq⟩,?_⟩
  intro j hj
  obtain ⟨p,hp,hxp⟩ := Finset.mem_biUnion.mp hj
  have hpq : p=q := hquniq p hxp
  exact hiuniq j (hpq ▸ hp)

theorem rows_inventory (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) (i : ι)
    (R : Finset (ZMod (h*n))) (hR : R ∈ L.rows T i) :
    finiteCyclicGapInventory (h*n) (R.image ZMod.val) =
      Multiset.ofList (fullGapList n) := by
  obtain ⟨ha,hb,hc,hd⟩ := TileGapWords.all_tile_inventories hn hsmall T.body T.differences
    (zeroSite h n (L.start i)+((n-1 : ℕ) : ZMod (h*n)))
    (zeroSite h n (L.start i)+2) (zeroSite h n (L.start i-1)+12)
  cases hs : L.size i <;>
    simp only [rows,hs,Finset.mem_insert,Finset.mem_singleton] at hR
  · rcases hR with rfl | rfl
    · exact ha
    · exact hb
  · rcases hR with rfl | rfl | rfl
    · exact ha
    · exact hc
    · exact hd

theorem rows_disjoint (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) (i : ι)
    (R S : Finset (ZMod (h*n)))
    (hR : R ∈ L.rows T i) (hS : S ∈ L.rows T i) (hRS : R ≠ S) : Disjoint R S := by
  cases hs : L.size i
  · have hab := (T.two_tile_partition hn hsmall (L.start i)).1
    exact CompletedTerrace.pair_disjoint _ _ R S hab
      (by simpa [rows,hs,CompletedTerrace.tileFirst,CompletedTerrace.tileTwoSecond] using hR)
      (by simpa [rows,hs,CompletedTerrace.tileFirst,CompletedTerrace.tileTwoSecond] using hS) hRS
  · obtain ⟨hab,hac,hbc,_⟩ := T.three_tile_partition hn hsmall (L.start i)
    exact CompletedTerrace.triple_disjoint _ _ _ R S hab hac hbc
      (by simpa [rows,hs,CompletedTerrace.tileFirst,CompletedTerrace.tileThreeSecond,
        CompletedTerrace.tileThreeThird] using hR)
      (by simpa [rows,hs,CompletedTerrace.tileFirst,CompletedTerrace.tileThreeSecond,
        CompletedTerrace.tileThreeThird] using hS) hRS

theorem rows_cover (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) (i : ι) :
    (L.rows T i).biUnion id = L.support T i := by
  cases hs : L.size i
  · have hc := (T.two_tile_partition hn hsmall (L.start i)).2
    simp only [rows,hs,Finset.biUnion_insert,Finset.singleton_biUnion,id_eq]
    rw [support,hs,TileSize.block]
    simp only [Finset.biUnion_insert,Finset.singleton_biUnion,
      CompletedTerrace.phaseSupport,← Finset.union_assoc]
    change T.tileFirst (L.start i) ∪ T.tileTwoSecond (L.start i) = _
    rw [show T.tileFirst (L.start i) ∪ T.tileTwoSecond (L.start i) = _ from hc]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  · have hc := (T.three_tile_partition hn hsmall (L.start i)).2.2.2
    simp only [rows,hs,Finset.biUnion_insert,Finset.singleton_biUnion,id_eq]
    rw [support,hs,TileSize.block]
    simp only [Finset.biUnion_insert,Finset.singleton_biUnion,
      CompletedTerrace.phaseSupport,← Finset.union_assoc]
    change T.tileFirst (L.start i) ∪ T.tileThreeSecond (L.start i) ∪
      T.tileThreeThird (L.start i) = _
    rw [show T.tileFirst (L.start i) ∪ T.tileThreeSecond (L.start i) ∪
      T.tileThreeThird (L.start i) = _ from hc]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto

theorem rows_subset_support (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) (i : ι)
    (R : Finset (ZMod (h*n))) (hR : R ∈ L.rows T i) : R ⊆ L.support T i := by
  intro x hx
  rw [← L.rows_cover T hn hsmall i]
  exact Finset.mem_biUnion.mpr ⟨R,hR,hx⟩

theorem inventory (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n)
    (R : Finset (ZMod (h*n))) (hR : R ∈ L.family T) :
    finiteCyclicGapInventory (h*n) (R.image ZMod.val) =
      Multiset.ofList (fullGapList n) := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hR
  exact L.rows_inventory T hn hsmall i R hi

theorem disjoint (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n)
    (R S : Finset (ZMod (h*n))) (hR : R ∈ L.family T) (hS : S ∈ L.family T)
    (hRS : R ≠ S) : Disjoint R S := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hR
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hS
  by_cases he : i=j
  · subst j
    exact L.rows_disjoint T hn hsmall i R S hi hj hRS
  · apply Finset.disjoint_left.mpr
    intro x hxR hxS
    obtain ⟨owner,_,huniq⟩ := L.support_exactly_once T x
    exact he ((huniq i (L.rows_subset_support T hn hsmall i R hi hxR)).trans
      (huniq j (L.rows_subset_support T hn hsmall j S hj hxS)).symm)

theorem full (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) :
    (L.family T).biUnion id = (Finset.univ : Finset (ZMod (h*n))) := by
  ext x
  simp only [Finset.mem_univ,iff_true]
  obtain ⟨i,hi,_⟩ := L.support_exactly_once T x
  rw [← L.rows_cover T hn hsmall i] at hi
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨R,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hR⟩,hxR⟩

theorem card (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) : (L.family T).card=h := by
  have hc : ((L.family T).biUnion id).card = ∑ R ∈ L.family T, R.card := by
    apply Finset.card_biUnion
    intro R hR S hS hRS
    exact L.disjoint T hn hsmall R S hR hS hRS
  have hs : (∑ R ∈ L.family T, R.card) = (L.family T).card*n := by
    calc
      _ = ∑ _R ∈ L.family T,n := Finset.sum_congr rfl (fun R hR =>
        CompletedTerrace.card_of_inventory R (L.inventory T hn hsmall R hR))
      _ = _ := by simp
  rw [L.full T hn hsmall,hs] at hc
  simp only [Finset.card_univ,ZMod.card] at hc
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
  simpa [Nat.mul_comm] using hc.symm

/-- The first geometric conclusion of Lemma 11 for every cyclic 2/3
tiling, rather than only a block of triples followed by a block of pairs. -/
theorem optimal_corral (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 15 ≤ n) :
    ∃ R : CorralRows h n, Finset.univ.image R.sites =
      (L.family T).image (fun S => S.image ZMod.val) := by
  apply CompletedTerrace.corral_of_physical_family _
    (optimal_width (NeZero.pos h) hn) (L.card T hn hsmall)
  · intro R hR
    apply Finset.card_pos.mp
    rw [CompletedTerrace.card_of_inventory R (L.inventory T hn hsmall R hR)]
    exact NeZero.pos n
  · intro R hR S hS hRS
    exact L.disjoint T hn hsmall R S hR hS hRS
  · exact L.inventory T hn hsmall

end CyclicTiling

end CorralFormalization.LatinCompletion.GeneralTiles
