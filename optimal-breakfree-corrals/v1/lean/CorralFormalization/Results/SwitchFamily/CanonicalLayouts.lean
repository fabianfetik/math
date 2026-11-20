import CorralFormalization.Results.GeneralTiles.TerraceTileConstruction

/-!
# Fixed layouts with one or two three-tiles

Turn the established consecutive phase blocks into the general cyclic
tiling type.  This supplies the exact fixed layout used for the Appendix A
orbit argument; it contains no terrace or switch-family existence claim.
-/

open CorralFormalization.LatinCompletion
open CorralFormalization.LatinCompletion.PhaseTiling
open CorralFormalization.LatinCompletion.GeneralTiles

namespace CorralFormalization.Results.SwitchFamily.CanonicalLayouts

noncomputable section

variable {h m k : ℕ} [NeZero h]

def blockSize : TileIndex m k → TileSize
  | .inl _ => .three
  | .inr _ => .two

omit [NeZero h] in
theorem phaseBlock_eq_tileBlock (i : TileIndex m k) :
    phaseBlock h i = (blockSize i).block (top h i) := by
  cases i with
  | inl i => simpa [blockSize, TileSize.block] using phaseBlock_three h (k:=k) i
  | inr j => simpa [blockSize, TileSize.block] using phaseBlock_two h (m:=m) j

/-- Any decomposition `h=3m+2k` gives the actual corresponding cyclic
tiling, using the existing proved phase partition. -/
def fromBlocks (htotal : h=3*m+2*k) : CyclicTiling h (TileIndex m k) where
  start := top h
  size := blockSize
  partition := by
    intro q
    obtain ⟨i,hi,huniq⟩ := phaseBlock_exactly_once htotal q
    refine ⟨i,?_,?_⟩
    · simpa [← phaseBlock_eq_tileBlock i] using hi
    · intro j hj
      apply huniq
      simpa [phaseBlock_eq_tileBlock j] using hj

theorem mem_fromBlocks_threeStarts (htotal : h=3*m+2*k) (q : ZMod h) :
    q ∈ (fromBlocks htotal).threeStarts ↔ ∃ i : Fin m, top h (.inl i : TileIndex m k)=q := by
  classical
  unfold CyclicTiling.threeStarts
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,hi,hiq⟩
    cases i with
    | inl i => exact ⟨i,hiq⟩
    | inr j => simp [fromBlocks,blockSize] at hi
  · rintro ⟨i,hi⟩
    exact ⟨.inl i,by rfl,hi⟩

/-- The odd-height layout has one three-tile. -/
theorem fromBlocks_one_three {k : ℕ} (htotal : h=3*1+2*k) :
    (fromBlocks htotal).threeStarts = {(2 : ZMod h)} := by
  ext q
  rw [mem_fromBlocks_threeStarts]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨i,hi⟩
    have hz : i.val=0 := by have := i.isLt; omega
    simpa [top,hz] using hi.symm
  · intro hq
    subst q
    refine ⟨⟨0,by omega⟩,?_⟩
    simp [top]

/-- The even-height layout has two consecutive three-tiles, with start
phases `5` and `5-3`. -/
theorem fromBlocks_two_three {k : ℕ} (htotal : h=3*2+2*k) :
    (fromBlocks htotal).threeStarts = {(5 : ZMod h),(5 : ZMod h)-3} := by
  ext q
  rw [mem_fromBlocks_threeStarts]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  have hsub : (5 : ZMod h)-3 = 2 := by ring
  rw [hsub]
  constructor
  · rintro ⟨i,hi⟩
    have hz : i.val=0 ∨ i.val=1 := by have := i.isLt; omega
    rcases hz with hz | hz
    · right
      simpa [top,hz] using hi.symm
    · left
      simpa [top,hz] using hi.symm
  · rintro (hq | hq)
    · subst q
      refine ⟨⟨1,by omega⟩,?_⟩
      simp [top]
    · subst q
      refine ⟨⟨0,by omega⟩,?_⟩
      simp [top]

/-- Every height at least eight has one of the two concrete fixed layouts
used in the paper, with all phase-partition obligations paid. -/
theorem fixed_layout_exists (h : ℕ) [NeZero h] (hh : 8 ≤ h) :
    ∃ (m k : ℕ) (htotal : h=3*m+2*k) (p : ZMod h),
      (fromBlocks htotal).threeStarts={p} ∨
      (fromBlocks htotal).threeStarts={p,p-3} := by
  by_cases ho : h%2=1
  · let k := (h-3)/2
    have htotal : h=3*1+2*k := by dsimp [k]; omega
    exact ⟨1,k,htotal,2,Or.inl (fromBlocks_one_three htotal)⟩
  · let k := (h-6)/2
    have htotal : h=3*2+2*k := by dsimp [k]; omega
    exact ⟨2,k,htotal,5,Or.inr (fromBlocks_two_three htotal)⟩

end
end CorralFormalization.Results.SwitchFamily.CanonicalLayouts
