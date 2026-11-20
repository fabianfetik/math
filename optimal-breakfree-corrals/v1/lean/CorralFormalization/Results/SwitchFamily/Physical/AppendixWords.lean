import CorralFormalization.Results.SwitchFamily.Physical.Words
import CorralFormalization.Results.SwitchFamily.Prefix.Colors

/-! Literal Appendix A.3 cells in every actual two/three-tile row. -/

namespace CorralFormalization.Results.SwitchFamily.Physical

open CorralFormalization CorralFormalization.LatinCompletion
open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift GeneralTiles LatinPrefix

abbrev Cell (m : ℕ) := Fin m × Bool

def cellBase {m : ℕ} (c : Cell m) : ℕ :=
  if c.2 then Prefix.beta c.1.val else Prefix.alpha c.1.val

def originalSetting {m : ℕ} (c : Cell m) : Bool := c.2

def blockPieces {m : ℕ} (n : ℕ) (i : Fin m) : List (Piece (Cell m)) :=
  [.cell (i,false),.fixed (n-(Prefix.alpha i.val+Prefix.beta i.val+1)),.cell (i,true)]

def switchPieces (n m : ℕ) : List (Piece (Cell m)) :=
  (List.finRange m).flatMap (blockPieces n)

def suffixPieces (n m : ℕ) (rest : List ℕ) : List (Piece (Cell m)) :=
  switchPieces n m++fixedPieces rest

def tilePieces (n m : ℕ) (rest : List ℕ) (role : RowRole) : List (Piece (Cell m)) :=
  fixedPieces (beforeSeventeen n role++[1])++suffixPieces n m rest++
    fixedPieces (afterSegment n role)

theorem map_val_finRange (m : ℕ) : (List.finRange m).map Fin.val=List.range m := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

theorem word_flatMap {J : Type*} {I : Type*} (A B c : I → ℕ)
    (f : J → List (Piece I)) (xs : List J) :
    word A B c (xs.flatMap f)=xs.flatMap (fun j => word A B c (f j)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,word_append,ih]

theorem blockPieces_word {m : ℕ} (n : ℕ) (i : Fin m) :
    word cellBase (fun c : Cell m => cellBase c+1)
      (binaryCoefficient originalSetting) (blockPieces n i)=Prefix.blockColors n i.val := by
  simp [blockPieces,word,Piece.gaps,cellBase,binaryCoefficient,originalSetting,
    Prefix.blockColors]

theorem switchPieces_word (n m : ℕ) :
    word cellBase (fun c : Cell m => cellBase c+1)
      (binaryCoefficient originalSetting) (switchPieces n m)=
        (List.range m).flatMap (Prefix.blockColors n) := by
  rw [switchPieces,word_flatMap]
  simp_rw [blockPieces_word]
  rw [← map_val_finRange m,List.flatMap_map]

theorem tilePieces_word {n m : ℕ} (T : CompletedTerrace n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (role : RowRole) :
    word cellBase (fun c : Cell m => cellBase c+1)
      (binaryCoefficient originalSetting) (tilePieces n m rest role)=roleWord T role := by
  simp only [tilePieces,suffixPieces,word_append,word_fixedPieces,switchPieces_word]
  rw [roleWord_segment T _ hbody role]
  simp [List.append_assoc]

theorem cellBase_positive {m : ℕ} (c : Cell m) : 0<cellBase c := by
  simp only [cellBase,Prefix.alpha,Prefix.beta]
  split <;> omega

theorem tilePieces_fixed_positive {h n m : ℕ} [NeZero h]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (role : RowRole) (d : ℕ) (hd : Piece.fixed d∈tilePieces n m rest role) : 0<d := by
  have hw := (TileGapWords.word_properties hn (NeZero.pos h) _
    (roleWord_perm T (by omega : 0<n) role)).1
  apply hw d
  rw [← tilePieces_word T rest hbody role]
  apply List.mem_flatMap.mpr
  exact ⟨.fixed d,hd,by simp [Piece.gaps]⟩

/-- The frame is constructed from the actual completed terrace and its
literal A4 prefix. Its winding, positivity and baseline identity are
conclusions of the existing tile-word theorems. -/
def tileWordFrame {h n m : ℕ} [NeZero h] [NeZero (h*n)]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (z : ZMod (h*n)) (role : RowRole) : BinaryWordFrame (h*n) (Cell m) where
  origin := (tileOrigin n z role).val
  base := cellBase
  pieces := tilePieces n m rest role
  base_positive := cellBase_positive
  fixed_positive := tilePieces_fixed_positive T hn hsmall rest hbody role
  winding := by
    rw [← binary_word_sum _ _ originalSetting,tilePieces_word T rest hbody role]
    exact (TileGapWords.word_properties hn (NeZero.pos h) _
      (roleWord_perm T (by omega : 0<n) role)).2.1
  length_two := by
    rw [← word_length cellBase (fun c : Cell m => cellBase c+1)
      (binaryCoefficient originalSetting),tilePieces_word T rest hbody role]
    have he := (TileGapWords.word_properties hn (NeZero.pos h) _
      (roleWord_perm T (by omega : 0<n) role)).2.2
    omega

theorem tileWordFrame_original {h n m : ℕ} [NeZero h] [NeZero (h*n)]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (z : ZMod (h*n)) (role : RowRole) :
    (tileWordFrame T hn hsmall rest hbody z role).row originalSetting=
      TileGapWords.row (tileOrigin n z role) (roleWord T role) := by
  change physicalOffsets _ (tileOrigin n z role).val
    (properPrefixSites (word cellBase (fun c : Cell m => cellBase c+1)
      (binaryCoefficient originalSetting) (tilePieces n m rest role)))=_
  rw [tilePieces_word T rest hbody role]
  rfl

theorem cellBase_avoids_markers {n m : ℕ} (hn : 65≤n)
    (hsize : (5*m+8)^2≤n) (c : Cell m) (d : ℕ) (hd : d∈({1,2,n} : Finset ℕ)) :
    cellBase c≠d ∧ cellBase c+1≠d := by
  have hs := Prefix.color_separation hn hsize c.1.isLt
  simp only [Finset.mem_insert,Finset.mem_singleton] at hd
  simp only [cellBase]
  split <;> rcases hd with rfl|rfl|rfl <;> omega

theorem tileWordFrame_inventory {h n m : ℕ} [NeZero h] [NeZero (h*n)]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (z : ZMod (h*n)) (role : RowRole) (b : Cell m → Bool) :
    finiteCyclicGapInventory (h*n)
      (((tileWordFrame T hn hsmall rest hbody z role).row b).image ZMod.val)=
        Multiset.ofList (fullGapList n) := by
  rw [(tileWordFrame T hn hsmall rest hbody z role).inventory_eq b originalSetting,
    tileWordFrame_original T hn hsmall rest hbody z role]
  exact TileGapWords.row_inventory hn (NeZero.pos h) _ _
    (roleWord_perm T (by omega : 0<n) role)

theorem tileWordFrame_tails {h n m : ℕ} [NeZero h] [NeZero (h*n)]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (z : ZMod (h*n)) (role : RowRole) (b : Cell m → Bool)
    (d : ℕ) (hd : d∈({1,2,n} : Finset ℕ)) :
    gapTails ((tileWordFrame T hn hsmall rest hbody z role).row b) d=
      gapTails (TileGapWords.row (tileOrigin n z role) (roleWord T role)) d := by
  rw [← tileWordFrame_original T hn hsmall rest hbody z role]
  apply BinaryWordFrame.gapTails_eq
  exact fun c => cellBase_avoids_markers hsmall hsize c d hd

end CorralFormalization.Results.SwitchFamily.Physical
