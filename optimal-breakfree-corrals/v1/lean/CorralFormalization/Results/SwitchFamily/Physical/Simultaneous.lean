import CorralFormalization.Results.SwitchFamily.Physical.Rows
import CorralFormalization.Results.SwitchFamily.Prefix.Completion

/-!
# The simultaneous physical Appendix A switches

For every set of the h*m actual site pairs, the common permutation of sites
has exactly the positive gap-word rows constructed here. This supplies the
full palette and the preserved physical 1/2/n edges to Lemma 11.
-/

namespace CorralFormalization.Results.SwitchFamily.Physical

open CorralFormalization CorralFormalization.LatinCompletion
open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift GeneralTiles LatinPrefix
open scoped Classical
noncomputable section

variable {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def switchedSetting (q : ZMod h) (role : RowRole)
    (U : Finset (ZMod (h*n) × ZMod (h*n))) (c : Cell m) : Bool :=
  Bool.xor c.2 (decide (sitePair (n:=n) (c.1,cellPhase q role c)∈U))

theorem tileWordFrame_center_at (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (q : ZMod h) (role : RowRole) (c : Cell m) (p : ℕ)
    (hp : (c,p)∈locatedCells cellBase (fun c : Cell m => cellBase c+1)
      (tilePieces n m rest role)) (b : Cell m → Bool) :
    (((tileWordFrame T hn hsmall rest hbody (zeroSite h n q) role).origin+
      (p+cellBase c+(b c).toNat) : ℕ) : ZMod (h*n))=
        endpoint (n:=n) (c.1,cellPhase q role c) (b c) := by
  have he := tileWordFrame_center T hn hsmall hsize rest hbody q role c p hp
  simp only [endpoint,Nat.cast_add,originalSetting] at he ⊢
  linear_combination he

theorem tileWordFrame_moving_action (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (q : ZMod h) (role : RowRole) (U : Finset (ZMod (h*n) × ZMod (h*n)))
    (c : Cell m) (p : ℕ)
    (hp : (c,p)∈locatedCells cellBase (fun c : Cell m => cellBase c+1)
      (tilePieces n m rest role)) :
    FamilySwitches.selectedMotion (switchLayer hsize) U
      (((tileWordFrame T hn hsmall rest hbody (zeroSite h n q) role).origin+
        (p+cellBase c+binaryCoefficient originalSetting c) : ℕ) : ZMod (h*n))=
      (((tileWordFrame T hn hsmall rest hbody (zeroSite h n q) role).origin+
        (p+cellBase c+binaryCoefficient (switchedSetting q role U) c) : ℕ) : ZMod (h*n)) := by
  change FamilySwitches.selectedMotion (switchLayer hsize) U
    (((tileWordFrame T hn hsmall rest hbody (zeroSite h n q) role).origin+
      (p+cellBase c+(originalSetting c).toNat) : ℕ) : ZMod (h*n))=
    (((tileWordFrame T hn hsmall rest hbody (zeroSite h n q) role).origin+
      (p+cellBase c+(switchedSetting q role U c).toNat) : ℕ) : ZMod (h*n))
  rw [tileWordFrame_center T hn hsmall hsize rest hbody q role c p hp,
    tileWordFrame_center_at T hn hsmall hsize rest hbody q role c p hp]
  cases hs : c.2
  · have ha := FamilySwitches.selectedMotion_left (switchLayer hsize) U
      (sitePair (n:=n) (c.1,cellPhase q role c)) (switchLayer_mem hsize _)
    by_cases hu : sitePair (n:=n) (c.1,cellPhase q role c)∈U
    · rw [if_pos hu] at ha
      have hb : switchedSetting q role U c=true := by simp [switchedSetting,hs,hu]
      rw [hb]
      simpa only [sitePair,hs] using ha
    · rw [if_neg hu] at ha
      have hb : switchedSetting q role U c=false := by simp [switchedSetting,hs,hu]
      rw [hb]
      simpa only [sitePair,hs] using ha
  · have ha := FamilySwitches.selectedMotion_right (switchLayer hsize) U
      (sitePair (n:=n) (c.1,cellPhase q role c)) (switchLayer_mem hsize _)
    by_cases hu : sitePair (n:=n) (c.1,cellPhase q role c)∈U
    · rw [if_pos hu] at ha
      have hb : switchedSetting q role U c=false := by simp [switchedSetting,hs,hu]
      rw [hb]
      simpa only [sitePair,hs] using ha
    · rw [if_neg hu] at ha
      have hb : switchedSetting q role U c=true := by simp [switchedSetting,hs,hu]
      rw [hb]
      simpa only [sitePair,hs] using ha

def simultaneousModification (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (U : Finset (ZMod (h*n) × ZMod (h*n))) : RowModification n (L.family T) :=
  wordModification L T hn hsmall hsize rest hbody
    (fun R => switchedSetting (rowRepresentation L T hn hsmall rest hbody R).phase
      (rowRepresentation L T hn hsmall rest hbody R).role U)

/-- Equality with the actual simultaneous physical ownership swaps,
proved row by row from the point action and the positive word geometry. -/
theorem simultaneousModification_row (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (U : Finset (ZMod (h*n) × ZMod (h*n)))
    (R : {R : Finset (ZMod (h*n)) // R∈L.family T}) :
    (simultaneousModification L T hn hsmall hsize rest hbody U).row R=
      R.val.image (FamilySwitches.selectedMotion (switchLayer hsize) U) := by
  rw [← rowFrame_original L T hn hsmall rest hbody R]
  symm
  apply BinaryWordFrame.row_image
  · intro x hx
    apply FamilySwitches.selectedMotion_isolated
    exact fixedRow_isolated L T hn hsmall hsize rest hbody R x hx
  · intro c p hp
    exact tileWordFrame_moving_action T hn hsmall hsize rest hbody
      (rowRepresentation L T hn hsmall rest hbody R).phase
      (rowRepresentation L T hn hsmall rest hbody R).role U c p hp

theorem simultaneousModification_family (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (U : Finset (ZMod (h*n) × ZMod (h*n))) :
    (simultaneousModification L T hn hsmall hsize rest hbody U).family=
      FamilySwitches.switchedFamily (switchLayer hsize) (L.family T) U := by
  ext S
  simp only [RowModification.family,FamilySwitches.switchedFamily,FamilySwitches.imageFamily,
    Finset.mem_image,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨R,he⟩
    exact ⟨R.val,R.property,(simultaneousModification_row L T hn hsmall hsize rest hbody U R).symm.trans he⟩
  · rintro ⟨R,hR,he⟩
    exact ⟨⟨R,hR⟩,(simultaneousModification_row L T hn hsmall hsize rest hbody U ⟨R,hR⟩).trans he⟩

/-- The concrete physical supplier for the marker/isometry/counting
assembly: every bit set has actual full-palette rows preserving 1/2/n,
and their unlabelled family is exactly the common site-swap permutation. -/
theorem actual_row_modification (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (U : Finset (ZMod (h*n) × ZMod (h*n))) :
    ∃ P : RowModification n (L.family T),
      P.family=FamilySwitches.switchedFamily (switchLayer hsize) (L.family T) U :=
  ⟨simultaneousModification L T hn hsmall hsize rest hbody U,
    simultaneousModification_family L T hn hsmall hsize rest hbody U⟩

theorem explicit_actual_row_modification (D : TerraceCompletion.DirectedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (hsize : (5*m+8)^2≤n)
    (hD : Prefix.PrescribedTerrace m D) (L : CyclicTiling h ι)
    (U : Finset (ZMod (h*n) × ZMod (h*n))) :
    ∃ P : RowModification n (L.family (completedOfSpecifiedPrefix D hsmall hD.1)),
      P.family=FamilySwitches.switchedFamily (switchLayer hsize)
        (L.family (completedOfSpecifiedPrefix D hsmall hD.1)) U := by
  apply actual_row_modification L _ hn hsmall hsize (D.word.drop (5*m+7))
  change [7,1]++D.word.drop 7=_
  rw [hD.2.2.2]

end
end CorralFormalization.Results.SwitchFamily.Physical
