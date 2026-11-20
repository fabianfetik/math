import CorralFormalization.Results.GeneralTiles.Isometries
import CorralFormalization.Results.GeneralTiles.UnchangedSegment

/-!
# Lemma 11 with exactly the printed directed-terrace input

These are direct statement-facing endpoints. They discharge the calendar
and source-body conditions from the actual eight-vertex prefix rather than
reintroducing those conditions as extra hypotheses.
-/

namespace CorralFormalization.LatinCompletion.GeneralTiles

open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift TerraceCompletion

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem explicit_optimal_corral (D : DirectedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hp : HasSpecifiedPrefix D) (L : CyclicTiling h ι) :
    ∃ R : CorralRows h n, Finset.univ.image R.sites =
      (L.family (completedOfSpecifiedPrefix D hsmall hp)).image (fun S => S.image ZMod.val) :=
  L.optimal_corral (completedOfSpecifiedPrefix D hsmall hp) hn (by omega)

theorem explicit_distinguished_tails (D : DirectedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hp : HasSpecifiedPrefix D) (L : CyclicTiling h ι) :
    familyTails (L.family (completedOfSpecifiedPrefix D hsmall hp)) 1=oneTailPattern h n ∧
    familyTails (L.family (completedOfSpecifiedPrefix D hsmall hp)) 2=L.twoTailPattern n ∧
    familyTails (L.family (completedOfSpecifiedPrefix D hsmall hp)) n=L.nTailPattern n :=
  ⟨L.gap_one_tails _ hn hsmall (D.word.drop 7) rfl,
    L.gap_two_tails _ hn hsmall,L.gap_n_tails _ hn hsmall⟩

theorem explicit_unchanged_segment (D : DirectedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hp : HasSpecifiedPrefix D) (L : CyclicTiling h ι)
    (R : Finset (ZMod (h*n))) (hR : R∈L.family (completedOfSpecifiedPrefix D hsmall hp)) :
    ∃ p : ZMod h, ∃ role : LatinPrefix.RowRole,
      R=TileGapWords.row (tileOrigin n (zeroSite h n p) role)
        (LatinPrefix.roleWord (completedOfSpecifiedPrefix D hsmall hp) role) ∧
      (∀ k, k<(1::D.word.drop 7).length →
        Adjacent R
          (segmentPhase n (zeroSite h n p) role+17+
            ((((1::D.word.drop 7).take k).sum : ℕ) : ZMod (h*n)))
          (segmentPhase n (zeroSite h n p) role+17+
            ((((1::D.word.drop 7).take (k+1)).sum : ℕ) : ZMod (h*n)))) ∧
      residueMap h n (segmentPhase n (zeroSite h n p) role+17)=17 ∧
      residueMap h n (segmentPhase n (zeroSite h n p) role+17+
        (((1::D.word.drop 7).sum : ℕ) : ZMod (h*n)))=((n-3 : ℕ) : ZMod n) := by
  obtain ⟨p,role,he,hseg⟩ := L.every_row_unchanged_segment
    (completedOfSpecifiedPrefix D hsmall hp) hn hsmall (D.word.drop 7) rfl R hR
  obtain ⟨hstart,hend⟩ := unchanged_segment_endpoints
    (completedOfSpecifiedPrefix D hsmall hp) hn hsmall (D.word.drop 7) rfl p role
  exact ⟨p,role,he,hseg,hstart,hend⟩

theorem explicit_modified_tails (D : DirectedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hp : HasSpecifiedPrefix D) (L : CyclicTiling h ι)
    (P : RowModification n (L.family (completedOfSpecifiedPrefix D hsmall hp))) :
    familyTails P.family 1=oneTailPattern h n ∧
    familyTails P.family 2=L.twoTailPattern n ∧
    familyTails P.family n=L.nTailPattern n :=
  ⟨L.modified_gap_one_tails _ hn hsmall (D.word.drop 7) rfl P,
    L.modified_gap_two_tails _ hn hsmall P,L.modified_gap_n_tails _ hn hsmall P⟩

/-- Complete general isometry endpoint of Lemma 11, from actual directed
terraces with the printed prefix and arbitrary cyclic tilings. -/
theorem explicit_modified_isometry {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D E : DirectedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hpD : HasSpecifiedPrefix D) (hpE : HasSpecifiedPrefix E)
    (L : CyclicTiling h ι) (K : CyclicTiling h κ)
    (P : RowModification n (L.family (completedOfSpecifiedPrefix D hsmall hpD)))
    (Q : RowModification n (K.family (completedOfSpecifiedPrefix E hsmall hpE)))
    (f : Motion (h*n)) (hf : f.onFamily P.family=Q.family) :
    ∃ a : ZMod h, f=.rotation (zeroSite h n a) ∧
      L.twoStarts.image (fun q => a+q)=K.twoStarts ∧
      L.threeStarts.image (fun q => a+q)=K.threeStarts :=
  L.modified_isometry K _ _ hn hsmall (D.word.drop 7) (E.word.drop 7)
    rfl rfl P Q f hf

theorem explicit_modified_same_layout_identity
    (D E : DirectedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hpD : HasSpecifiedPrefix D) (hpE : HasSpecifiedPrefix E) (L : CyclicTiling h ι)
    (P : RowModification n (L.family (completedOfSpecifiedPrefix D hsmall hpD)))
    (Q : RowModification n (L.family (completedOfSpecifiedPrefix E hsmall hpE)))
    (p : ZMod h) (hthree : L.threeStarts={p} ∨ L.threeStarts={p,p-3})
    (f : Motion (h*n)) (hf : f.onFamily P.family=Q.family) : f=.rotation 0 :=
  L.modified_same_layout_identity _ _ hn hsmall (D.word.drop 7) (E.word.drop 7)
    rfl rfl P Q p hthree f hf

end CorralFormalization.LatinCompletion.GeneralTiles
