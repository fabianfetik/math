import CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCodeBounds

/-!
# Actual whole-phase translation of the Appendix A physical family

The word action `LocalWord.rotate t` precomposes with `q ↦ q+t`.
Accordingly a physical translation by `zeroSite a` has word action
`rotate (-a)`. Every selected physical pair is translated in the positive
direction by `zeroSite a`; no bit is complemented or exchanged with a
different block index. The proofs below use the actual tile rows and the
actual matching-layer permutation, with no equivariance supplier.
-/

namespace CorralFormalization.Results.SwitchFamily.LayoutPhysicalEquivariance

open CorralFormalization.LatinCompletion
open TerraceCompletion TerraceLift GeneralTiles DiversitySymmetry PhysicalCorral
open CorralFormalization.Results.SwitchFamily.Counting
open CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode
open CorralFormalization.Results.SwitchFamily.Physical
open CorralFormalization.Results.SwitchFamily.FamilySwitches
open CorralFormalization.Results.SwitchFamily.LayoutPhysicalBridge

noncomputable section

variable {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

theorem row_rotation (o c : ZMod (h*n)) (w : List ℕ) :
    (Motion.rotation c).onRow (TileGapWords.row o w)=TileGapWords.row (c+o) w := by
  simp only [Motion.onRow,TileGapWords.row,physicalOffsets,Finset.image_image,
    Function.comp_def,Motion.act]
  apply Finset.image_congr
  intro x _
  simp only [Nat.cast_add,ZMod.natCast_zmod_val]
  ring

theorem tileFirst_rotation (T : CompletedTerrace n) (a q : ZMod h) :
    (Motion.rotation (zeroSite h n a)).onRow (T.tileFirst q)=T.tileFirst (q+a) := by
  rw [CompletedTerrace.tileFirst,row_rotation,CompletedTerrace.tileFirst,zeroSite_add]
  congr 1
  ring

theorem tileTwoSecond_rotation (T : CompletedTerrace n) (a q : ZMod h) :
    (Motion.rotation (zeroSite h n a)).onRow (T.tileTwoSecond q)=T.tileTwoSecond (q+a) := by
  rw [CompletedTerrace.tileTwoSecond,row_rotation,CompletedTerrace.tileTwoSecond,zeroSite_add]
  congr 1
  ring

theorem tileThreeSecond_rotation (T : CompletedTerrace n) (a q : ZMod h) :
    (Motion.rotation (zeroSite h n a)).onRow (T.tileThreeSecond q)=T.tileThreeSecond (q+a) := by
  rw [CompletedTerrace.tileThreeSecond,row_rotation,CompletedTerrace.tileThreeSecond,zeroSite_add]
  congr 1
  ring

theorem tileThreeThird_rotation (T : CompletedTerrace n) (a q : ZMod h) :
    (Motion.rotation (zeroSite h n a)).onRow (T.tileThreeThird q)=T.tileThreeThird (q+a) := by
  have hqa : q+a-1=(q-1)+a := by ring
  rw [CompletedTerrace.tileThreeThird,row_rotation,CompletedTerrace.tileThreeThird,hqa,zeroSite_add]
  congr 1
  ring

def tileRowsAt (T : CompletedTerrace n) (q : ZMod h) : TileSize →
    Finset (Finset (ZMod (h*n)))
  | .two => {T.tileFirst q,T.tileTwoSecond q}
  | .three => {T.tileFirst q,T.tileThreeSecond q,T.tileThreeThird q}

theorem tileRowsAt_rotation (T : CompletedTerrace n) (a q : ZMod h) (s : TileSize) :
    (Motion.rotation (zeroSite h n a)).onFamily (tileRowsAt T q s)=tileRowsAt T (q+a) s := by
  cases s <;> simp only [tileRowsAt,Motion.onFamily,Finset.image_insert,
    Finset.image_singleton,tileFirst_rotation,tileTwoSecond_rotation,
    tileThreeSecond_rotation,tileThreeThird_rotation]

theorem layout_family_tileData (u : Layout h) (T : CompletedTerrace n) :
    u.toCyclicTiling.family T=
      u.tileData.biUnion (fun d => tileRowsAt T d.1 d.2) := by
  rw [Layout.tileData,Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro p _
  change u.toCyclicTiling.rows T p=tileRowsAt T (u.tileEndpoint p) (u.tileSize p)
  rfl

/-- The original physical tile family itself translates exactly with the
actual cyclic word. This is valid for every completed terrace. -/
theorem layout_family_rotation (u : Layout h) (T : CompletedTerrace n) (a : ZMod h) :
    (Motion.rotation (zeroSite h n a)).onFamily (u.toCyclicTiling.family T)=
      (Layout.toCyclicTiling (LocalWord.rotate (-a) u)).family T := by
  rw [layout_family_tileData,layout_family_tileData,Layout.tileData_rotate,
    Finset.image_biUnion]
  change (u.tileData.biUnion (fun d => tileRowsAt T d.1 d.2)).image
    (Motion.rotation (zeroSite h n a)).onRow=_
  rw [Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro d _
  simpa only [Motion.onFamily,sub_neg_eq_add] using tileRowsAt_rotation T a d.1 d.2

theorem endpoint_shift (a : ZMod h) (k : Bit m h) (s : Bool) :
    endpoint (n:=n) (k.1,k.2+a) s=endpoint (n:=n) k s+zeroSite h n a := by
  simp only [endpoint,zeroSite_add]
  ring

theorem pairShift_injective (a : ZMod h) :
    Function.Injective (pairShift (n:=n) a) := by
  intro e d he
  apply Prod.ext
  · exact add_right_cancel (congrArg Prod.fst he)
  · exact add_right_cancel (congrArg Prod.snd he)

theorem pairShift_mem_image (a : ZMod h)
    (U : Finset (ZMod (h*n) × ZMod (h*n))) (e : ZMod (h*n) × ZMod (h*n)) :
    pairShift a e∈U.image (pairShift a) ↔ e∈U := by
  constructor
  · intro he
    obtain ⟨d,hd,hde⟩ := Finset.mem_image.mp he
    exact (pairShift_injective a hde) ▸ hd
  · intro he
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩

theorem selectedMotion_endpoint (hsize : (5*m+8)^2≤n)
    (U : Finset (ZMod (h*n) × ZMod (h*n))) (k : Bit m h) (s : Bool) :
    selectedMotion (switchLayer hsize) U (endpoint (n:=n) k s)=
      if sitePair (n:=n) k∈U then endpoint (n:=n) k (!s) else endpoint (n:=n) k s := by
  cases s
  · exact selectedMotion_left (switchLayer hsize) U (sitePair k) (switchLayer_mem hsize k)
  · exact selectedMotion_right (switchLayer hsize) U (sitePair k) (switchLayer_mem hsize k)

theorem isolated_translation (hsize : (5*m+8)^2≤n) (a : ZMod h) (x : ZMod (h*n))
    (hx : (switchLayer hsize).Isolated x) :
    (switchLayer hsize).Isolated (zeroSite h n a+x) := by
  rw [switchLayer_isolated_iff] at hx ⊢
  intro k s he
  apply hx (k.1,k.2-a) s
  have hshift := endpoint_shift (n:=n) a (k.1,k.2-a) s
  simp only [sub_add_cancel] at hshift
  linear_combination he-hshift

/-- Conjugation of the actual simultaneous matching-layer permutation by
a whole-phase translation. The translated choice is literally the image
of its physical ordered pairs. No bit or cell permutation is postulated. -/
theorem selectedMotion_translation (hsize : (5*m+8)^2≤n) (a : ZMod h)
    (U : Finset (ZMod (h*n) × ZMod (h*n))) (x : ZMod (h*n)) :
    zeroSite h n a+selectedMotion (switchLayer hsize) U x=
      selectedMotion (switchLayer hsize) (U.image (pairShift a)) (zeroSite h n a+x) := by
  by_cases hx : ∃ (k : Bit m h) (s : Bool),endpoint (n:=n) k s=x
  · obtain ⟨k,s,rfl⟩ := hx
    have hinput : zeroSite h n a+endpoint (n:=n) k s=
        endpoint (n:=n) (k.1,k.2+a) s := by
      rw [endpoint_shift]
      ring
    rw [hinput,selectedMotion_endpoint,selectedMotion_endpoint]
    simp only [sitePair_shift,pairShift_mem_image]
    split_ifs <;> rw [endpoint_shift] <;> ring
  · have hi : (switchLayer hsize).Isolated x := by
      rw [switchLayer_isolated_iff]
      intro k s he
      exact hx ⟨k,s,he⟩
    rw [selectedMotion_isolated _ _ _ hi,
      selectedMotion_isolated _ _ _ (isolated_translation hsize a x hi)]

/-- Exact covariance of the switched physical family, before choosing
any special layout or using a marker reconstruction theorem. -/
theorem switchedFamily_translation (hsize : (5*m+8)^2≤n)
    (F : Finset (Finset (ZMod (h*n)))) (a : ZMod h)
    (U : Finset (ZMod (h*n) × ZMod (h*n))) :
    (Motion.rotation (zeroSite h n a)).onFamily (switchedFamily (switchLayer hsize) F U)=
      switchedFamily (switchLayer hsize)
        ((Motion.rotation (zeroSite h n a)).onFamily F) (U.image (pairShift a)) := by
  simp only [switchedFamily,imageFamily,Motion.onFamily,Motion.onRow,Finset.image_image,
    Function.comp_def,Motion.act]
  apply Finset.image_congr
  intro R _
  simp only [Finset.image_image,Function.comp_def]
  apply Finset.image_congr
  intro x _
  exact selectedMotion_translation hsize a U x

variable [NeZero (2*h-1)] [NeZero (h*(2*h-1))]

/-- At the translated phase the same block bit has exactly its original
truth value. In particular the physical action never complements bits. -/
theorem explicitShiftChoice_pair_mem (hh : 33≤h) (a : ZMod h) (U : SwitchChoice hh)
    (k : Bit (switchMultiplicity (2*h-1)) h) :
    sitePair (n:=2*h-1) (k.1,k.2+a)∈(explicitShiftChoice hh a U).1 ↔
      sitePair (n:=2*h-1) k∈U.1 := by
  change sitePair (n:=2*h-1) (k.1,k.2+a)∈U.1.image (pairShift a) ↔ _
  rw [sitePair_shift,pairShift_mem_image]

/-- A physical translation by +a phases is exactly `rotate (-a)` on the
cyclic layout and positive translation of every selected physical pair.
This is an unconditional equality for the actual anchored construction,
for every permitted terrace and every genuine switch choice. -/
theorem anchoredFamily_translation (hh : 33≤h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D)
    (u : Layout h) (U : SwitchChoice hh) (a : ZMod h) :
    (Motion.rotation (zeroSite h (2*h-1) a)).onFamily (anchoredFamily hh D hD (u,U))=
      anchoredFamily hh D hD (LocalWord.rotate (-a) u,explicitShiftChoice hh a U) := by
  change (Motion.rotation (zeroSite h (2*h-1) a)).onFamily
    (switchedFamily (switchLayer (explicitSizeBound hh))
      (u.toCyclicTiling.family (completedOfSpecifiedPrefix D (by omega) hD.1)) U.1)=_
  rw [switchedFamily_translation,layout_family_rotation]
  rfl

/-- The counted decorated-word convention rotates by positive
precomposition t, hence by physical translation -t phases. -/
theorem anchoredDecoratedFamily_rotation (hh : 33≤h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D)
    (t : ZMod h) (u : DecoratedLayout h (2^switchMultiplicity (2*h-1))) :
    anchoredDecoratedFamily hh D hD (t+ᵥu)=
      (Motion.rotation (zeroSite h (2*h-1) (-t))).onFamily (anchoredDecoratedFamily hh D hD u) := by
  rw [anchoredDecoratedFamily,decoratedPhysicalEquiv_rotate]
  symm
  simpa only [neg_neg,anchoredDecoratedFamily,Prod.mk.eta] using anchoredFamily_translation hh D hD
    (decoratedPhysicalEquiv hh u).1 (decoratedPhysicalEquiv hh u).2 (-t)

end
end CorralFormalization.Results.SwitchFamily.LayoutPhysicalEquivariance
