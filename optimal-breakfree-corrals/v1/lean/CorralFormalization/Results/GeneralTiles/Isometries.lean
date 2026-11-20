import CorralFormalization.Results.GeneralTiles.Modifications

/-!
# General physical isometries, including modified arbitrary layouts

The gap-one coset first fixes the residue of an isometry. A residue-(n-3)
gap-two tail then excludes reflections, even for all-two layouts. The two
decoding filters show that the remaining phase translation carries the
whole recovered layout to the other layout.
-/

namespace CorralFormalization.LatinCompletion.GeneralTiles

open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift

def oneTailPattern (h n : ℕ) [NeZero h] : Finset (ZMod (h*n)) :=
  (Finset.univ : Finset (ZMod h)).image (fun q => zeroSite h n q+17)

theorem mem_oneTailPattern {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (x : ZMod (h*n)) : x∈oneTailPattern h n ↔ residueMap h n x=17 := by
  have h17 : residueMap h n (17 : ZMod (h*n))=(17 : ZMod n) :=
    map_natCast (residueMap h n) 17
  constructor
  · intro hx
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
    simp [map_add,zeroSite_residue,h17]
  · intro hx
    have hz : residueMap h n (x-17)=0 := by simp [map_sub,hx,h17]
    obtain ⟨q,hq,_⟩ := (zeroSite_exactly_once _).mp hz
    exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,by rw [hq]; ring⟩

namespace CyclicTiling

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem twoTailPattern_residues (L : CyclicTiling h ι) (x : ZMod (h*n))
    (hx : x∈L.twoTailPattern n) :
    residueMap h n x= -3 ∨ residueMap h n x=0 ∨ residueMap h n x= -2 := by
  have h2 : residueMap h n (2 : ZMod (h*n))=(2 : ZMod n) :=
    map_natCast (residueMap h n) 2
  have h3 : residueMap h n (3 : ZMod (h*n))=(3 : ZMod n) :=
    map_natCast (residueMap h n) 3
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
  cases hs : L.size i <;>
    simp only [localTwoTails,hs,Finset.mem_insert,Finset.mem_singleton] at hi
  · rcases hi with rfl | rfl <;> simp [map_sub,zeroSite_residue,h2,h3]
  · rcases hi with rfl | rfl | rfl <;> simp [map_sub,zeroSite_residue,h2,h3]

theorem twoTailPattern_has_minus_three (L : CyclicTiling h ι) :
    ∃ x∈L.twoTailPattern n,residueMap h n x= -3 := by
  have h3 : residueMap h n (3 : ZMod (h*n))=(3 : ZMod n) :=
    map_natCast (residueMap h n) 3
  obtain ⟨i,_,_⟩ := L.partition 0
  refine ⟨zeroSite h n (L.start i)-3,?_,by simp [map_sub,zeroSite_residue,h3]⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,?_⟩
  cases hs : L.size i <;> simp [localTwoTails,hs]

theorem translated_layout_reconstruction {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : CyclicTiling h ι) (K : CyclicTiling h κ) (hsmall : 65≤n) (a : ZMod h)
    (htails : (L.twoTailPattern n).image (fun x => zeroSite h n a+x)=K.twoTailPattern n) :
    L.twoStarts.image (fun q => a+q)=K.twoStarts ∧
      L.threeStarts.image (fun q => a+q)=K.threeStarts := by
  have hi0 := congrArg (Finset.filter (fun x => residueMap h n x=0)) htails
  have hi2 := congrArg (Finset.filter (fun x => residueMap h n x= -2)) htails
  rw [Finset.filter_image] at hi0 hi2
  simp only [map_add,zeroSite_residue,zero_add] at hi0 hi2
  rw [L.recover_two_starts hsmall,K.recover_two_starts hsmall] at hi0
  rw [L.recover_three_starts hsmall,K.recover_three_starts hsmall] at hi2
  constructor
  · apply Finset.image_injective (zeroSite_injective (NeZero.pos n))
    simpa only [Finset.image_image,Function.comp_def,zeroSite_add] using hi0
  · apply Finset.image_injective (f := fun q => zeroSite h n q-2)
      (fun q p he => zeroSite_injective (NeZero.pos n) (sub_left_injective he))
    have he (q : ZMod h) : zeroSite h n (a+q)-2 = zeroSite h n a+(zeroSite h n q-2) := by
      rw [zeroSite_add]
      ring
    simpa only [Finset.image_image,Function.comp_def,he] using hi2

/-- The full general isometry conclusion from the actual one/two-tail
sets. No three-tile, canonical layout or row-modification restriction is
needed beyond these already calculated invariants. -/
theorem marker_isometry {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : CyclicTiling h ι) (K : CyclicTiling h κ) (hsmall : 65≤n)
    (F G : Finset (Finset (ZMod (h*n))))
    (hF1 : familyTails F 1=oneTailPattern h n) (hG1 : familyTails G 1=oneTailPattern h n)
    (hF2 : familyTails F 2=L.twoTailPattern n) (hG2 : familyTails G 2=K.twoTailPattern n)
    (f : Motion (h*n)) (hf : f.onFamily F=G) :
    ∃ a : ZMod h, f=.rotation (zeroSite h n a) ∧
      L.twoStarts.image (fun q => a+q)=K.twoStarts ∧
      L.threeStarts.image (fun q => a+q)=K.threeStarts := by
  have h17 : residueMap h n (17 : ZMod (h*n))=(17 : ZMod n) :=
    map_natCast (residueMap h n) 17
  have h2 : residueMap h n (2 : ZMod (h*n))=(2 : ZMod n) :=
    map_natCast (residueMap h n) 2
  have hbase : (17 : ZMod (h*n))∈oneTailPattern h n :=
    (mem_oneTailPattern _).mpr h17
  cases f with
  | rotation c =>
    have hrot1 : (oneTailPattern h n).image (fun x => c+x)=oneTailPattern h n := by
      have he := (familyTails_rotation F c 1).symm
      simpa only [hf,hF1,hG1] using he
    have htail : c+17∈oneTailPattern h n := by
      rw [← hrot1]
      exact Finset.mem_image_of_mem _ hbase
    have hc : residueMap h n c=0 := by
      have he := (mem_oneTailPattern _).mp htail
      rw [map_add,h17] at he
      linear_combination he
    obtain ⟨a,ha,_⟩ := (zeroSite_exactly_once _).mp hc
    have hrot2 : (L.twoTailPattern n).image (fun x => zeroSite h n a+x)=K.twoTailPattern n := by
      rw [ha]
      have he := (familyTails_rotation F c 2).symm
      simpa only [hf,hF2,hG2] using he
    obtain ⟨htwo,hthree⟩ := L.translated_layout_reconstruction K hsmall a hrot2
    exact ⟨a,by rw [ha],htwo,hthree⟩
  | reflection c =>
    have href1 : (oneTailPattern h n).image (fun x => c-1-x)=oneTailPattern h n := by
      have he := (familyTails_reflection F c 1).symm
      simpa only [hf,hF1,hG1,Nat.cast_one] using he
    have htail : c-1-17∈oneTailPattern h n := by
      rw [← href1]
      exact Finset.mem_image_of_mem _ hbase
    have hc : residueMap h n c=35 := by
      have he := (mem_oneTailPattern _).mp htail
      rw [map_sub,map_sub,map_one,h17] at he
      linear_combination he
    obtain ⟨x,hx,hxres⟩ := L.twoTailPattern_has_minus_three (n := n)
    have href2 : (L.twoTailPattern n).image (fun x => c-2-x)=K.twoTailPattern n := by
      have he := (familyTails_reflection F c 2).symm
      simpa only [hf,hF2,hG2,Nat.cast_ofNat] using he
    have him : c-2-x∈K.twoTailPattern n := by
      rw [← href2]
      exact Finset.mem_image_of_mem _ hx
    have h36 : residueMap h n (c-2-x)=36 := by
      rw [map_sub,map_sub,hc,h2,hxres]
      norm_num
    have hn36 : (36 : ZMod n)≠0 :=
      CorralLatinTailMarker.small_cast_ne_zero (n := n) (k := 36) (by decide) (by omega)
    have hn38 : (38 : ZMod n)≠0 :=
      CorralLatinTailMarker.small_cast_ne_zero (n := n) (k := 38) (by decide) (by omega)
    have hn39 : (39 : ZMod n)≠0 :=
      CorralLatinTailMarker.small_cast_ne_zero (n := n) (k := 39) (by decide) (by omega)
    rcases K.twoTailPattern_residues _ him with he | he | he
    · exfalso
      apply hn39
      linear_combination he-h36
    · exact False.elim (hn36 (h36.symm.trans he))
    · exfalso
      apply hn38
      linear_combination he-h36

/-- Arbitrary full-palette row modifications preserving only the original
edges 1, 2, n satisfy the general rotation/layout conclusion. The two
terraces may differ after the prescribed initial path. -/
theorem modified_isometry {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : CyclicTiling h ι) (K : CyclicTiling h κ) (T U : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n)
    (restT restU : List ℕ) (hT : T.body=[7,1]++restT) (hU : U.body=[7,1]++restU)
    (P : RowModification n (L.family T)) (Q : RowModification n (K.family U))
    (f : Motion (h*n)) (hf : f.onFamily P.family=Q.family) :
    ∃ a : ZMod h, f=.rotation (zeroSite h n a) ∧
      L.twoStarts.image (fun q => a+q)=K.twoStarts ∧
      L.threeStarts.image (fun q => a+q)=K.threeStarts := by
  apply L.marker_isometry K hsmall P.family Q.family
    (L.modified_gap_one_tails T hn hsmall restT hT P)
    (K.modified_gap_one_tails U hn hsmall restU hU Q)
    (L.modified_gap_two_tails T hn hsmall P)
    (K.modified_gap_two_tails U hn hsmall Q) f hf

theorem marked_three_starts_rotation_zero (hh : 7≤h)
    (B : Finset (ZMod h)) (p a : ZMod h)
    (hB : B={p} ∨ B={p,p-3})
    (hrot : B.image (fun q => a+q)=B) : a=0 := by
  have h3 : (3 : ZMod h)≠0 :=
    CorralLatinTailMarker.small_cast_ne_zero (n := h) (k := 3) (by decide) (by omega)
  have h6 : (6 : ZMod h)≠0 :=
    CorralLatinTailMarker.small_cast_ne_zero (n := h) (k := 6) (by decide) (by omega)
  have him (q : ZMod h) (hq : q∈B) : a+q∈B := by
    rw [← hrot]
    exact Finset.mem_image_of_mem _ hq
  rcases hB with rfl | rfl
  · have he := him p (by simp)
    simp only [Finset.mem_singleton] at he
    linear_combination he
  · have he := him p (by simp)
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with he | he
    · linear_combination he
    · have he' := him (p-3) (by simp)
      simp only [Finset.mem_insert,Finset.mem_singleton] at he'
      rcases he' with he' | he'
      · exfalso
        apply h6
        linear_combination he-he'
      · exfalso
        apply h3
        linear_combination he-he'

/-- The two layouts singled out by the paper have only the identity
physical isometry, after arbitrary allowed modifications. This statement
uses exactly one three-tile or two starts three phases apart; parity is
irrelevant once that literal layout condition is supplied. -/
theorem modified_same_layout_identity
    (L : CyclicTiling h ι) (T U : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n)
    (restT restU : List ℕ) (hT : T.body=[7,1]++restT) (hU : U.body=[7,1]++restU)
    (P : RowModification n (L.family T)) (Q : RowModification n (L.family U))
    (p : ZMod h) (hthree : L.threeStarts={p} ∨ L.threeStarts={p,p-3})
    (f : Motion (h*n)) (hf : f.onFamily P.family=Q.family) : f=.rotation 0 := by
  obtain ⟨a,ha,_,hstarts⟩ := L.modified_isometry L T U hn hsmall
    restT restU hT hU P Q f hf
  have ha0 := marked_three_starts_rotation_zero (by omega : 7≤h)
    L.threeStarts p a hthree hstarts
  simpa [ha0,zeroSite] using ha

end CyclicTiling

end CorralFormalization.LatinCompletion.GeneralTiles
