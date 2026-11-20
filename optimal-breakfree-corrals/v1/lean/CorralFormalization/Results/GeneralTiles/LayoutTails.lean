import CorralFormalization.Results.GeneralTiles.LocalTails
import CorralFormalization.DiversityCompletion.TailMarker

/-!
# Distinguished tails and recovery of an arbitrary cyclic layout
-/

namespace CorralFormalization.LatinCompletion.GeneralTiles

open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift

noncomputable def familyTails {M : ℕ} [NeZero M]
    (F : Finset (Finset (ZMod M))) (d : ℕ) : Finset (ZMod M) :=
  F.biUnion (fun R => gapTails R d)

def localTwoTails {M : ℕ} (n : ℕ) (s : TileSize) (z : ZMod M) : Finset (ZMod M) :=
  match s with
  | .two => {z-3,z}
  | .three => {z-3,z-(n : ZMod M)-3,z-2}

def localNTails {M : ℕ} (n : ℕ) (s : TileSize) (z : ZMod M) : Finset (ZMod M) :=
  match s with
  | .two => {z-1,z-(n : ZMod M)}
  | .three => {z-1,z-(n : ZMod M)+2,z-2*(n : ZMod M)}

namespace CyclicTiling

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def twoStarts (L : CyclicTiling h ι) : Finset (ZMod h) :=
  (Finset.univ.filter (fun i => L.size i = .two)).image L.start

def threeStarts (L : CyclicTiling h ι) : Finset (ZMod h) :=
  (Finset.univ.filter (fun i => L.size i = .three)).image L.start

def twoTailPattern (L : CyclicTiling h ι) (n : ℕ) : Finset (ZMod (h*n)) :=
  Finset.univ.biUnion (fun i => localTwoTails n (L.size i) (zeroSite h n (L.start i)))

def nTailPattern (L : CyclicTiling h ι) (n : ℕ) : Finset (ZMod (h*n)) :=
  Finset.univ.biUnion (fun i => localNTails n (L.size i) (zeroSite h n (L.start i)))

theorem rows_gap_two (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65 ≤ n) (i : ι) :
    familyTails (L.rows T i) 2 =
      localTwoTails n (L.size i) (zeroSite h n (L.start i)) := by
  obtain ⟨ha,hb,hc,hd⟩ := LocalTails.gap_two_tails hn hsmall T.body T.differences
    (zeroSite h n (L.start i))
  rw [← zeroSite_pred] at hd
  cases hs : L.size i <;>
    simp only [familyTails,rows,hs,Finset.biUnion_insert,Finset.singleton_biUnion,
      CompletedTerrace.tileFirst,CompletedTerrace.tileTwoSecond,
      CompletedTerrace.tileThreeSecond,CompletedTerrace.tileThreeThird,
      ha,hb,hc,hd,localTwoTails]
  all_goals
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]

theorem rows_gap_n (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65 ≤ n) (i : ι) :
    familyTails (L.rows T i) n =
      localNTails n (L.size i) (zeroSite h n (L.start i)) := by
  obtain ⟨ha,hb,hc,hd⟩ := TileGapWords.tile_tails hn (by omega : 15≤n)
    T.body T.differences (zeroSite h n (L.start i))
  rw [← zeroSite_pred] at hd
  cases hs : L.size i <;>
    simp only [familyTails,rows,hs,Finset.biUnion_insert,Finset.singleton_biUnion,
      CompletedTerrace.tileFirst,CompletedTerrace.tileTwoSecond,
      CompletedTerrace.tileThreeSecond,CompletedTerrace.tileThreeThird,
      ha,hb,hc,hd,localNTails]
  all_goals
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]

theorem gap_two_tails (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65 ≤ n) :
    familyTails (L.family T) 2 = L.twoTailPattern n := by
  simp only [familyTails,family,Finset.biUnion_biUnion]
  exact Finset.biUnion_congr rfl (fun i _ => L.rows_gap_two T hn hsmall i)

theorem gap_n_tails (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65 ≤ n) :
    familyTails (L.family T) n = L.nTailPattern n := by
  simp only [familyTails,family,Finset.biUnion_biUnion]
  exact Finset.biUnion_congr rfl (fun i _ => L.rows_gap_n T hn hsmall i)

theorem rows_gap_one (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65 ≤ n) (rest : List ℕ)
    (hbody : T.body=[7,1]++rest) (i : ι) :
    familyTails (L.rows T i) 1 =
      ((L.size i).block (L.start i)).image (fun q => zeroSite h n (q+2)+17) := by
  have hp : (TileGapWords.cycle n ([7,1]++rest)).Perm (fullGapList (n-1)) := by
    rw [← hbody]
    exact T.differences
  obtain ⟨ha,hb,hc,hd⟩ := LocalTails.gap_one_tails hn hsmall rest hp
    (zeroSite h n (L.start i))
  rw [← zeroSite_pred] at hd
  have hz2 (q : ZMod h) : zeroSite h n (q+2) = zeroSite h n q+2*(n : ZMod (h*n)) := by
    rw [zeroSite_add]
    have he := zeroSite_natCast h n 2
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using congrArg (zeroSite h n q+·) he
  have hpa : zeroSite h n (L.start i-1)+2*(n : ZMod (h*n)) =
      zeroSite h n (L.start i)+(n : ZMod (h*n)) := by
    rw [zeroSite_pred]
    ring
  have hpb : zeroSite h n (L.start i-2)+2*(n : ZMod (h*n)) = zeroSite h n (L.start i) := by
    rw [CompletedTerrace.zeroSite_two_pred]
    ring
  cases hs : L.size i <;>
    simp only [familyTails,rows,hs,Finset.biUnion_insert,Finset.singleton_biUnion,
      CompletedTerrace.tileFirst,CompletedTerrace.tileTwoSecond,
      CompletedTerrace.tileThreeSecond,CompletedTerrace.tileThreeThird,
      hbody,ha,hb,hc,hd,TileSize.block,Finset.image_insert,Finset.image_singleton,
      hz2,hpa,hpb]
  all_goals
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]

/-- The global gap-one tails are precisely all h physical sites of
residue 17, independently of the positions and types of the tiles. -/
theorem gap_one_tails (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65 ≤ n) (rest : List ℕ)
    (hbody : T.body=[7,1]++rest) :
    familyTails (L.family T) 1 =
      (Finset.univ : Finset (ZMod h)).image (fun q => zeroSite h n q+17) := by
  simp only [familyTails,family,Finset.biUnion_biUnion]
  change Finset.univ.biUnion (fun i => familyTails (L.rows T i) 1) = _
  simp_rw [L.rows_gap_one T hn hsmall rest hbody]
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,q,hq,he⟩
    exact ⟨q+2,he⟩
  · rintro ⟨q,he⟩
    obtain ⟨i,hi,_⟩ := L.partition (q-2)
    exact ⟨i,q-2,hi,by simpa using he⟩

end CyclicTiling

theorem local_two_filter_zero {h n : ℕ} (hsmall : 65≤n)
    (s : TileSize) (z : ZMod (h*n)) (hz : residueMap h n z=0) :
    (localTwoTails n s z).filter (fun x => residueMap h n x=0) =
      if s=.two then {z} else ∅ := by
  have h2 : (2 : ZMod n) ≠ 0 :=
    CorralLatinTailMarker.small_cast_ne_zero (n := n) (k := 2) (by decide) (by omega)
  have h3 : (3 : ZMod n) ≠ 0 :=
    CorralLatinTailMarker.small_cast_ne_zero (n := n) (k := 3) (by decide) (by omega)
  have hm2 : (-2 : ZMod n) ≠ 0 := neg_ne_zero.mpr h2
  have hm3 : (-3 : ZMod n) ≠ 0 := neg_ne_zero.mpr h3
  have r2 : residueMap h n (2 : ZMod (h*n)) = (2 : ZMod n) := by
    exact map_natCast (residueMap h n) 2
  have r3 : residueMap h n (3 : ZMod (h*n)) = (3 : ZMod n) := by
    exact map_natCast (residueMap h n) 3
  cases s <;> simp [localTwoTails,Finset.filter_insert,Finset.filter_singleton,
    map_sub,hz,hm2,hm3,r2,r3]

theorem local_two_filter_neg_two {h n : ℕ} (hsmall : 65≤n)
    (s : TileSize) (z : ZMod (h*n)) (hz : residueMap h n z=0) :
    (localTwoTails n s z).filter (fun x => residueMap h n x= -2) =
      if s=.three then {z-2} else ∅ := by
  have h2 : (2 : ZMod n) ≠ 0 :=
    CorralLatinTailMarker.small_cast_ne_zero (n := n) (k := 2) (by decide) (by omega)
  have h1 : (1 : ZMod n) ≠ 0 := by
    simpa using CorralLatinTailMarker.small_cast_ne_zero (n := n) (k := 1) (by decide) (by omega)
  have h32 : (-3 : ZMod n) ≠ -2 := by
    intro he
    apply h1
    linear_combination -he
  have h02 : (0 : ZMod n) ≠ -2 := by
    intro he
    apply h2
    linear_combination he
  have r2 : residueMap h n (2 : ZMod (h*n)) = (2 : ZMod n) := by
    exact map_natCast (residueMap h n) 2
  have r3 : residueMap h n (3 : ZMod (h*n)) = (3 : ZMod n) := by
    exact map_natCast (residueMap h n) 3
  cases s <;> simp [localTwoTails,Finset.filter_insert,Finset.filter_singleton,
    map_sub,hz,h32,h02,r2,r3]

namespace CyclicTiling

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Residue-zero gap-two tails recover exactly the two-tile starts. -/
theorem recover_two_starts (L : CyclicTiling h ι) (hsmall : 65≤n) :
    (L.twoTailPattern n).filter (fun x => residueMap h n x=0) =
      L.twoStarts.image (zeroSite h n) := by
  rw [twoTailPattern,Finset.filter_biUnion]
  simp_rw [local_two_filter_zero hsmall _ _ (zeroSite_residue _ _ _)]
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,twoStarts,
    Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨i,hi⟩
    split_ifs at hi with hs
    · exact ⟨L.start i,⟨i,hs,rfl⟩,(Finset.mem_singleton.mp hi).symm⟩
    · simp at hi
  · rintro ⟨q,⟨i,hi,hq⟩,he⟩
    rw [← hq] at he
    exact ⟨i,by simpa [hi] using he.symm⟩

/-- Residue-(n-2) gap-two tails recover exactly the three-tile starts,
after restoring the literal offset two. -/
theorem recover_three_starts (L : CyclicTiling h ι) (hsmall : 65≤n) :
    (L.twoTailPattern n).filter (fun x => residueMap h n x= -2) =
      L.threeStarts.image (fun q => zeroSite h n q-2) := by
  rw [twoTailPattern,Finset.filter_biUnion]
  simp_rw [local_two_filter_neg_two hsmall _ _ (zeroSite_residue _ _ _)]
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,threeStarts,
    Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨i,hi⟩
    split_ifs at hi with hs
    · exact ⟨L.start i,⟨i,hs,rfl⟩,(Finset.mem_singleton.mp hi).symm⟩
    · simp at hi
  · rintro ⟨q,⟨i,hi,hq⟩,he⟩
    rw [← hq] at he
    exact ⟨i,by simpa [hi] using he.symm⟩

/-- Equality of the actual gap-two tails determines an arbitrary layout,
including layouts with no three-tile. Labels of tiles are immaterial. -/
theorem layout_reconstruction {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : CyclicTiling h ι) (K : CyclicTiling h κ) (hsmall : 65≤n)
    (htails : L.twoTailPattern n=K.twoTailPattern n) :
    L.twoStarts=K.twoStarts ∧ L.threeStarts=K.threeStarts := by
  have hi0 := congrArg (Finset.filter (fun x => residueMap h n x=0)) htails
  have hi2 := congrArg (Finset.filter (fun x => residueMap h n x= -2)) htails
  rw [L.recover_two_starts hsmall,K.recover_two_starts hsmall] at hi0
  rw [L.recover_three_starts hsmall,K.recover_three_starts hsmall] at hi2
  refine ⟨Finset.image_injective (zeroSite_injective (NeZero.pos n)) hi0,?_⟩
  apply Finset.image_injective (f := fun q => zeroSite h n q-2) ?_ hi2
  intro q p he
  exact zeroSite_injective (NeZero.pos n) (sub_left_injective he)

end CyclicTiling

end CorralFormalization.LatinCompletion.GeneralTiles
