import CorralFormalization.Results.GeneralTiles.DirectedInput
import CorralFormalization.DiversityCompletion.LatinPrefixFrame

/-!
# The unchanged directed path from 17 through the final vertex

The assertion is made with actual clockwise adjacency in the physical row,
for every successive edge of the original suffix calendar.
-/

namespace CorralFormalization.LatinCompletion.GeneralTiles

open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift LatinPrefix

theorem row_adjacent_at {M : ℕ} [NeZero M] (o : ZMod M) (w : List ℕ)
    (hpos : ∀ x∈w,0<x) (hsum : w.sum=M) (hlen : 2≤w.length)
    (k : ℕ) (hk : k+1<w.length) :
    Adjacent (TileGapWords.row o w)
      (o+(((w.take k).sum : ℕ) : ZMod M))
      (o+(((w.take (k+1)).sum : ℕ) : ZMod M)) := by
  let : NeZero w.length := ⟨by omega⟩
  obtain ⟨E,hsite,_⟩ := cyclicRow_of_positive_word w rfl hpos hsum hlen
  have hrow : TileGapWords.row o w =
      (Motion.rotation o).onRow (wordSites M w.length w) := by
    rw [wordSites_eq_physicalPrefixes w rfl]
    simp only [TileGapWords.row,physicalOffsets,Motion.onRow,physicalSites,
      Finset.image_image,Function.comp_def,Motion.act,Nat.cast_add,ZMod.natCast_zmod_val]
  have hval : (k : ZMod w.length).val=k := ZMod.val_natCast_of_lt (by omega)
  have hnext : ((k : ZMod w.length)+1).val=k+1 := by
    rw [← Nat.cast_one,← Nat.cast_add]
    exact ZMod.val_natCast_of_lt hk
  rw [hrow]
  simpa only [hsite,hval,hnext] using adjacent_rotation (E.consecutive (k : ZMod w.length)) o

theorem row_segment_adjacent {M : ℕ} [NeZero M] (o : ZMod M)
    (pre u post : List ℕ) (hpost : post≠[])
    (hpos : ∀ x∈pre++(u++post),0<x)
    (hsum : (pre++(u++post)).sum=M) (hlen : 2≤(pre++(u++post)).length)
    (k : ℕ) (hk : k<u.length) :
    Adjacent (TileGapWords.row o (pre++(u++post)))
      (o+(pre.sum : ZMod M)+(((u.take k).sum : ℕ) : ZMod M))
      (o+(pre.sum : ZMod M)+(((u.take (k+1)).sum : ℕ) : ZMod M)) := by
  have ht (j : ℕ) (hj : j≤u.length) :
      ((pre++(u++post)).take (pre.length+j)).sum=pre.sum+(u.take j).sum := by
    rw [List.take_append,List.take_of_length_le (by omega),Nat.add_sub_cancel_left,
      List.take_append_of_le_length hj,List.sum_append]
  have hpostlen : 0<post.length := List.length_pos_iff.mpr hpost
  have h := row_adjacent_at o (pre++(u++post)) hpos hsum hlen
    (pre.length+k) (by simp only [List.length_append]; omega)
  have htake0 := ht k (by omega)
  have htake1 := ht (k+1) (by omega)
  have hadd : pre.length+k+1=pre.length+(k+1) := by omega
  simpa only [hadd,htake0,htake1,Nat.cast_add,add_assoc] using h

def beforeSeventeen (n : ℕ) : RowRole → List ℕ
  | .first => [3,10,n-14,12,7]
  | .secondTwo => [10,n-14,12,7]
  | .secondThree => [10,n-14,12,7]
  | .third => [n-14,2,10,7]

def afterSegment (n : ℕ) : RowRole → List ℕ
  | .first => [2,n]
  | .secondTwo => [3,n,2]
  | .secondThree => [2,3,n]
  | .third => [3,n,12]

def tileOrigin {M : ℕ} (n : ℕ) (z : ZMod M) : RowRole → ZMod M
  | .first => z+((n-1 : ℕ) : ZMod M)
  | .secondTwo => z+2
  | .secondThree => z+2
  | .third => z-(n : ZMod M)+12

def segmentPhase {M : ℕ} (n : ℕ) (z : ZMod M) : RowRole → ZMod M
  | .first => z+2*(n : ZMod M)
  | .secondTwo => z+(n : ZMod M)
  | .secondThree => z+(n : ZMod M)
  | .third => z

theorem roleWord_segment {n : ℕ} (T : CompletedTerrace n) (rest : List ℕ)
    (hbody : T.body=[7,1]++rest) (role : RowRole) :
    roleWord T role=beforeSeventeen n role++((1::rest)++afterSegment n role) := by
  cases role <;> simp [roleWord,beforeSeventeen,afterSegment,TileGapWords.first,
    TileGapWords.cycle,TileGapWords.twoSecond,TileGapWords.middle,
    TileGapWords.threeSecond,TileGapWords.threeThird,TileGapWords.thirdPrefix,hbody]

theorem segment_start {M n : ℕ} (hn : 65≤n) (z : ZMod M) (role : RowRole) :
    tileOrigin n z role+((beforeSeventeen n role).sum : ZMod M)=segmentPhase n z role+17 := by
  have hs1 : ((n-1 : ℕ) : ZMod M)=(n : ZMod M)-1 := by
    rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  have hs14 : ((n-14 : ℕ) : ZMod M)=(n : ZMod M)-14 := by
    rw [Nat.cast_sub (by omega : 14≤n),Nat.cast_ofNat]
  cases role <;>
    simp only [tileOrigin,beforeSeventeen,segmentPhase,List.sum_cons,List.sum_nil,
      Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,hs1,hs14] <;> ring

/-- Every successive physical edge of the original path 17→18→...→n-3
survives unchanged in all four row roles. This concerns actual `Adjacent`
edges, rather than only equality of palettes or residue lists. -/
theorem unchanged_segment {h n : ℕ} [NeZero (h*n)] (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ) (hbody : T.body=[7,1]++rest)
    (z : ZMod (h*n)) (role : RowRole) (k : ℕ) (hk : k<(1::rest).length) :
    Adjacent (TileGapWords.row (tileOrigin n z role) (roleWord T role))
      (segmentPhase n z role+17+((((1::rest).take k).sum : ℕ) : ZMod (h*n)))
      (segmentPhase n z role+17+((((1::rest).take (k+1)).sum : ℕ) : ZMod (h*n))) := by
  have hp := roleWord_perm T (by omega : 0<n) role
  obtain ⟨hpos,hsum,hlen⟩ := TileGapWords.word_properties hn (by omega) _ hp
  have hpost : afterSegment n role≠[] := by cases role <;> simp [afterSegment]
  have he := roleWord_segment T rest hbody role
  rw [he] at hpos hsum hlen ⊢
  have h := row_segment_adjacent (tileOrigin n z role) (beforeSeventeen n role)
    (1::rest) (afterSegment n role) hpost hpos hsum (by omega) k hk
  rw [segment_start hsmall z role] at h
  exact h

theorem unchanged_segment_endpoints {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (rest : List ℕ) (hbody : T.body=[7,1]++rest) (p : ZMod h) (role : RowRole) :
    residueMap h n (segmentPhase n (zeroSite h n p) role+17)=17 ∧
    residueMap h n (segmentPhase n (zeroSite h n p) role+17+
      (((1::rest).sum : ℕ) : ZMod (h*n)))=((n-3 : ℕ) : ZMod n) := by
  have hp := TileGapWords.first_perm (by omega : 0<n) T.body T.differences
  have hs := (TileGapWords.word_properties hn (by omega) _ hp).2.1
  have hsum : (1::rest).sum+2*n+20=h*n := by
    simp [TileGapWords.first,TileGapWords.cycle,hbody] at hs
    simp only [List.sum_cons]
    omega
  have he := congrArg (fun k : ℕ => (k : ZMod n)) hsum
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,Nat.cast_ofNat,
    add_zero] at he
  have hres : residueMap h n (segmentPhase n (zeroSite h n p) role)=0 := by
    cases role <;> simp [segmentPhase,map_add,map_mul,zeroSite_residue]
  have h17 : residueMap h n (17 : ZMod (h*n))=(17 : ZMod n) :=
    map_natCast (residueMap h n) 17
  have h3 : ((n-3 : ℕ) : ZMod n)= -3 := by
    rw [Nat.cast_sub (by omega : 3≤n),ZMod.natCast_self,Nat.cast_ofNat]
    simp
  constructor
  · simp only [map_add,hres,h17,zero_add]
  · rw [map_add,map_add,hres,h17,map_natCast,h3]
    linear_combination he

theorem CyclicTiling.every_row_unchanged_segment
    {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : CyclicTiling h ι) (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (rest : List ℕ) (hbody : T.body=[7,1]++rest)
    (R : Finset (ZMod (h*n))) (hR : R∈L.family T) :
    ∃ p : ZMod h, ∃ role : RowRole,
      R=TileGapWords.row (tileOrigin n (zeroSite h n p) role) (roleWord T role) ∧
      ∀ k, k<(1::rest).length →
        Adjacent R
          (segmentPhase n (zeroSite h n p) role+17+
            ((((1::rest).take k).sum : ℕ) : ZMod (h*n)))
          (segmentPhase n (zeroSite h n p) role+17+
            ((((1::rest).take (k+1)).sum : ℕ) : ZMod (h*n))) := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hR
  have hrole : ∃ role : RowRole,
      R=TileGapWords.row (tileOrigin n (zeroSite h n (L.start i)) role) (roleWord T role) := by
    cases hs : L.size i <;>
      simp only [CyclicTiling.rows,hs,Finset.mem_insert,Finset.mem_singleton] at hi
    · rcases hi with rfl | rfl
      · exact ⟨.first,rfl⟩
      · exact ⟨.secondTwo,rfl⟩
    · rcases hi with rfl | rfl | rfl
      · exact ⟨.first,rfl⟩
      · exact ⟨.secondThree,rfl⟩
      · exact ⟨.third,by simp [CompletedTerrace.tileThreeThird,tileOrigin,roleWord,zeroSite_pred]⟩
  obtain ⟨role,rfl⟩ := hrole
  exact ⟨L.start i,role,rfl,fun k hk => unchanged_segment T hn hsmall rest hbody
    (zeroSite h n (L.start i)) role k hk⟩

end CorralFormalization.LatinCompletion.GeneralTiles
