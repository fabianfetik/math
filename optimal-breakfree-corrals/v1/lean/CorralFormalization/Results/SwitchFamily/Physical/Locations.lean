import CorralFormalization.Results.SwitchFamily.Physical.Geometry

/-! Exact positive-lift locations of every Appendix A moving center. -/

namespace CorralFormalization.Results.SwitchFamily.Physical

open CorralFormalization CorralFormalization.LatinCompletion
open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift GeneralTiles LatinPrefix

theorem locatedCells_flatMap_member {I J : Type*} (A B : I → ℕ)
    (f : J → List (Piece I)) (xs : List J) (c : I) (p : ℕ)
    (hp : (c,p)∈locatedCells A B (xs.flatMap f)) :
    ∃ k, ∃ hk : k<xs.length, ∃ u,
      (c,u)∈locatedCells A B (f xs[k]) ∧
      p=(((xs.take k).flatMap f).map (Piece.weight A B)).sum+u := by
  induction xs generalizing p with
  | nil => simp [locatedCells] at hp
  | cons x xs ih =>
    rw [List.flatMap_cons,locatedCells_append] at hp
    rcases List.mem_append.mp hp with hhead|htail
    · exact ⟨0,by simp,p,hhead,by simp⟩
    · obtain ⟨⟨a,u⟩,hu,he⟩ := List.mem_map.mp htail
      have hac : a=c := congrArg Prod.fst he
      subst a
      have hpu : ((f x).map (Piece.weight A B)).sum+u=p := congrArg Prod.snd he
      obtain ⟨k,hk,v,hv,huv⟩ := ih u hu
      refine ⟨k+1,by simpa using Nat.succ_lt_succ hk,v,hv,?_⟩
      simp only [List.take_succ_cons,List.flatMap_cons,List.map_append,List.sum_append]
      omega

theorem switchPrefix_weight {n m k : ℕ} (hk : k ≤ m) :
    (List.map (Piece.weight cellBase (fun c : Cell m => cellBase c+1))
      (((List.finRange m).take k).flatMap (blockPieces n))).sum=
        ((List.range k).flatMap (Prefix.blockColors n)).sum := by
  have htake : ((List.finRange m).take k).map Fin.val=List.range k := by
    rw [List.map_take,map_val_finRange]
    simp [List.take_range,Nat.min_eq_left hk]
  rw [← binary_word_sum _ _ originalSetting,word_flatMap]
  simp_rw [blockPieces_word]
  rw [← htake,List.flatMap_map]

theorem switchPieces_location {n m : ℕ} (hn : 65≤n) (hsize : (5*m+8)^2≤n)
    (c : Cell m) (p : ℕ)
    (hp : (c,p)∈locatedCells cellBase (fun c : Cell m => cellBase c+1)
      (switchPieces n m)) :
    18+p+cellBase c+(originalSetting c).toNat=
      Prefix.center c.1.val+(c.1.val+c.2.toNat)*n+c.2.toNat := by
  obtain ⟨k,hk,u,hu,hpu⟩ := locatedCells_flatMap_member cellBase
    (fun c : Cell m => cellBase c+1) (blockPieces n) (List.finRange m) c p hp
  have hk' : k < m := by simpa using hk
  have hi : (List.finRange m)[k]=⟨k,hk'⟩ := by simp
  rw [hi] at hu
  rw [switchPrefix_weight (by omega : k ≤ m)] at hpu
  have hlift := Prefix.centers_positive_lift hn hsize (by omega : k ≤ m)
  have hs := Prefix.color_separation hn hsize hk'
  have hsub : Prefix.alpha k+Prefix.beta k+1≤n := by omega
  have hcancel := Nat.sub_add_cancel hsub
  simp only [blockPieces,locatedCells,cellBase,Bool.false_eq_true,↓reduceIte,
    Bool.toNat_false,Bool.toNat_true,List.map_cons,List.map_nil,Piece.weight,
    List.mem_cons,List.not_mem_nil,or_false,Nat.add_zero] at hu
  rcases hu with he|he
  · have hc : c=(⟨k,hk'⟩,false) := congrArg Prod.fst he
    have hu0 : u=0 := congrArg Prod.snd he
    subst c
    subst u
    simp only [cellBase,originalSetting,Bool.false_eq_true,↓reduceIte,
      Bool.toNat_false,Nat.add_zero,Nat.zero_add] at *
    omega
  · have hc : c=(⟨k,hk'⟩,true) := congrArg Prod.fst he
    have hu0 := congrArg Prod.snd he
    subst c
    simp only [cellBase,originalSetting,↓reduceIte,Bool.toNat_true,Fin.val_mk] at *
    nlinarith

theorem tilePieces_locations {n m : ℕ} (rest : List ℕ) (role : RowRole) :
    locatedCells cellBase (fun c : Cell m => cellBase c+1) (tilePieces n m rest role)=
      (locatedCells cellBase (fun c : Cell m => cellBase c+1) (switchPieces n m)).map
        (fun p => (p.1,(beforeSeventeen n role).sum+1+p.2)) := by
  simp [tilePieces,suffixPieces,locatedCells_append,locatedCells_fixedPieces,
    weights_fixedPieces,List.sum_append,List.map_map,Function.comp_def,Nat.add_assoc]

def segmentPhaseIndex {h : ℕ} (p : ZMod h) : RowRole → ZMod h
  | .first => p+2
  | .secondTwo => p+1
  | .secondThree => p+1
  | .third => p

theorem segmentPhase_eq {h n : ℕ} [NeZero h] (p : ZMod h) (role : RowRole) :
    segmentPhase n (zeroSite h n p) role=zeroSite h n (segmentPhaseIndex p role) := by
  have h1 : zeroSite h n (1 : ZMod h)=(n : ZMod (h*n)) := by
    simpa using zeroSite_natCast h n 1
  have h2 : zeroSite h n (2 : ZMod h)=2*(n : ZMod (h*n)) := by
    simpa using zeroSite_natCast h n 2
  cases role <;> simp [segmentPhase,segmentPhaseIndex,zeroSite_add,h1,h2]

def cellPhase {h m : ℕ} (p : ZMod h) (role : RowRole) (c : Cell m) : ZMod h :=
  segmentPhaseIndex p role+((c.1.val+c.2.toNat : ℕ) : ZMod h)

/-- In an actual tile row the x-center has phase `segment+i`, and the
y-center has phase `segment+i+1`. Their positive displacement is n+1. -/
theorem tileWordFrame_center {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (q : ZMod h) (role : RowRole) (c : Cell m) (p : ℕ)
    (hp : (c,p)∈locatedCells cellBase (fun c : Cell m => cellBase c+1)
      (tilePieces n m rest role)) :
    (((tileWordFrame T hn hsmall rest hbody (zeroSite h n q) role).origin+
      (p+cellBase c+(originalSetting c).toNat) : ℕ) : ZMod (h*n))=
        endpoint (n:=n) (c.1,cellPhase q role c) c.2 := by
  rw [tilePieces_locations rest role] at hp
  obtain ⟨⟨a,u⟩,hu,he⟩ := List.mem_map.mp hp
  have hac : a=c := congrArg Prod.fst he
  subst a
  have hpu : (beforeSeventeen n role).sum+1+u=p := congrArg Prod.snd he
  have hloc := switchPieces_location hsmall hsize c u hu
  have hstart := segment_start hsmall (zeroSite h n q) role
  change (((tileOrigin n (zeroSite h n q) role).val+
    (p+cellBase c+(originalSetting c).toNat) : ℕ) : ZMod (h*n))=_
  rw [Nat.cast_add,ZMod.natCast_zmod_val]
  have hsum : p+cellBase c+(originalSetting c).toNat=
      (beforeSeventeen n role).sum+
        (Prefix.center c.1.val+(c.1.val+c.2.toNat)*n+c.2.toNat)-17 := by omega
  have hsum' : p+cellBase c+(originalSetting c).toNat+17=
      (beforeSeventeen n role).sum+
        (Prefix.center c.1.val+(c.1.val+c.2.toNat)*n+c.2.toNat) := by omega
  have hcast := congrArg (fun k : ℕ => (k : ZMod (h*n))) hsum'
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hcast
  dsimp only [endpoint,cellPhase]
  rw [zeroSite_add,zeroSite_natCast]
  simp only [Nat.cast_add,Nat.cast_mul]
  rw [← segmentPhase_eq]
  linear_combination hcast+hstart

theorem cells_flatMap {I J : Type*} (f : J → List (Piece I)) (xs : List J) :
    cells (xs.flatMap f)=xs.flatMap (fun j => cells (f j)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cells_append,ih]

theorem tilePieces_cell_mem {n m : ℕ} (rest : List ℕ) (role : RowRole) (c : Cell m) :
    c∈cells (tilePieces n m rest role) := by
  rcases c with ⟨i,s⟩
  simp only [tilePieces,suffixPieces,cells_append,cells_fixedPieces,
    List.nil_append,List.append_nil,switchPieces,cells_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨i,by simp,?_⟩
  cases s <;> simp [blockPieces,cells]

theorem tilePieces_location_exists {n m : ℕ} (rest : List ℕ) (role : RowRole) (c : Cell m) :
    ∃ p,(c,p)∈locatedCells cellBase (fun c : Cell m => cellBase c+1)
      (tilePieces n m rest role) := by
  have hm := tilePieces_cell_mem (n:=n) rest role c
  rw [← locatedCells_indices cellBase (fun c : Cell m => cellBase c+1)] at hm
  obtain ⟨⟨i,p⟩,hip,he⟩ := List.mem_map.mp hm
  change i=c at he
  subst i
  exact ⟨p,hip⟩

def cellEndpoint {h n m : ℕ} (q : ZMod h) (role : RowRole) (c : Cell m) : ZMod (h*n) :=
  endpoint (n:=n) (c.1,cellPhase q role c) c.2

/-- Each row contains exactly the literal two centers for every block,
with their actual, potentially different physical phases. -/
theorem tileWordFrame_movingRow {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (q : ZMod h) (role : RowRole) :
    (tileWordFrame T hn hsmall rest hbody (zeroSite h n q) role).movingRow originalSetting=
      (Finset.univ : Finset (Cell m)).image (cellEndpoint (n:=n) q role) := by
  classical
  rw [BinaryWordFrame.movingRow_locations]
  ext x
  constructor
  · intro hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨i,p⟩,hip,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,
      (tileWordFrame_center T hn hsmall hsize rest hbody q role i p hip).symm⟩
  · intro hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p,hip⟩ := tilePieces_location_exists (n:=n) rest role i
    apply Finset.mem_image.mpr
    refine ⟨p+cellBase i+(originalSetting i).toNat,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨(i,p),hip,rfl⟩),?_⟩
    exact tileWordFrame_center T hn hsmall hsize rest hbody q role i p hip

theorem cellEndpoint_injective {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (hsize : (5*m+8)^2≤n) (q : ZMod h) (role : RowRole) :
    Function.Injective (cellEndpoint (n:=n) (m:=m) q role) := by
  intro c d he
  have heq := endpoint_injective hsize (a₁:=((c.1,cellPhase q role c),c.2))
    (a₂:=((d.1,cellPhase q role d),d.2)) he
  apply Prod.ext
  · exact congrArg (fun z => z.1.1) heq
  · exact congrArg (fun z : Bit m h × Bool => z.2) heq

theorem tileWordFrame_movingRow_card {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 65≤n)
    (hsize : (5*m+8)^2≤n) (rest : List ℕ)
    (hbody : T.body=[7,1]++((List.range m).flatMap (Prefix.blockColors n)++rest))
    (q : ZMod h) (role : RowRole) :
    ((tileWordFrame T hn hsmall rest hbody (zeroSite h n q) role).movingRow originalSetting).card=2*m := by
  rw [tileWordFrame_movingRow T hn hsmall hsize rest hbody q role,
    Finset.card_image_of_injective _ (cellEndpoint_injective hsize q role)]
  simp [Fintype.card_prod,Nat.mul_comm]

end CorralFormalization.Results.SwitchFamily.Physical
