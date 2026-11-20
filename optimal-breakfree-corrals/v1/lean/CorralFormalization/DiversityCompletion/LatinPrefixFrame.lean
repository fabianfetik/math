import CorralFormalization.DiversityCompletion.GlobalTileCorral

namespace CorralFormalization.LatinCompletion.LatinPrefix

open LatinTransfer TerraceLift

inductive RowRole where
  | first | secondTwo | secondThree | third
  deriving DecidableEq

def before (n : ℕ) : RowRole → List ℕ
  | .first => [3,10,n-14,12]
  | .secondTwo => [10,n-14,12]
  | .secondThree => [10,n-14,12]
  | .third => [n-14,2,10]

def after (n : ℕ) : RowRole → List ℕ
  | .first => [2,n]
  | .secondTwo => [3,n,2]
  | .secondThree => [2,3,n]
  | .third => [3,n,12]

/-- q in the following construction is the phase of THIS terrace round,
not the tile top. The second rows have q=top-1, the third q=top-2. -/
def startOffset (n : ℕ) : RowRole → ℕ
  | .first => n-1
  | .secondTwo => n+2
  | .secondThree => n+2
  | .third => n+12

def roleWord {n : ℕ} (T : CompletedTerrace n) : RowRole → List ℕ
  | .first => TileGapWords.first n T.body
  | .secondTwo => TileGapWords.twoSecond n T.body
  | .secondThree => TileGapWords.threeSecond n T.body
  | .third => TileGapWords.threeThird n T.body

def canonicalSymbol {r : ℕ} [NeZero r] (i : Cell r) : ℕ :=
  ((cyclicLatinSquare r).entry i.1 i.2).val

/-- Explicit source-terrace prefix data, BEFORE any tile frame is built.
Only the original calendar body is decomposed into fixed edges and the
actual adjacent Latin gap pairs. The location field is the raw integer H2
predecessor formula; it does not assert connectorPrefixCenterSite or a full PhysicalFrame. -/
structure BodyInput {n : ℕ} (T : CompletedTerrace n) (r : ℕ) [NeZero r] where
  pieces : List (Piece (Cell r))
  fixed_positive : ∀ d, Piece.fixed d ∈ pieces → 0 < d
  cells_complete : (cells pieces).Perm (Finset.univ : Finset (Cell r)).toList
  calendar : T.body = word cellA cellB canonicalSymbol pieces
  position : ∀ i p, (i,p) ∈ locatedCells cellA cellB pieces →
    2*n+10+p = predecessor i.1 i.2+(2+2*r*i.1.val+2*i.2.val)*n

def fixedPieces {I : Type*} (ds : List ℕ) : List (Piece I) := ds.map Piece.fixed

theorem word_append {I : Type*} (A B c : I → ℕ) (ps ts : List (Piece I)) :
    word A B c (ps++ts) = word A B c ps ++ word A B c ts := by
  simp [word]

theorem word_fixedPieces {I : Type*} (A B c : I → ℕ) (ds : List ℕ) :
    word A B c (fixedPieces ds) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [fixedPieces,word] at ih ⊢
    simpa [Piece.gaps] using congrArg (List.cons d) ih

theorem cells_append {I : Type*} (ps ts : List (Piece I)) :
    cells (ps++ts) = cells ps ++ cells ts := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [cells,ih]

theorem cells_fixedPieces {I : Type*} (ds : List ℕ) : cells (fixedPieces (I := I) ds) = [] := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simpa [fixedPieces,cells] using ih

theorem weights_fixedPieces {I : Type*} (A B : I → ℕ) (ds : List ℕ) :
    (fixedPieces ds).map (Piece.weight A B) = ds := by
  simp [fixedPieces,List.map_map,Function.comp_def,Piece.weight]

theorem locatedCells_append {I : Type*} (A B : I → ℕ) (ps ts : List (Piece I)) :
    locatedCells A B (ps++ts) = locatedCells A B ps ++
      (locatedCells A B ts).map (fun p => (p.1,(ps.map (Piece.weight A B)).sum+p.2)) := by
  induction ps with
  | nil => simp [locatedCells]
  | cons p ps ih =>
    cases p <;> simp [locatedCells,ih,List.map_append,List.map_map,Function.comp_def,
      Piece.weight,Nat.add_assoc]

theorem locatedCells_fixedPieces {I : Type*} (A B : I → ℕ) (ds : List ℕ) :
    locatedCells A B (fixedPieces ds) = [] := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simpa [fixedPieces,locatedCells] using ih

def assembled {n r : ℕ} {T : CompletedTerrace n} [NeZero r]
    (P : BodyInput T r) (role : RowRole) : List (Piece (Cell r)) :=
  fixedPieces (before n role) ++ P.pieces ++ fixedPieces (after n role)

theorem assembled_word {n r : ℕ} {T : CompletedTerrace n} [NeZero r]
    (P : BodyInput T r) (role : RowRole) :
    word cellA cellB canonicalSymbol (assembled P role) = roleWord T role := by
  rw [assembled,word_append,word_append,word_fixedPieces,word_fixedPieces,← P.calendar]
  cases role <;> simp [before,after,roleWord,TileGapWords.first,TileGapWords.cycle,
    TileGapWords.middle,TileGapWords.twoSecond,TileGapWords.threeSecond,
    TileGapWords.threeThird,TileGapWords.thirdPrefix,List.append_assoc]

theorem assembled_cells {n r : ℕ} {T : CompletedTerrace n} [NeZero r]
    (P : BodyInput T r) (role : RowRole) :
    (cells (assembled P role)).Perm (Finset.univ : Finset (Cell r)).toList := by
  simpa only [assembled,cells_append,cells_fixedPieces,List.nil_append,List.append_nil]
    using P.cells_complete

theorem assembled_locations {n r : ℕ} {T : CompletedTerrace n} [NeZero r]
    (P : BodyInput T r) (role : RowRole) :
    locatedCells cellA cellB (assembled P role) =
      (locatedCells cellA cellB P.pieces).map (fun p => (p.1,(before n role).sum+p.2)) := by
  simp [assembled,locatedCells_append,locatedCells_fixedPieces,weights_fixedPieces]

theorem common_body_start {n : ℕ} (hn : 15 ≤ n) (role : RowRole) :
    startOffset n role+(before n role).sum = 2*n+10 := by
  cases role <;> simp [startOffset,before] <;> omega

theorem assembled_fixed_positive {n r : ℕ} {T : CompletedTerrace n} [NeZero r]
    (P : BodyInput T r) (hn : 15 ≤ n) (role : RowRole) (d : ℕ)
    (hd : Piece.fixed d ∈ assembled P role) : 0 < d := by
  have hmem : Piece.fixed d ∈ fixedPieces (I := Cell r) (before n role) ∨
      Piece.fixed d ∈ P.pieces ∨ Piece.fixed d ∈ fixedPieces (I := Cell r) (after n role) := by
    simpa [assembled,List.mem_append,or_assoc] using hd
  rcases hmem with hp | hp | hp
  · cases role <;> simp [fixedPieces,before] at hp <;> omega
  · exact P.fixed_positive d hp
  · cases role <;> simp [fixedPieces,after] at hp <;> omega

theorem roleWord_perm {n : ℕ} (T : CompletedTerrace n) (hn : 0 < n) (role : RowRole) :
    (roleWord T role).Perm (fullGapList n) := by
  have hf := TileGapWords.first_perm hn T.body T.differences
  cases role with
  | first => exact hf
  | secondTwo => exact (TileGapWords.twoSecond_perm_first n T.body).trans hf
  | secondThree => exact (TileGapWords.threeSecond_perm_first n T.body).trans hf
  | third => exact (TileGapWords.threeThird_perm_first n T.body).trans hf

theorem canonical_lt {r : ℕ} [NeZero r] (hr : 2 ≤ r) (i : Cell r) :
    canonicalSymbol i < cellB i := by
  have hv : canonicalSymbol i < r := ((cyclicLatinSquare r).entry i.1 i.2).isLt
  have hsq : r ≤ r*r := by nlinarith [Nat.mul_le_mul_left r (by omega : 1 ≤ r)]
  dsimp [cellB,outgoingBase]
  nlinarith

theorem assembled_winding {h n r : ℕ} [NeZero h] [NeZero r]
    {T : CompletedTerrace n} (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) (role : RowRole) :
    ((assembled P role).map (Piece.weight cellA cellB)).sum = h*n := by
  rw [← word_sum cellA cellB canonicalSymbol _ (fun i => (canonical_lt hr i).le),
    assembled_word P role,(roleWord_perm T (by nlinarith) role).sum_eq,fullGapList_sum,
    optimal_width (NeZero.pos h) hn]

theorem rowLift_connectorPrefixCenterSite {h n r : ℕ} [NeZero h] (q : ZMod h) (j u s : Fin r) :
    ((q.val*n+centerResidue u s+(2+2*r*j.val+2*u.val)*n : ℕ) : ZMod (h*n)) =
      connectorPrefixCenterSite h n r (q+phaseOffset h r j,u,s) := by
  simp only [connectorPrefixCenterSite,Nat.cast_add]
  change zeroSite h n q+(centerResidue u s : ZMod (h*n))+
      (((2+2*r*j.val+2*u.val)*n : ℕ) : ZMod (h*n)) =
    (centerResidue u s : ZMod (h*n))+
      zeroSite h n ((q+phaseOffset h r j)+((2+2*u.val : ℕ) : ZMod h))
  have hOff : zeroSite h n (phaseOffset h r j) = (((2*r)*j.val*n : ℕ) : ZMod (h*n)) :=
    zeroSite_natCast h n ((2*r)*j.val)
  have hC : zeroSite h n ((2+2*u.val : ℕ) : ZMod h) =
      (((2+2*u.val)*n : ℕ) : ZMod (h*n)) := zeroSite_natCast h n (2+2*u.val)
  rw [zeroSite_add,zeroSite_add,hOff,hC]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem assembled_connectorPrefixCenterSite {h n r : ℕ} [NeZero h] [NeZero r] {T : CompletedTerrace n}
    (P : BodyInput T r) (hr : 2 ≤ r) (hlarge : 100*r*r ≤ n) (hnsmall : 15 ≤ n)
    (q : ZMod h) (role : RowRole) (i : Cell r) (p : ℕ)
    (hp : (i,p) ∈ locatedCells cellA cellB (assembled P role)) (s : Fin r) :
    ((q.val*n+startOffset n role+(p+cellA i+s.val) : ℕ) : ZMod (h*n)) =
      connectorPrefixCenterSite h n r (q+phaseOffset h r i.1,i.2,s) := by
  rw [assembled_locations P role] at hp
  obtain ⟨⟨a,b⟩,hab,he⟩ := List.mem_map.mp hp
  have hai : a=i := congrArg Prod.fst he
  subst a
  have hbp : (before n role).sum+b=p := congrArg Prod.snd he
  have hstart := common_body_start hnsmall role
  have hH2 := P.position i b hab
  rcases local_gap_geometry hr hlarge i.1 i.2 s with ⟨hlt,_,hdiff,_,_,_,_,_⟩
  have hPA : predecessor i.1 i.2+cellA i = centerBase i.2 := by
    have he := Nat.sub_add_cancel hlt.le
    rw [hdiff] at he
    change predecessor i.1 i.2+incomingBase i.1 = centerBase i.2
    omega
  have hcoord : q.val*n+startOffset n role+(p+cellA i+s.val) =
      q.val*n+centerResidue i.2 s+(2+2*r*i.1.val+2*i.2.val)*n := by
    dsimp [centerResidue,centerBase] at hPA ⊢
    omega
  rw [hcoord]
  exact rowLift_connectorPrefixCenterSite q i.1 i.2 s

/-- Constructed physical frame from source-body H2 data, for any specified
row-role function. No completed physical frame or connectorPrefixCenterSite equation is assumed. -/
def physicalFrame {h n r : ℕ} [NeZero h] [NeZero r] {T : CompletedTerrace n}
    (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1) (hlarge : 100*r*r ≤ n)
    (roles : ZMod h → RowRole) : PhysicalFrame h n r where
  pieces q := assembled P (roles q)
  origin q := q.val*n+startOffset n (roles q)
  fixed_positive q := assembled_fixed_positive P (by nlinarith) (roles q)
  cells_complete q := assembled_cells P (roles q)
  winding q := assembled_winding P hr hn hlarge (roles q)
  location q i p hp s := assembled_connectorPrefixCenterSite P hr hlarge (by nlinarith) q (roles q) i p hp s

end CorralFormalization.LatinCompletion.LatinPrefix
