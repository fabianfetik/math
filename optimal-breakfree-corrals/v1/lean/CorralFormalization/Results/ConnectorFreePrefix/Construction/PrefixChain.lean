import CorralFormalization.Results.ConnectorFreePrefix.WaleckiCoordinates
import CorralFormalization.Results.ConnectorFreePrefix.Construction.DirectJoinColors
import CorralFormalization.DiversityCompletion.LatinConnectorPathGaps

/-!
# The literal connector-free prefix and its positive lift

The eight markers and every actual P/C/N triple are explicitly present.
There is one direct edge and no inserted vertex between consecutive cells.
The location theorem is the integer formula (L14), derived from the actual
one-wrap edge sum. No rainbow prefix or completed terrace is an input.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply

variable {r : ℕ} [NeZero r]

abbrev prefixA (i : Cell r) : ℕ := (waleckiCoordinates r).a i.1
abbrev prefixB (i : Cell r) : ℕ := (waleckiCoordinates r).b i.1
abbrev prefixPredecessor (i : Cell r) : ℕ := (waleckiCoordinates r).predecessor i.1 i.2
abbrev prefixCenter (i : Cell r) : ℕ := (waleckiCoordinates r).xi i.2+canonicalSymbol i
abbrev prefixSuccessor (i : Cell r) : ℕ := (waleckiCoordinates r).successor i.1 i.2

/-- The actual positive representative of a direct N-to-P join. -/
def directGap (n : ℕ) (i k : Cell r) : ℕ := n+prefixPredecessor k-prefixSuccessor i

theorem prefix_vertex_bands (hr : 3 ≤ r) (i : Cell r) :
    7*r*r+1 ≤ prefixPredecessor i ∧ prefixPredecessor i ≤ 12*r*r ∧
    18*r*r ≤ prefixCenter i ∧ prefixCenter i ≤ 23*r*r ∧
    68*r*r ≤ prefixSuccessor i ∧ prefixSuccessor i ≤ 73*r*r := by
  have hxi := (waleckiCoordinates r).xi_bounds hr i.2
  have hp := row_product_bound hr i.1.isLt
  have hs := ((cyclicLatinSquare r).entry i.1 i.2).isLt
  have hpos : 0 < r*r := Nat.mul_pos (by omega) (by omega)
  have hcancel : r*r-1+1=r*r := by omega
  have ha : (waleckiCoordinates r).a i.1 ≤ (waleckiCoordinates r).xi i.2 := by
    dsimp [ConnectorFreePhysical.Coordinates.a]
    change 10*r*r+modulus r*i.1.val ≤ _
    nlinarith
  have hP := Nat.sub_add_cancel ha
  dsimp [ConnectorFreePhysical.Coordinates.a] at hP
  change (waleckiCoordinates r).xi i.2-(10*r*r+modulus r*i.1.val)+
      (10*r*r+modulus r*i.1.val)=(waleckiCoordinates r).xi i.2 at hP
  dsimp [prefixPredecessor, prefixCenter, prefixSuccessor,
    ConnectorFreePhysical.Coordinates.predecessor, ConnectorFreePhysical.Coordinates.successor,
    ConnectorFreePhysical.Coordinates.a, ConnectorFreePhysical.Coordinates.b, canonicalSymbol]
  change 7*r*r+1 ≤ (waleckiCoordinates r).xi i.2-(10*r*r+modulus r*i.1.val) ∧ _
  constructor
  · nlinarith
  constructor
  · nlinarith [Nat.sub_le ((waleckiCoordinates r).xi i.2) (10*r*r+modulus r*i.1.val)]
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem prefix_cell_displacement (hr : 3 ≤ r) (i : Cell r) :
    prefixPredecessor i+(prefixA i+prefixB i)=prefixSuccessor i := by
  have hxi := (waleckiCoordinates r).xi_bounds hr i.2
  have hp := (row_product_bound hr i.1.isLt).trans (Nat.sub_le (r*r) 1)
  have ha : (waleckiCoordinates r).a i.1 ≤ (waleckiCoordinates r).xi i.2 := by
    dsimp [ConnectorFreePhysical.Coordinates.a]
    change 10*r*r+modulus r*i.1.val ≤ _
    nlinarith
  have hc := Nat.sub_add_cancel ha
  dsimp [prefixPredecessor,prefixSuccessor,prefixA,prefixB,
    ConnectorFreePhysical.Coordinates.predecessor,ConnectorFreePhysical.Coordinates.successor]
  omega

theorem directGap_geometry {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (i k : Cell r) :
    0 < directGap n i k ∧ directGap n i k < n ∧
    prefixSuccessor i+directGap n i k=prefixPredecessor k+n := by
  have hi := prefix_vertex_bands hr i
  have hk := prefix_vertex_bands hr k
  have hpos : 0 < r*r := Nat.mul_pos (by omega) (by omega)
  unfold directGap
  simp only [Nat.mul_assoc] at hi hk hn ⊢
  omega

/-- Piece chain for actual triples and one direct join between them. -/
def directChain (n : ℕ) (first : Cell r) : List (Cell r) → List (Piece (Cell r))
  | [] => [Piece.cell first]
  | next::rest => Piece.cell first::Piece.fixed (directGap n first next)::directChain n next rest

/-- Literal tail after the predecessor of a connector-free triple. -/
def directTailVertices (first : Cell r) : List (Cell r) → List ℕ
  | [] => [prefixCenter first,prefixSuccessor first]
  | next::rest => prefixCenter first::prefixSuccessor first::prefixPredecessor next::directTailVertices next rest

/-- Literal ordinary P/C/N list, with no connector vertices. -/
def directVertices (first : Cell r) (rest : List (Cell r)) : List ℕ :=
  prefixPredecessor first::directTailVertices first rest

def prefixVertices (n r : ℕ) [NeZero r] : List ℕ :=
  [n-3,n-1,2,12,n-2,10,17,18] ++ directVertices (firstCell r) (lexCells r).tail

def prefixPath (n r : ℕ) [NeZero r] : List (ZMod n) :=
  (prefixVertices n r).map (fun x : ℕ => (x : ZMod n))

def prefixGaps (n r : ℕ) [NeZero r] : List ℕ :=
  [7,1,10*r*r-18] ++ word prefixA prefixB canonicalSymbol
    (directChain n (firstCell r) (lexCells r).tail)

def prefixPieces (n r : ℕ) [NeZero r] (suffix : List ℕ) : List (Piece (Cell r)) :=
  fixedPieces [7,1,10*r*r-18] ++
    directChain n (firstCell r) (lexCells r).tail ++ fixedPieces suffix

theorem directVertices_length (first : Cell r) (rest : List (Cell r)) :
    (directVertices first rest).length=3*rest.length+3 := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    change (directVertices next rest).length+3=3*(next::rest).length+3
    rw [ih]
    simp only [List.length_cons]
    omega

theorem prefixVertices_length (n r : ℕ) [NeZero r] :
    (prefixVertices n r).length=3*r*r+8 := by
  have hpos : 0 < r*r := Nat.mul_pos (NeZero.pos r) (NeZero.pos r)
  simp only [prefixVertices,List.length_append,List.length_cons,List.length_nil,
    directVertices_length,List.length_tail,lexCells_length,Nat.mul_assoc]
  omega

theorem prefixPath_length (n r : ℕ) [NeZero r] :
    (prefixPath n r).length=3*r*r+8 := by
  simp only [prefixPath,List.length_map,prefixVertices_length]

theorem directChain_cells (n : ℕ) (first : Cell r) (rest : List (Cell r)) :
    cells (directChain n first rest)=first::rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih => simpa [directChain,cells] using congrArg (List.cons first) (ih next)

theorem prefixPieces_cells (n r : ℕ) [NeZero r] (suffix : List ℕ) :
    (cells (prefixPieces n r suffix)).Perm (Finset.univ : Finset (Cell r)).toList := by
  simpa only [prefixPieces,cells_append,cells_fixedPieces,List.nil_append,List.append_nil,
    directChain_cells,←lexCells_cons] using lexCells_perm r

theorem prefixPieces_word (n r : ℕ) [NeZero r] (suffix : List ℕ) :
    word prefixA prefixB canonicalSymbol (prefixPieces n r suffix)=prefixGaps n r++suffix := by
  simp only [prefixPieces,word_append,word_fixedPieces,prefixGaps,List.append_assoc]

theorem first_predecessor (r : ℕ) [NeZero r] :
    prefixPredecessor (firstCell r)=10*r*r := by
  have hxi : (waleckiCoordinates r).xi (0:Fin r)=20*r*r := by
    dsimp [ConnectorFreePhysical.Coordinates.xi]
    omega
  dsimp [prefixPredecessor,ConnectorFreePhysical.Coordinates.predecessor,firstCell]
  rw [hxi]
  simp only [ConnectorFreePhysical.Coordinates.a,Fin.val_zero,Nat.mul_zero,Nat.add_zero,Nat.mul_assoc]
  omega

/-- All cell edges are their actual positive directed colour values (L9). -/
theorem cell_edge_values {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n) (i : Cell r) :
    ((prefixCenter i:ZMod n)-(prefixPredecessor i:ZMod n)).val=prefixA i+canonicalSymbol i ∧
    ((prefixSuccessor i:ZMod n)-(prefixCenter i:ZMod n)).val=prefixB i-canonicalSymbol i := by
  obtain ⟨hPC,hCN,hPA,hA,hB,_,hAn,_,hBn⟩ :=
    (waleckiCoordinates r).local_gap_geometry hr hn i.1 i.2 ((cyclicLatinSquare r).entry i.1 i.2)
  constructor
  · exact edgeGap_of_nat_sum n _ _ _ hAn (Or.inl (by dsimp [prefixPredecessor,prefixCenter,prefixA,canonicalSymbol]; omega))
  · exact edgeGap_of_nat_sum n _ _ _ hBn (Or.inl (by dsimp [prefixSuccessor,prefixCenter,prefixB,canonicalSymbol]; omega))

theorem direct_edge_value {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n) (i k : Cell r) :
    ((prefixPredecessor k:ZMod n)-(prefixSuccessor i:ZMod n)).val=directGap n i k := by
  obtain ⟨_,hd,hs⟩ := directGap_geometry hr hn i k
  exact edgeGap_of_nat_sum n _ _ _ hd (Or.inr (by omega))

/-- The actual directed gaps of the concrete triple chain are its piece word. -/
theorem directVertices_pathGaps {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (first : Cell r) (rest : List (Cell r)) :
    pathGaps ((directVertices first rest).map (fun x : ℕ => (x : ZMod n)))=
      word prefixA prefixB canonicalSymbol (directChain n first rest) := by
  induction rest generalizing first with
  | nil =>
    obtain ⟨hA,hB⟩ := cell_edge_values hr hn first
    change [((prefixCenter first:ZMod n)-(prefixPredecessor first:ZMod n)).val,
      ((prefixSuccessor first:ZMod n)-(prefixCenter first:ZMod n)).val]=_
    rw [hA,hB]
    rfl
  | cons next rest ih =>
    obtain ⟨hA,hB⟩ := cell_edge_values hr hn first
    have hJ := direct_edge_value hr hn first next
    change ((prefixCenter first:ZMod n)-(prefixPredecessor first:ZMod n)).val::
      ((prefixSuccessor first:ZMod n)-(prefixCenter first:ZMod n)).val::
      ((prefixPredecessor next:ZMod n)-(prefixSuccessor first:ZMod n)).val::
      pathGaps ((directVertices next rest).map (fun x : ℕ => (x : ZMod n)))=_
    rw [hA,hB,hJ,ih next]
    rfl

/-- Exact physical gap list of the literal eight-marker prefix. -/
theorem prefixPath_pathGaps {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n) :
    pathGaps (prefixPath n r)=[2,3,10,n-14,12]++prefixGaps n r := by
  have hfirst := first_predecessor r
  have hbands := prefix_vertex_bands hr (firstCell r)
  have hr2 : 9 ≤ r*r := by nlinarith
  have hinit := initial_pathGaps n (prefixPredecessor (firstCell r))
    (by nlinarith) (by nlinarith) (by nlinarith)
  have hchain := directVertices_pathGaps hr hn (firstCell r) (lexCells r).tail
  change pathGaps ([n-3,n-1,2,12,n-2,10,17,18].map (fun x : ℕ => (x : ZMod n)) ++
    (prefixPredecessor (firstCell r):ZMod n)::
    ((directTailVertices (firstCell r) (lexCells r).tail).map (fun x : ℕ => (x : ZMod n))))=_
  rw [pathGaps_append_pivot]
  change pathGaps ([n-3,n-1,2,12,n-2,10,17,18,prefixPredecessor (firstCell r)].map
    (fun x : ℕ => (x : ZMod n)))++
    pathGaps ((directVertices (firstCell r) (lexCells r).tail).map (fun x : ℕ => (x : ZMod n)))=_
  rw [hinit,hchain]
  simp only [prefixGaps,hfirst,List.append_assoc]
  rfl

/-- The actual single-wrap join sum proves the one-level increase. -/
theorem directChain_location {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (first : Cell r) (rest : List (Cell r)) (i : Cell r) (p : ℕ)
    (hp : (i,p) ∈ locatedCells prefixA prefixB (directChain n first rest)) :
    ∃ t : Fin (first::rest).length,
      (first::rest)[t.val]=i ∧ prefixPredecessor first+p=prefixPredecessor i+t.val*n := by
  induction rest generalizing first i p with
  | nil =>
    have he : (i,p)=(first,0) := by simpa [directChain,locatedCells] using hp
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨⟨0,by simp⟩,rfl,by simp⟩
  | cons next rest ih =>
    simp only [directChain,locatedCells,List.map_map,Function.comp_def,List.mem_cons,List.mem_map] at hp
    rcases hp with he | ⟨⟨j,q⟩,hq,he⟩
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact ⟨⟨0,by simp⟩,rfl,by simp⟩
    · have hji : j=i := congrArg Prod.fst he
      have hqp := congrArg Prod.snd he
      dsimp at hji hqp
      subst j
      obtain ⟨t,hti,ht⟩ := ih next i q hq
      have hc := prefix_cell_displacement hr first
      have hj := (directGap_geometry hr hn first next).2.2
      refine ⟨⟨t.val+1,by simpa only [List.length_cons] using Nat.succ_lt_succ t.isLt⟩,?_,?_⟩
      · simpa using hti
      · rw [←hqp]
        calc
          prefixPredecessor first+(prefixA first+prefixB first+(directGap n first next+q)) =
              prefixPredecessor next+n+q := by omega
          _ = prefixPredecessor i+t.val*n+n := by omega
          _ = prefixPredecessor i+(t.val+1)*n := by ring

/-- The concrete positive lift (L14), in the exact form used by the physical
body frame. It is derived before choosing any endpoint completion. -/
theorem prefixPieces_position {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (suffix : List ℕ) (i : Cell r) (p : ℕ)
    (hp : (i,p) ∈ locatedCells prefixA prefixB (prefixPieces n r suffix)) :
    2*n+10+p=prefixPredecessor i+(2+r*i.1.val+i.2.val)*n := by
  simp only [prefixPieces,locatedCells_append,locatedCells_fixedPieces,List.nil_append,
    List.map_nil,List.append_nil,weights_fixedPieces,List.sum_cons,List.sum_nil,Nat.add_zero] at hp
  obtain ⟨⟨j,q⟩,hq,he⟩ := List.mem_map.mp hp
  have hji : j=i := congrArg Prod.fst he
  have hqp := congrArg Prod.snd he
  dsimp at hji hqp
  subst j
  obtain ⟨t,hti,ht⟩ := directChain_location hr hn (firstCell r) (lexCells r).tail i q hq
  have htbound : t.val < (lexCells r).length := by
    exact t.isLt.trans_eq (congrArg List.length (lexCells_cons r).symm)
  have hti' : (lexCells r)[t.val]=i := by simpa only [(lexCells_cons r).symm] using hti
  have hrank : t.val=i.2.val+r*i.1.val := by
    have hh := lexCells_rank r t.val htbound
    rw [hti'] at hh
    exact hh.symm
  have hfirst := first_predecessor r
  have hlarge : 18 < 10*r*r := by nlinarith
  calc
    2*n+10+p=prefixPredecessor (firstCell r)+q+2*n := by omega
    _ = (prefixPredecessor i+t.val*n)+2*n := by rw [ht]
    _ = prefixPredecessor i+(2+r*i.1.val+i.2.val)*n := by rw [hrank]; ring

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction
