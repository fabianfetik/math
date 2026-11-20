import CorralFormalization.DiversityCompletion.EndpointSplice

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply

open LatinTransfer TerraceLift LatinPrefix TerraceCompletion

/-- The literal part of the connector-prefix vertex chain following a cell predecessor. -/
def connectorCellTailVertices {r : ℕ} [NeZero r] (y : Cell r → ℕ) (first : Cell r) :
    List (Cell r) → List ℕ
  | [] => [centerBase first.2+canonicalSymbol first,successor first.1 first.2]
  | next :: rest => (centerBase first.2+canonicalSymbol first) :: successor first.1 first.2 ::
      y first :: predecessor next.1 next.2 :: connectorCellTailVertices y next rest

/-- Actual P/C/N triples, joined by the chosen connector value. -/
def connectorCellVertices {r : ℕ} [NeZero r] (y : Cell r → ℕ) (first : Cell r)
    (rest : List (Cell r)) : List ℕ :=
  predecessor first.1 first.2 :: connectorCellTailVertices y first rest

theorem connectorCellVertices_nil {r : ℕ} [NeZero r] (y : Cell r → ℕ) (first : Cell r) :
    connectorCellVertices y first [] =
      [predecessor first.1 first.2,centerBase first.2+canonicalSymbol first,
       successor first.1 first.2] := rfl

theorem connectorCellVertices_cons {r : ℕ} [NeZero r] (y : Cell r → ℕ)
    (first next : Cell r) (rest : List (Cell r)) :
    connectorCellVertices y first (next::rest) =
      predecessor first.1 first.2 :: (centerBase first.2+canonicalSymbol first) ::
        successor first.1 first.2 :: y first :: connectorCellVertices y next rest := rfl

def connectorPrefixVertices {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) : List ℕ :=
  [n-3,n-1,2,12,n-2,10,17,18] ++ connectorCellVertices y (firstCell r) (lexCells r).tail

def connectorPrefixPath {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) : List (ZMod n) :=
  (connectorPrefixVertices n y).map (fun x : ℕ => (x : ZMod n))

theorem edgeGap_of_step {n : ℕ} (a b : ZMod n) (d : ℕ)
    (hd : d < n) (hs : a+(d : ZMod n)=b) : (b-a).val=d := by
  have he : b-a=(d : ZMod n) := by rw [← hs]; ring
  rw [he,ZMod.val_natCast_of_lt hd]

theorem edgeGap_of_nat_sum (n a b d : ℕ) (hd : d < n)
    (hs : a+d=b ∨ a+d=n+b) :
    ((b : ZMod n)-(a : ZMod n)).val=d := by
  apply edgeGap_of_step _ _ d hd
  rcases hs with hs | hs
  · simpa only [Nat.cast_add] using congrArg (fun x : ℕ => (x : ZMod n)) hs
  · simpa only [Nat.cast_add,ZMod.natCast_self,zero_add] using
      congrArg (fun x : ℕ => (x : ZMod n)) hs

/-- The actual directed gaps of a concrete connector-prefix triple are its literal
incoming/outgoing calendar entries. No whole-path validity is assumed. -/
theorem connectorPrefix_cell_edge_values {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (i : Cell r) :
    (((centerBase i.2+canonicalSymbol i : ℕ) : ZMod n)-
      (predecessor i.1 i.2 : ZMod n)).val = cellA i+canonicalSymbol i ∧
    ((successor i.1 i.2 : ZMod n)-
      ((centerBase i.2+canonicalSymbol i : ℕ) : ZMod n)).val = cellB i-canonicalSymbol i := by
  obtain ⟨hPC,hCN,hA,hB,_,hAn,_,hBn⟩ :=
    local_gap_geometry hr hn i.1 i.2 ((cyclicLatinSquare r).entry i.1 i.2)
  dsimp [canonicalSymbol,cellA,cellB]
  constructor
  · rw [← Nat.cast_sub hPC.le,ZMod.val_natCast_of_lt (by rw [hA]; exact hAn),hA]
  · rw [← Nat.cast_sub hCN.le,ZMod.val_natCast_of_lt (by rw [hB]; exact hBn),hB]

theorem connectorPrefix_connector_edge_values {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (y : Cell r → ℕ)
    (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r) (previous next : Cell r) :
    ((y previous : ZMod n)-(successor previous.1 previous.2 : ZMod n)).val =
      wrapOut n (y previous) (successor previous.1 previous.2) ∧
    ((predecessor next.1 next.2 : ZMod n)-(y previous : ZMod n)).val =
      wrapIn n (y previous) (predecessor next.1 next.2) := by
  obtain ⟨hP,hyN,hN⟩ := connectorPrefix_connector_order hr hn y hy previous next
  obtain ⟨_,ho,_,hi,_,hsOut,hsIn⟩ :=
    two_wrap_geometry n (predecessor next.1 next.2) (successor previous.1 previous.2)
      (y previous) hP hyN hN
  exact ⟨edgeGap_of_step _ _ _ ho hsOut,edgeGap_of_step _ _ _ hi hsIn⟩

theorem initial_pathGaps (n P : ℕ) (hn : 19 ≤ n) (hP : 18 < P) (hPn : P < n) :
    pathGaps ([n-3,n-1,2,12,n-2,10,17,18,P].map (fun x : ℕ => (x : ZMod n))) =
      [2,3,10,n-14,12,7,1,P-18] := by
  have h1 := edgeGap_of_nat_sum n (n-3) (n-1) 2 (by omega) (Or.inl (by omega))
  have h2 := edgeGap_of_nat_sum n (n-1) 2 3 (by omega) (Or.inr (by omega))
  have h3 := edgeGap_of_nat_sum n 2 12 10 (by omega) (Or.inl (by omega))
  have h4 := edgeGap_of_nat_sum n 12 (n-2) (n-14) (by omega) (Or.inl (by omega))
  have h5 := edgeGap_of_nat_sum n (n-2) 10 12 (by omega) (Or.inr (by omega))
  have h6 := edgeGap_of_nat_sum n 10 17 7 (by omega) (Or.inl (by omega))
  have h7 := edgeGap_of_nat_sum n 17 18 1 (by omega) (Or.inl (by omega))
  have h8 := edgeGap_of_nat_sum n 18 P (P-18) (by omega) (Or.inl (by omega))
  simp only [List.map_cons,List.map_nil,pathGaps,h1,h2,h3,h4,h5,h6,h7,h8]

/-- The actual cell/connector vertex chain has exactly the previously
defined piece-word gaps. This remains true without simplicity or rainbow. -/
theorem connectorCellVertices_pathGaps {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (y : Cell r → ℕ)
    (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r) (first : Cell r) (rest : List (Cell r)) :
    pathGaps ((connectorCellVertices y first rest).map (fun x : ℕ => (x : ZMod n))) =
      word cellA cellB canonicalSymbol
        (cellChain n (fun i : Cell r => predecessor i.1 i.2)
          (fun i => successor i.1 i.2) y first rest) := by
  induction rest generalizing first with
  | nil =>
    obtain ⟨hA,hB⟩ := connectorPrefix_cell_edge_values hr hn first
    change [(((centerBase first.2+canonicalSymbol first : ℕ) : ZMod n)-
          (predecessor first.1 first.2 : ZMod n)).val,
        ((successor first.1 first.2 : ZMod n)-
          ((centerBase first.2+canonicalSymbol first : ℕ) : ZMod n)).val] =
      [cellA first+canonicalSymbol first,cellB first-canonicalSymbol first]
    rw [hA,hB]
  | cons next rest ih =>
    obtain ⟨hA,hB⟩ := connectorPrefix_cell_edge_values hr hn first
    obtain ⟨hO,hI⟩ := connectorPrefix_connector_edge_values hr hn y hy first next
    change [(((centerBase first.2+canonicalSymbol first : ℕ) : ZMod n)-
          (predecessor first.1 first.2 : ZMod n)).val,
        ((successor first.1 first.2 : ZMod n)-
          ((centerBase first.2+canonicalSymbol first : ℕ) : ZMod n)).val,
        ((y first : ZMod n)-(successor first.1 first.2 : ZMod n)).val,
        ((predecessor next.1 next.2 : ZMod n)-(y first : ZMod n)).val] ++
        pathGaps ((connectorCellVertices y next rest).map (fun x : ℕ => (x : ZMod n))) = _
    rw [hA,hB,hO,hI,ih next]
    rfl

/-- Exact genuine directed gap list of the connector-prefix vertex prefix.
The only inputs are the numerical regime and the individual connector
band values. Prefix simplicity and rainbow are not assumed or asserted. -/
theorem connectorPrefixPath_pathGaps {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (y : Cell r → ℕ)
    (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r) :
    pathGaps (connectorPrefixPath n y) = [2,3,10,n-14,12] ++ connectorPrefixGaps n y := by
  have hn19 : 19 ≤ n := by nlinarith
  have hP := connectorPrefix_predecessor_large hr (firstCell r)
  obtain ⟨hPy,hyN,hN⟩ := connectorPrefix_connector_order hr hn y hy (firstCell r) (firstCell r)
  have hPn : predecessor (firstCell r).1 (firstCell r).2 < n := by omega
  have hinit := initial_pathGaps n (predecessor (firstCell r).1 (firstCell r).2) hn19 hP hPn
  have hchain := connectorCellVertices_pathGaps hr hn y hy (firstCell r) (lexCells r).tail
  change pathGaps ([n-3,n-1,2,12,n-2,10,17,18].map (fun x : ℕ => (x : ZMod n)) ++
    (predecessor (firstCell r).1 (firstCell r).2 : ZMod n) ::
      (connectorCellTailVertices y (firstCell r) (lexCells r).tail).map (fun x : ℕ => (x : ZMod n))) = _
  rw [pathGaps_append_pivot]
  change pathGaps ([n-3,n-1,2,12,n-2,10,17,18,
      predecessor (firstCell r).1 (firstCell r).2].map (fun x : ℕ => (x : ZMod n))) ++
    pathGaps ((connectorCellVertices y (firstCell r) (lexCells r).tail).map (fun x : ℕ => (x : ZMod n))) = _
  rw [hinit,hchain]
  rfl

end CorralFormalization.LatinCompletion.LatinPrefixSupply
