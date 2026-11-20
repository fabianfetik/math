import CorralFormalization.DiversityCompletion.LatinConnectorPathGaps

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply

open LatinTransfer TerraceLift LatinPrefix TerraceCompletion

theorem connectorCellVertices_length {r : ℕ} [NeZero r]
    (y : Cell r → ℕ) (first : Cell r) (rest : List (Cell r)) :
    (connectorCellVertices y first rest).length = 4*rest.length+3 := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    rw [connectorCellVertices_cons]
    simp only [List.length_cons,ih]
    omega

theorem connectorPrefixVertices_length {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) :
    (connectorPrefixVertices n y).length = 4*r*r+7 := by
  have hR : 0 < r*r := Nat.mul_pos (NeZero.pos r) (NeZero.pos r)
  simp only [connectorPrefixVertices,List.length_append,List.length_cons,List.length_nil,
    connectorCellVertices_length,List.length_tail,lexCells_length]
  simp only [Nat.mul_assoc]
  omega

theorem connectorPrefixPath_length {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) :
    (connectorPrefixPath n y).length = 4*r*r+7 := by
  rw [connectorPrefixPath,List.length_map,connectorPrefixVertices_length]

theorem connectorPrefixVertices_head {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) :
    (connectorPrefixVertices n y).head? = some (n-3) := rfl

theorem connectorPrefixPath_head {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) :
    (connectorPrefixPath n y).head? = some ((n-3 : ℕ) : ZMod n) := rfl

def lastCell (r : ℕ) [NeZero r] : Cell r :=
  (⟨r-1,by have := NeZero.pos r; omega⟩, ⟨r-1,by have := NeZero.pos r; omega⟩)

theorem lastCell_rank (r : ℕ) [NeZero r] :
    (finProdFinEquiv (lastCell r)).val = r*r-1 := by
  have hr := NeZero.pos r
  have hsub : r-1+1=r := Nat.sub_add_cancel hr
  have hR : 0 < r*r := Nat.mul_pos hr hr
  have hRsub : r*r-1+1=r*r := Nat.sub_add_cancel hR
  dsimp [lastCell,finProdFinEquiv]
  nlinarith

theorem lexCells_getLast (r : ℕ) [NeZero r] :
    (lexCells r).getLast? = some (lastCell r) := by
  have hR : 0 < r*r := Nat.mul_pos (NeZero.pos r) (NeZero.pos r)
  have hnon : lexCells r ≠ [] := by
    intro h
    have hh := lexCells_length r
    rw [h] at hh
    simp only [List.length_nil] at hh
    omega
  rw [List.getLast?_eq_some_getLast hnon]
  apply congrArg some
  apply finProdFinEquiv.injective
  apply Fin.ext
  rw [List.getLast_eq_getElem]
  have ht : (lexCells r).length-1 < (lexCells r).length := by rw [lexCells_length]; omega
  rw [lexCells_rank r _ ht,lastCell_rank,lexCells_length]

theorem connectorCellVertices_getLast {r : ℕ} [NeZero r]
    (y : Cell r → ℕ) (first : Cell r) (rest : List (Cell r)) :
    (connectorCellVertices y first rest).getLast? =
      ((first::rest).getLast?).map (fun i => successor i.1 i.2) := by
  induction rest generalizing first with
  | nil => simp [connectorCellVertices_nil]
  | cons next rest ih =>
    rw [connectorCellVertices_cons]
    simp only [List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil (xs := connectorCellVertices y next rest) (by simp [connectorCellVertices])]
    exact ih next

def connectorPrefixLastValue (r : ℕ) [NeZero r] : ℕ := successor (lastCell r).1 (lastCell r).2

theorem connectorPrefixLastValue_formula (r : ℕ) [NeZero r] : connectorPrefixLastValue r = 72*r*r-r-1 := by
  have hr := NeZero.pos r
  have hsub : r-1+1=r := Nat.sub_add_cancel hr
  have hs : connectorPrefixLastValue r+r+1=72*r*r := by
    dsimp [connectorPrefixLastValue,lastCell,successor,centerBase,outgoingBase]
    nlinarith
  omega

theorem connectorPrefixVertices_getLast {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) :
    (connectorPrefixVertices n y).getLast? = some (connectorPrefixLastValue r) := by
  rw [connectorPrefixVertices,List.getLast?_append,connectorCellVertices_getLast,← lexCells_cons,lexCells_getLast]
  rfl

theorem connectorPrefixPath_getLast {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) :
    (connectorPrefixPath n y).getLast? = some ((connectorPrefixLastValue r : ℕ) : ZMod n) := by
  rw [connectorPrefixPath,List.getLast?_map,connectorPrefixVertices_getLast]
  rfl

/-- A robust endpoint/interior decomposition for direct RainbowPrefix or
EndpointSplice assembly. It needs no path validity, band or size regime. -/
theorem connectorPrefixPath_decomposition {r : ℕ} [NeZero r] (n : ℕ) (y : Cell r → ℕ) :
    ∃ interior : List (ZMod n),
      connectorPrefixPath n y = (((n-3 : ℕ) : ZMod n)::interior) ++ [((connectorPrefixLastValue r : ℕ) : ZMod n)] ∧
      interior.length = 4*r*r+5 := by
  obtain ⟨initialPart,hpart⟩ := List.getLast?_eq_some_iff.mp (connectorPrefixPath_getLast n y)
  have hlen := connectorPrefixPath_length n y
  cases initialPart with
  | nil =>
    rw [hpart] at hlen
    simp only [List.nil_append,List.length_cons,List.length_nil] at hlen
    omega
  | cons first interior =>
    have hh := connectorPrefixPath_head n y
    rw [hpart] at hh
    have hfirst : first=((n-3 : ℕ) : ZMod n) := by simpa using hh
    rw [hfirst] at hpart
    refine ⟨interior,hpart,?_⟩
    rw [hpart] at hlen
    simp only [List.length_append,List.length_cons,List.length_nil] at hlen
    omega

end CorralFormalization.LatinCompletion.LatinPrefixSupply
