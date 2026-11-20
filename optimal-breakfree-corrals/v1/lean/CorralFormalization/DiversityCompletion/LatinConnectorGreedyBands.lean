import CorralFormalization.DiversityCompletion.LatinConnectorGreedy

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.ConnectorGreedy

open Finset LatinTransfer TerraceLift LatinPrefix

def candidateBand (r : ℕ) : Finset ℕ := Ico (30*r*r) (40*r*r)

def prescribedVertices (n r : ℕ) [NeZero r] : Finset ℕ :=
  {n-3,n-1,2,12,n-2,10,17,18} ∪
    univ.biUnion (fun i : Cell r =>
      {predecessor i.1 i.2,centerBase i.2+canonicalSymbol i,successor i.1 i.2})

def prescribedColors (n r : ℕ) [NeZero r] : Finset ℕ :=
  {2,3,10,n-14,12,7,1,predecessor (firstCell r).1 (firstCell r).2-18} ∪
    univ.biUnion (fun i : Cell r => {cellA i+canonicalSymbol i,cellB i-canonicalSymbol i})

theorem connectorPrefix_value_bounds {r : ℕ} [NeZero r] (hr : 2 ≤ r) (i : Cell r) :
    predecessor i.1 i.2 < 22*r*r ∧
    centerBase i.2+canonicalSymbol i < 24*r*r ∧
    60*r*r < successor i.1 i.2 ∧ successor i.1 i.2 < 73*r*r ∧
    cellA i+canonicalSymbol i ≤ 52*r*r ∧ cellB i-canonicalSymbol i ≤ 52*r*r := by
  have hsq : r ≤ r*r := by nlinarith
  have hri := i.1.isLt
  have hru := i.2.isLt
  have hs : canonicalSymbol i < r := ((cyclicLatinSquare r).entry i.1 i.2).isLt
  have hmi := Nat.mul_lt_mul_of_pos_left hri (by omega : 0 < r)
  have hmu := Nat.mul_lt_mul_of_pos_left hru (by omega : 0 < r+1)
  have hp := Nat.sub_le (centerBase i.2) (incomingBase i.1)
  have hb := Nat.sub_le (outgoingBase i.1) (canonicalSymbol i)
  dsimp [predecessor,successor,cellA,cellB,centerBase,incomingBase,outgoingBase] at *
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

/-- All prescribed connector-prefix vertices, including the eight initial vertices, are
outside the candidate band. No vertex-disjointness premise is needed. -/
theorem band_avoids_prescribedVertices {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (y : ℕ) (hy : y ∈ candidateBand r) :
    y ∉ prescribedVertices n r := by
  obtain ⟨hylo,hyhi⟩ := mem_Ico.mp hy
  have hR : 4 ≤ r*r := by nlinarith
  have hys : 18 < y := by nlinarith
  have hny : y+3 < n := by nlinarith
  intro hm
  rcases mem_union.mp hm with hm | hm
  · simp only [mem_insert,mem_singleton] at hm
    omega
  · obtain ⟨i,_,hi⟩ := mem_biUnion.mp hm
    obtain ⟨hP,hC,hN,_⟩ := connectorPrefix_value_bounds hr i
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with hi | hi | hi <;> nlinarith only [hi,hP,hC,hN,hylo,hyhi,hR]

theorem prescribedColors_bound {r n : ℕ} [NeZero r] (hr : 2 ≤ r)
    (d : ℕ) (hd : d ∈ prescribedColors n r) : d ≤ 52*r*r ∨ d=n-14 := by
  have hR : 4 ≤ r*r := by nlinarith
  rcases mem_union.mp hd with hd | hd
  · have hp := (connectorPrefix_value_bounds hr (firstCell r)).1
    have hsub := Nat.sub_le (predecessor (firstCell r).1 (firstCell r).2) 18
    simp only [mem_insert,mem_singleton] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd | hd
    all_goals first | exact Or.inr hd | (left; omega) | (left; nlinarith)
  · obtain ⟨i,_,hi⟩ := mem_biUnion.mp hd
    obtain ⟨_,_,_,_,hA,hB⟩ := connectorPrefix_value_bounds hr i
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Or.inl hA
    · exact Or.inl hB

/-- Every possible actual connector gap is above the fixed connector-prefix color bands
and below the exceptional initial color `n-14`. -/
theorem connector_gap_separation {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (previous next : Cell r)
    (y : ℕ) (hy : y ∈ candidateBand r) :
    52*r*r < wrapOut n y (successor previous.1 previous.2) ∧
    wrapOut n y (successor previous.1 previous.2) < n-14 ∧
    52*r*r < wrapIn n y (predecessor next.1 next.2) ∧
    wrapIn n y (predecessor next.1 next.2) < n-14 := by
  obtain ⟨hylo,hyhi⟩ := mem_Ico.mp hy
  obtain ⟨hP,_,_,_⟩ := connectorPrefix_value_bounds hr next
  obtain ⟨_,_,hNlo,hNhi,_⟩ := connectorPrefix_value_bounds hr previous
  have hR : 4 ≤ r*r := by nlinarith
  have hNn : successor previous.1 previous.2 < n := by nlinarith
  have hyn : y < n := by nlinarith only [hyhi,hn,hR]
  have ho : successor previous.1 previous.2+
      wrapOut n y (successor previous.1 previous.2) = n+y := by dsimp [wrapOut]; omega
  have hi : y+wrapIn n y (predecessor next.1 next.2) =
      n+predecessor next.1 next.2 := by dsimp [wrapIn]; omega
  have h14 : 14 ≤ n := by nlinarith
  have hsub : n-14+14=n := Nat.sub_add_cancel h14
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [ho,hn,hylo,hNhi,hR]
  · nlinarith only [ho,hyhi,hNlo,hsub,hR]
  · nlinarith only [hi,hn,hyhi,hR]
  · nlinarith only [hi,hP,hylo,hsub,hR]

theorem connector_avoids_prescribedColors {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (previous next : Cell r)
    (y : ℕ) (hy : y ∈ candidateBand r) :
    wrapOut n y (successor previous.1 previous.2) ∉ prescribedColors n r ∧
    wrapIn n y (predecessor next.1 next.2) ∉ prescribedColors n r := by
  obtain ⟨ho0,hoN,hi0,hiN⟩ := connector_gap_separation hr hn previous next y hy
  constructor
  · intro h
    rcases prescribedColors_bound hr _ h with h | h <;> omega
  · intro h
    rcases prescribedColors_bound hr _ h with h | h <;> omega

/-- A literal previous connector and its two incident connector-prefix cells. -/
structure ConnectorRecord (r : ℕ) where
  previous : Cell r
  next : Cell r
  value : ℕ
  deriving DecidableEq

def historyVertices {r : ℕ} (history : List (ConnectorRecord r)) : Finset ℕ :=
  history.toFinset.image ConnectorRecord.value

def historyColors {r : ℕ} (n : ℕ) (history : List (ConnectorRecord r)) : Finset ℕ :=
  history.toFinset.biUnion (fun s =>
    {wrapOut n s.value (successor s.previous.1 s.previous.2),
     wrapIn n s.value (predecessor s.next.1 s.next.2)})

theorem historyVertices_card {r : ℕ} (history : List (ConnectorRecord r)) :
    (historyVertices history).card ≤ history.length :=
  card_image_le.trans (List.toFinset_card_le _)

theorem historyColors_card {r : ℕ} (n : ℕ) (history : List (ConnectorRecord r)) :
    (historyColors n history).card ≤ 2*history.length := by
  calc
    (historyColors n history).card ≤
        ∑ s ∈ history.toFinset,
          ({wrapOut n s.value (successor s.previous.1 s.previous.2),
            wrapIn n s.value (predecessor s.next.1 s.next.2)} : Finset ℕ).card := card_biUnion_le
    _ ≤ ∑ _s ∈ history.toFinset, 2 := sum_le_sum (fun _ _ => card_le_two)
    _ = 2*history.toFinset.card := by simp [Nat.mul_comm]
    _ ≤ 2*history.length := Nat.mul_le_mul_left 2 (List.toFinset_card_le _)

theorem candidateBand_card (r : ℕ) : (candidateBand r).card = 10*r*r := by
  have he : 40*r*r = 30*r*r+10*r*r := by ring
  simp only [candidateBand,Nat.card_Ico]
  omega

/-- Actual next-step greedy existence. The consumed vertex/color sets are
computed from the supplied finite history; their cardinal bounds and their
separation from all prescribed connector-prefix data are conclusions of earlier lemmas.
The history need not be assumed valid, simple, rainbow, or already chosen
by a successful greedy family. -/
theorem connectorPrefix_extend_history {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (history : List (ConnectorRecord r)) (ht : history.length ≤ r*r-2)
    (previous next : Cell r) :
    ∃ y ∈ candidateBand r,
      y ∉ prescribedVertices n r ∪ historyVertices history ∧
      wrapOut n y (successor previous.1 previous.2) ∉
        prescribedColors n r ∪ historyColors n history ∧
      wrapIn n y (predecessor next.1 next.2) ∉
        prescribedColors n r ∪ historyColors n history ∧
      wrapOut n y (successor previous.1 previous.2) ≠
        wrapIn n y (predecessor next.1 next.2) ∧
      0 < wrapOut n y (successor previous.1 previous.2) ∧
      wrapOut n y (successor previous.1 previous.2) < n ∧
      0 < wrapIn n y (predecessor next.1 next.2) ∧
      wrapIn n y (predecessor next.1 next.2) < n := by
  have horder : ∀ y ∈ candidateBand r,
      predecessor next.1 next.2<y ∧ y<successor previous.1 previous.2 ∧
        successor previous.1 previous.2<n := by
    intro y hy
    exact connectorPrefix_connector_order hr hn (fun _ => y) (fun _ => mem_Ico.mp hy) previous next
  have hcard : (candidateBand r ∩ historyVertices history).card+
      2*(historyColors n history).card+1 < (candidateBand r).card := by
    have hV : (candidateBand r ∩ historyVertices history).card ≤ history.length :=
      (card_le_card inter_subset_right).trans (historyVertices_card history)
    have hD := historyColors_card n history
    have hR : 4 ≤ r*r := by nlinarith
    have ht' : history.length+2 ≤ r*r := by omega
    rw [candidateBand_card]
    nlinarith only [hV,hD,ht',hR]
  obtain ⟨y,hy,hv,ho,hi,hne,hrest⟩ := exists_two_wrap_connector n
    (predecessor next.1 next.2) (successor previous.1 previous.2)
    (candidateBand r) (historyVertices history) (historyColors n history) horder hcard
  obtain ⟨hoBase,hiBase⟩ := connector_avoids_prescribedColors hr hn previous next y hy
  refine ⟨y,hy,?_,?_,?_,hne,hrest⟩
  · simp only [mem_union,not_or]
    exact ⟨band_avoids_prescribedVertices hr hn y hy,hv⟩
  · simp only [mem_union,not_or]
    exact ⟨hoBase,ho⟩
  · simp only [mem_union,not_or]
    exact ⟨hiBase,hi⟩

end CorralFormalization.LatinCompletion.LatinPrefixSupply.ConnectorGreedy
