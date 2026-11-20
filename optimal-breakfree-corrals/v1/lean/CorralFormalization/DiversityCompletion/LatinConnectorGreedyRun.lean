import CorralFormalization.DiversityCompletion.LatinConnectorGreedyBands

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.ConnectorGreedy

open Finset LatinTransfer TerraceLift LatinPrefix

/-- Exactly the verified next-step conditions, relative to the actual
preceding finite record history. -/
def FreshRecord {r : ℕ} [NeZero r] (n : ℕ)
    (history : List (ConnectorRecord r)) (s : ConnectorRecord r) : Prop :=
  s.value ∈ candidateBand r ∧
  s.value ∉ prescribedVertices n r ∪ historyVertices history ∧
  wrapOut n s.value (successor s.previous.1 s.previous.2) ∉
    prescribedColors n r ∪ historyColors n history ∧
  wrapIn n s.value (predecessor s.next.1 s.next.2) ∉
    prescribedColors n r ∪ historyColors n history ∧
  wrapOut n s.value (successor s.previous.1 s.previous.2) ≠
    wrapIn n s.value (predecessor s.next.1 s.next.2) ∧
  0 < wrapOut n s.value (successor s.previous.1 s.previous.2) ∧
  wrapOut n s.value (successor s.previous.1 s.previous.2) < n ∧
  0 < wrapIn n s.value (predecessor s.next.1 s.next.2) ∧
  wrapIn n s.value (predecessor s.next.1 s.next.2) < n

/-- A finite run over prescribed cell-to-cell connector edges. The actual
history is extended by the selected record at each recursive step. -/
def FreshRun {r : ℕ} [NeZero r] (n : ℕ) (history : List (ConnectorRecord r)) :
    List (Cell r × Cell r) → List (ConnectorRecord r) → Prop
  | [], [] => True
  | edge :: edges, s :: records =>
      s.previous=edge.1 ∧ s.next=edge.2 ∧ FreshRecord n history s ∧
        FreshRun n (history++[s]) edges records
  | _, _ => False

theorem exists_freshRun {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (edges : List (Cell r × Cell r))
    (history : List (ConnectorRecord r))
    (hcount : history.length+edges.length ≤ r*r-1) :
    ∃ records, FreshRun n history edges records := by
  induction edges generalizing history with
  | nil => exact ⟨[], trivial⟩
  | cons edge edges ih =>
    have hR : 4 ≤ r*r := by nlinarith
    have hstep : history.length ≤ r*r-2 := by simp only [List.length_cons] at hcount; omega
    obtain ⟨y,hy,hv,ho,hi,hne,hpos⟩ := connectorPrefix_extend_history hr hn history hstep edge.1 edge.2
    let s : ConnectorRecord r := ⟨edge.1,edge.2,y⟩
    have hs : FreshRecord n history s := ⟨hy,hv,ho,hi,hne,hpos⟩
    have hnext : (history++[s]).length+edges.length ≤ r*r-1 := by
      simp only [List.length_append,List.length_cons,List.length_nil] at hcount ⊢
      omega
    obtain ⟨records,hrecords⟩ := ih (history++[s]) hnext
    exact ⟨s::records,rfl,rfl,hs,hrecords⟩

theorem freshRun_map_edges {r n : ℕ} [NeZero r]
    (history : List (ConnectorRecord r)) (edges : List (Cell r × Cell r))
    (records : List (ConnectorRecord r)) (h : FreshRun n history edges records) :
    records.map (fun s => (s.previous,s.next)) = edges := by
  induction edges generalizing history records with
  | nil => cases records <;> simp_all [FreshRun]
  | cons edge edges ih =>
    cases records with
    | nil => simp [FreshRun] at h
    | cons s records =>
      obtain ⟨hp,hn,_,ht⟩ := h
      simp only [List.map_cons]
      rw [hp,hn,ih (history++[s]) records ht]

theorem freshRun_length {r n : ℕ} [NeZero r]
    (history : List (ConnectorRecord r)) (edges : List (Cell r × Cell r))
    (records : List (ConnectorRecord r)) (h : FreshRun n history edges records) :
    records.length = edges.length := by
  simpa only [List.length_map] using congrArg List.length (freshRun_map_edges history edges records h)

/-- Every selected record is fresh relative to precisely the earlier
records in the returned list, together with any initial history. -/
theorem freshRun_get {r n : ℕ} [NeZero r]
    (history : List (ConnectorRecord r)) (edges : List (Cell r × Cell r))
    (records : List (ConnectorRecord r)) (h : FreshRun n history edges records)
    (t : ℕ) (ht : t < records.length) :
    FreshRecord n (history++records.take t) records[t] := by
  induction records generalizing history edges t with
  | nil => simp at ht
  | cons s records ih =>
    cases edges with
    | nil => simp [FreshRun] at h
    | cons edge edges =>
      obtain ⟨_,_,hs,hrun⟩ := h
      cases t with
      | zero => simpa using hs
      | succ t =>
        have ht' : t < records.length := by simpa using ht
        simpa only [List.take_succ_cons,List.getElem_cons_succ,List.append_assoc,
          List.singleton_append] using ih (history++[s]) edges hrun t ht'

/-- Full finite iteration for at most `r^2-1` prescribed connector edges.
The returned records have exactly those endpoints, and every value and
its two colors are fresh relative to the actual returned prefix history. -/
theorem connectorPrefix_greedy_connectors {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (edges : List (Cell r × Cell r))
    (hcount : edges.length ≤ r*r-1) :
    ∃ records : List (ConnectorRecord r),
      records.length=edges.length ∧
      records.map (fun s => (s.previous,s.next))=edges ∧
      ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t] := by
  obtain ⟨records,h⟩ := exists_freshRun hr hn edges [] (by simpa using hcount)
  refine ⟨records,freshRun_length [] edges records h,freshRun_map_edges [] edges records h,?_⟩
  intro t ht
  simpa only [List.nil_append] using freshRun_get [] edges records h t ht

/-- The actual consecutive pairs in the lexicographic connector-prefix order. -/
def lexEdges (r : ℕ) : List (Cell r × Cell r) := (lexCells r).zip (lexCells r).tail

theorem lexEdges_length (r : ℕ) : (lexEdges r).length = r*r-1 := by
  simp only [lexEdges,List.length_zip,List.length_tail,lexCells_length]
  exact Nat.min_eq_right (Nat.sub_le _ _)

/-- Actual connector-prefix connector records exist for every consecutive cell pair.
This is a connector selection theorem, not a completed-prefix or endpoint
existence theorem; the prescribed connector-prefix data's internal rainbow proof is separate. -/
theorem connectorPrefix_lex_greedy_connectors {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    ∃ records : List (ConnectorRecord r),
      records.length=r*r-1 ∧
      records.map (fun s => (s.previous,s.next))=lexEdges r ∧
      ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t] := by
  obtain ⟨records,hlen,hmap,hfresh⟩ := connectorPrefix_greedy_connectors hr hn (lexEdges r)
    (by rw [lexEdges_length])
  exact ⟨records,hlen.trans (lexEdges_length r),hmap,hfresh⟩

end CorralFormalization.LatinCompletion.LatinPrefixSupply.ConnectorGreedy
