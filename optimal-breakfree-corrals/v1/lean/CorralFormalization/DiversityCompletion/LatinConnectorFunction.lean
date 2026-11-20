import CorralFormalization.DiversityCompletion.LatinConnectorGreedyRun

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.ConnectorGreedy

open Finset LatinTransfer TerraceLift LatinPrefix

/-- Read the connector attached to a preceding connector-prefix cell from its actual
lexicographic rank. The final unused value is set to the band minimum. -/
def connectorFunction {r : ℕ} (records : List (ConnectorRecord r)) (i : Cell r) : ℕ :=
  if h : (finProdFinEquiv i).val < records.length then
    records[(finProdFinEquiv i).val].value
  else 30*r*r

theorem connectorFunction_band {r : ℕ} (hr : 2 ≤ r)
    (records : List (ConnectorRecord r))
    (hband : ∀ t (ht : t < records.length), records[t].value ∈ candidateBand r)
    (i : Cell r) : connectorFunction records i ∈ candidateBand r := by
  unfold connectorFunction
  split
  · exact hband _ _
  · apply mem_Ico.mpr
    exact ⟨le_rfl,by nlinarith⟩

/-- Exact endpoints in the returned lexicographic record sequence pay the
rank lookup; no independent indexing or connector-function premise is used. -/
theorem records_previous_rank {r : ℕ} (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (t : ℕ) (ht : t < records.length) :
    (finProdFinEquiv records[t].previous).val = t := by
  have hlen : records.length = (lexEdges r).length := by
    simpa only [List.length_map] using congrArg List.length hmap
  have htEdge : t < (lexEdges r).length := ht.trans_eq hlen
  have htLex : t < (lexCells r).length := by
    rw [lexEdges_length] at htEdge
    rw [lexCells_length]
    omega
  have he : (records[t].previous,records[t].next) = (lexEdges r)[t] := by
    have heq := List.getElem_of_eq hmap (by simpa only [List.length_map] using ht)
    rw [List.getElem_map] at heq
    exact heq
  have hp : records[t].previous = (lexCells r)[t] := by
    simpa [lexEdges] using congrArg Prod.fst he
  rw [hp]
  exact lexCells_rank r t htLex

theorem connectorFunction_matches {r : ℕ} (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (t : ℕ) (ht : t < records.length) :
    connectorFunction records records[t].previous = records[t].value := by
  have hRank := records_previous_rank records hmap t ht
  simp only [connectorFunction,hRank,dif_pos ht]

/-- A band-bounded connector function for the literal `connectorPrefixGaps n y` is
constructed from the finite greedy run. Each of its used values is exactly
the corresponding fresh record's value, with exactly the prescribed connector-prefix
cell-to-cell endpoints. Internal connector-prefix rainbow/vertex simplicity and endpoint
completion remain separate statements. -/
theorem connectorPrefix_connector_function_exists {r n : ℕ} [NeZero r]
    (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    ∃ (y : Cell r → ℕ) (records : List (ConnectorRecord r)),
      (∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r) ∧
      records.length = r*r-1 ∧
      records.map (fun s => (s.previous,s.next)) = lexEdges r ∧
      ∀ t (ht : t < records.length),
        y records[t].previous = records[t].value ∧
        FreshRecord n (records.take t) records[t] := by
  obtain ⟨records,hlen,hmap,hfresh⟩ := connectorPrefix_lex_greedy_connectors hr hn
  refine ⟨connectorFunction records,records,?_,hlen,hmap,?_⟩
  · intro i
    exact mem_Ico.mp (connectorFunction_band hr records (fun t ht => (hfresh t ht).1) i)
  · intro t ht
    exact ⟨connectorFunction_matches records hmap t ht,hfresh t ht⟩

end CorralFormalization.LatinCompletion.LatinPrefixSupply.ConnectorGreedy
