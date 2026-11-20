import CorralFormalization.DiversityCompletion.LatinConnectorFixedSeparation
import CorralFormalization.DiversityCompletion.LatinConnectorFunction

/-! Freshness in the actual returned connector history proves simplicity
and rainbow of the connector pools, disjoint from all fixed connector-prefix data. -/

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix

open Finset LatinTransfer TerraceLift LatinPrefix ConnectorGreedy

variable {r n : ℕ} [NeZero r]

def recordColors (n : ℕ) (s : ConnectorRecord r) : List ℕ :=
  [wrapOut n s.value (successor s.previous.1 s.previous.2),
   wrapIn n s.value (predecessor s.next.1 s.next.2)]

theorem mem_lexCells (r : ℕ) (i : Cell r) : i ∈ lexCells r :=
  (lexCells_perm r).mem_iff.mpr (by simp)

theorem fixedVertex_mem_prescribed (x : ℕ) (hx : x ∈ fixedVertexList n r) :
    x ∈ prescribedVertices n r := by
  rcases List.mem_append.mp hx with hs | hc
  · apply Finset.mem_union_left
    simpa only [startVertices, List.mem_cons, List.mem_nil_iff, or_false,
      Finset.mem_insert, Finset.mem_singleton] using hs
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simpa only [vertexBlock, P, C, N, List.mem_cons, List.mem_nil_iff, or_false,
      Finset.mem_insert, Finset.mem_singleton] using hi

theorem fixedColor_mem_prescribed (d : ℕ) (hd : d ∈ fixedColorList n r) :
    d ∈ prescribedColors n r := by
  rcases List.mem_append.mp hd with hs | hc
  · apply Finset.mem_union_left
    simpa only [List.mem_append, startColors, firstJoin, P, List.mem_cons,
      List.mem_nil_iff, or_false, Finset.mem_insert, Finset.mem_singleton, or_assoc] using hs
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simpa only [colorBlock, incoming, outgoing, List.mem_cons, List.mem_nil_iff, or_false,
      Finset.mem_insert, Finset.mem_singleton] using hi

theorem getElem_mem_take {A : Type*} (xs : List A) (i j : ℕ)
    (hi : i < xs.length) (hj : j < xs.length) (hij : i < j) :
    xs[i] ∈ xs.take j := by
  have hit : i < (xs.take j).length := by simp only [List.length_take]; omega
  simpa only [List.getElem_take] using List.getElem_mem hit

theorem recordValues_nodup (records : List (ConnectorRecord r))
    (hfresh : ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t]) :
    (records.map ConnectorRecord.value).Nodup := by
  change (records.map ConnectorRecord.value).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  have hm : records[i].value ∈ historyVertices (records.take j) :=
    Finset.mem_image.mpr ⟨records[i], List.mem_toFinset.mpr
      (getElem_mem_take records i j hi hj hij), rfl⟩
  exact (hfresh j hj).2.1 (Finset.mem_union_right _ (he ▸ hm))

theorem recordColors_nodup (records : List (ConnectorRecord r))
    (hfresh : ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t]) :
    (records.flatMap (recordColors n)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hs
    have hne := (hfresh t ht).2.2.2.2.1
    simpa only [recordColors, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
      List.nodup_nil, not_false_eq_true, and_true, or_false] using hne
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij d hd he
    have hm : d ∈ historyColors n (records.take j) := by
      apply Finset.mem_biUnion.mpr
      refine ⟨records[i], List.mem_toFinset.mpr (getElem_mem_take records i j hi hj hij), ?_⟩
      simpa only [recordColors, List.mem_cons, List.mem_nil_iff, or_false,
        Finset.mem_insert, Finset.mem_singleton] using hd
    obtain ⟨_, _, hOut, hIn, _, _⟩ := hfresh j hj
    simp only [recordColors, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact hOut (Finset.mem_union_right _ hm)
    · exact hIn (Finset.mem_union_right _ hm)

theorem fixed_disjoint_recordValues (records : List (ConnectorRecord r))
    (hfresh : ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t]) :
    List.Disjoint (fixedVertexList n r) (records.map ConnectorRecord.value) := by
  intro x hx hy
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hs
  exact (hfresh t ht).2.1 (Finset.mem_union_left _ (fixedVertex_mem_prescribed _ hx))

theorem fixed_disjoint_recordColors (records : List (ConnectorRecord r))
    (hfresh : ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t]) :
    List.Disjoint (fixedColorList n r) (records.flatMap (recordColors n)) := by
  intro d hd he
  obtain ⟨s, hs, hi⟩ := List.mem_flatMap.mp he
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hs
  obtain ⟨_, _, hOut, hIn, _, _⟩ := hfresh t ht
  have hm := fixedColor_mem_prescribed d hd
  simp only [recordColors, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl
  · exact hOut (Finset.mem_union_left _ hm)
  · exact hIn (Finset.mem_union_left _ hm)

theorem fixed_and_recordValues_nodup (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (records : List (ConnectorRecord r))
    (hfresh : ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t]) :
    (fixedVertexList n r ++ records.map ConnectorRecord.value).Nodup :=
  (fixedVertexList_nodup hr hn).append (recordValues_nodup records hfresh)
    (fixed_disjoint_recordValues records hfresh)

theorem fixed_and_recordColors_nodup (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (records : List (ConnectorRecord r))
    (hfresh : ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t]) :
    (fixedColorList n r ++ records.flatMap (recordColors n)).Nodup :=
  (fixedColorList_nodup hr hn).append (recordColors_nodup records hfresh)
    (fixed_disjoint_recordColors records hfresh)

end CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix
