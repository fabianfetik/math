import CorralFormalization.DiversityCompletion.LatinConnectorInterleave
import CorralFormalization.DiversityCompletion.LatinConnectorPathShape
import CorralFormalization.DiversityCompletion.EndpointPathSupplier

/-! The deterministic connector-prefix prefix is actually simple, nonzero and rainbow.
Its only selection input is the previously constructed fresh connector run. -/

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix

open Finset LatinTransfer TerraceLift LatinPrefix ConnectorGreedy TerraceCompletion

variable {r n : ℕ} [NeZero r]

theorem fixedVertex_range (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (x : ℕ) (hx : x ∈ fixedVertexList n r) : 0 < x ∧ x < n := by
  have hR : 4 ≤ r*r := by nlinarith
  have hlarge : 400 ≤ n := by nlinarith
  rcases List.mem_append.mp hx with hs | hc
  · simp only [startVertices, List.mem_cons, List.mem_nil_iff, or_false] at hs
    omega
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
    have hb := point_range hr hn i
    simp only [vertexBlock, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> omega

theorem fixedColor_range (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (d : ℕ) (hd : d ∈ fixedColorList n r) : 0 < d ∧ d < n := by
  have hR : 4 ≤ r*r := by nlinarith
  have hlarge : 400 ≤ n := by nlinarith
  rcases List.mem_append.mp hd with hs | hc
  · rcases List.mem_append.mp hs with hs | hj
    · simp only [startColors, List.mem_cons, List.mem_nil_iff, or_false] at hs
      omega
    · have he : d = firstJoin r := by simpa using hj
      have hb := firstJoin_range hr hn
      omega
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
    have hb := color_range hr hn i
    simp only [colorBlock, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> omega

theorem recordValue_range (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (records : List (ConnectorRecord r))
    (hfresh : ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t])
    (x : ℕ) (hx : x ∈ records.map ConnectorRecord.value) : 0 < x ∧ x < n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hs
  have hb := Finset.mem_Ico.mp (hfresh t ht).1
  have hR : 4 ≤ r*r := by nlinarith
  constructor <;> nlinarith

theorem recordColor_range (records : List (ConnectorRecord r))
    (hfresh : ∀ t (ht : t < records.length), FreshRecord n (records.take t) records[t])
    (d : ℕ) (hd : d ∈ records.flatMap (recordColors n)) : 0 < d ∧ d < n := by
  obtain ⟨s, hs, hi⟩ := List.mem_flatMap.mp hd
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hs
  obtain ⟨_, _, _, _, _, hO, hOn, hI, hIn⟩ := hfresh t ht
  simp only [recordColors, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hO,hOn⟩
  · exact ⟨hI,hIn⟩

theorem connectorPrefixVertices_range (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hfresh : ∀ t (ht : t < records.length),
      y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t])
    (x : ℕ) (hx : x ∈ connectorPrefixVertices n y) : 0 < x ∧ x < n := by
  have hp := connectorPrefixVertices_perm_pools (n := n) y records hmap (fun t ht => (hfresh t ht).1)
  rcases List.mem_append.mp (hp.mem_iff.mp hx) with hf | hc
  · exact fixedVertex_range hr hn x hf
  · exact recordValue_range hr hn records (fun t ht => (hfresh t ht).2) x hc

theorem connectorPrefixPath_nodup (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hfresh : ∀ t (ht : t < records.length),
      y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t]) :
    (connectorPrefixPath n y).Nodup := by
  apply List.Nodup.map_on (f := fun x : ℕ => (x : ZMod n)) ?_
    (connectorPrefixVertices_nodup hr hn y records hmap hfresh)
  intro x hx z hz he
  have hb := connectorPrefixVertices_range hr hn y records hmap hfresh x hx
  have hc := connectorPrefixVertices_range hr hn y records hmap hfresh z hz
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hb.2, ZMod.val_natCast_of_lt hc.2] at hv
  exact hv

theorem connectorPrefixPath_nonzero (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hfresh : ∀ t (ht : t < records.length),
      y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t])
    (z : ZMod n) (hz : z ∈ connectorPrefixPath n y) : z ≠ 0 := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  have hb := connectorPrefixVertices_range hr hn y records hmap hfresh x hx
  intro he
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hb.2, ZMod.val_zero] at hv
  omega

theorem connectorPrefixPath_colors (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hfresh : ∀ t (ht : t < records.length),
      y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t])
    (d : ℕ) (hd : d ∈ pathGaps (connectorPrefixPath n y)) : 0 < d ∧ d < n := by
  have hp := connectorPrefixPathGaps_perm_pools hr hn y hy records hmap (fun t ht => (hfresh t ht).1)
  rcases List.mem_append.mp (hp.mem_iff.mp hd) with hf | hc
  · exact fixedColor_range hr hn d hf
  · exact recordColor_range records (fun t ht => (hfresh t ht).2) d hc

/-- The actual path, with the actual first and last vertex, supplies all
fields of RainbowPrefix from the constructed fresh connector history. -/
theorem rainbowPrefix_from_records (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hfresh : ∀ t (ht : t < records.length),
      y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t]) :
    ∃ P : RainbowPrefix n, P.path = connectorPrefixPath n y ∧
      P.first = ((n-3 : ℕ) : ZMod n) ∧
      pathGaps P.path = [2,3,10,n-14,12] ++ connectorPrefixGaps n y := by
  obtain ⟨interior, hdec, _⟩ := connectorPrefixPath_decomposition n y
  let P : RainbowPrefix n := {
    first := ((n-3 : ℕ) : ZMod n)
    last := (connectorPrefixLastValue r : ZMod n)
    interior := interior
    simple := by rw [← hdec]; exact connectorPrefixPath_nodup hr hn y records hmap hfresh
    nonzero := by
      intro z hz
      rw [← hdec] at hz
      exact connectorPrefixPath_nonzero hr hn y records hmap hfresh z hz
    rainbow := by rw [← hdec]; exact connectorPrefixPath_rainbow hr hn y hy records hmap hfresh
    colors := by
      intro d hd
      rw [← hdec] at hd
      exact connectorPrefixPath_colors hr hn y hy records hmap hfresh d hd
  }
  have hpath : P.path = connectorPrefixPath n y := hdec.symm
  refine ⟨P,hpath,rfl,?_⟩
  rw [hpath]
  exact connectorPrefixPath_pathGaps hr hn y hy

/-- The deterministic simple rainbow connector-prefix prefix now exists for every
connector-prefix numeric regime, without any endpoint-completion assumption. -/
theorem connectorPrefix_rainbowPrefix_exists (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    ∃ (y : Cell r → ℕ) (P : RainbowPrefix n),
      (∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r) ∧ P.path = connectorPrefixPath n y ∧
      P.first = ((n-3 : ℕ) : ZMod n) ∧
      pathGaps P.path = [2,3,10,n-14,12] ++ connectorPrefixGaps n y := by
  obtain ⟨y,records,hy,_,hmap,hfresh⟩ := connectorPrefix_connector_function_exists hr hn
  obtain ⟨P,hpath,hfirst,hgap⟩ := rainbowPrefix_from_records hr hn y hy records hmap hfresh
  exact ⟨y,P,hy,hpath,hfirst,hgap⟩

/-- Exactly the remaining prefix-supplier argument of
`hprefix_and_path_supplier_of_separate_paths`, now proved for the actual connector-prefix path. -/
theorem hprefix_supplier (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (records : List (ConnectorRecord r))
    (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (_hlen : records.length = r*r-1)
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hfresh : ∀ t (ht : t < records.length),
      y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t]) :
    ∃ P : RainbowPrefix n,
      P.first = ((n-3 : ℕ) : ZMod n) ∧
      pathGaps P.path = [2,3,10,n-14,12] ++ connectorPrefixGaps n y := by
  obtain ⟨P,_,hfirst,hgap⟩ := rainbowPrefix_from_records hr hn y hy records hmap hfresh
  exact ⟨P,hfirst,hgap⟩

end CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix
