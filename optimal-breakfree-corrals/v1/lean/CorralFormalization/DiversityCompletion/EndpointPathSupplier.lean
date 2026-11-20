import CorralFormalization.DiversityCompletion.EndpointSplice
import CorralFormalization.DiversityCompletion.LatinConnectorFunction

namespace CorralFormalization.LatinCompletion.TerraceCompletion

open LatinTransfer LatinPrefix LatinPrefixSupply ConnectorGreedy

/-- A given actual simple rainbow path. This object contains no completion
path and no cyclic terrace. -/
structure RainbowPrefix (n : ℕ) where
  first : ZMod n
  last : ZMod n
  interior : List (ZMod n)
  simple : ((first::interior) ++ [last]).Nodup
  nonzero : ∀ x ∈ (first::interior) ++ [last], x ≠ 0
  rainbow : (pathGaps ((first::interior) ++ [last])).Nodup
  colors : ∀ d ∈ pathGaps ((first::interior) ++ [last]), 0 < d ∧ d < n

namespace RainbowPrefix

def path {n : ℕ} (P : RainbowPrefix n) : List (ZMod n) :=
  (P.first::P.interior) ++ [P.last]

/-- A separately given actual endpoint path on precisely the remaining
vertices and colours. Its return endpoints are fixed by P. This is the
conclusion needed from endpoint completion, not an existence assertion. -/
structure ComplementaryPath {n : ℕ} (P : RainbowPrefix n) where
  interior : List (ZMod n)
  simple : ((P.last::interior) ++ [P.first]).Nodup
  vertices : ∀ x, x ∈ (P.last::interior) ++ [P.first] ↔ x ≠ 0 ∧ x ∉ P.interior
  rainbow : (pathGaps ((P.last::interior) ++ [P.first])).Nodup
  colors : ∀ d, d ∈ pathGaps ((P.last::interior) ++ [P.first]) ↔
    0 < d ∧ d < n ∧ d ∉ pathGaps P.path

def splice {n : ℕ} (P : RainbowPrefix n) (Q : P.ComplementaryPath) :
    EndpointSpliceInput n where
  first := P.first
  last := P.last
  prefixInterior := P.interior
  completionInterior := Q.interior
  prefix_simple := P.simple
  prefix_nonzero := P.nonzero
  prefix_rainbow := P.rainbow
  prefix_colors := P.colors
  completion_simple := Q.simple
  remaining_vertices := Q.vertices
  completion_rainbow := Q.rainbow
  remaining_colors := Q.colors

theorem splice_first {n : ℕ} (P : RainbowPrefix n) (Q : P.ComplementaryPath) :
    (P.splice Q).first = P.first := rfl

theorem splice_prefix {n : ℕ} (P : RainbowPrefix n) (Q : P.ComplementaryPath) :
    (P.splice Q).prefixPath = P.path := rfl

/-- The supplied connector-prefix prefix and its separately supplied complementary path
give exactly the local supplier result required by GreedyConnectorOrbits. -/
theorem supply_connectorPrefix {n r : ℕ} [NeZero r] (y : Cell r → ℕ)
    (P : RainbowPrefix n) (Q : P.ComplementaryPath)
    (hfirst : P.first = ((n-3 : ℕ) : ZMod n))
    (hprefix : pathGaps P.path = [2,3,10,n-14,12] ++ connectorPrefixGaps n y) :
    ∃ S : EndpointSpliceInput n,
      S.first = ((n-3 : ℕ) : ZMod n) ∧
      pathGaps S.prefixPath = [2,3,10,n-14,12] ++ connectorPrefixGaps n y :=
  ⟨P.splice Q,hfirst,hprefix⟩

end RainbowPrefix

/-- Separate remaining suppliers suffice for the exact visible hypothesis
of GreedyConnectorOrbits. Neither hypothesis assumes a completed terrace, corral,
physical frame, tail pattern or orbit count. This theorem proves no
existential endpoint-completion principle. -/
theorem hprefix_and_path_supplier_of_separate_paths {n r : ℕ} [NeZero r]
    (hprefix_supplier : ∀ (y : Cell r → ℕ) (records : List (ConnectorRecord r)),
      (∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r) →
      records.length = r*r-1 →
      records.map (fun s => (s.previous,s.next)) = lexEdges r →
      (∀ t (ht : t < records.length),
        y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t]) →
      ∃ P : RainbowPrefix n,
        P.first = ((n-3 : ℕ) : ZMod n) ∧
        pathGaps P.path = [2,3,10,n-14,12] ++ connectorPrefixGaps n y)
    (hendpoint_supplier : ∀ (y : Cell r → ℕ) (P : RainbowPrefix n),
      P.first = ((n-3 : ℕ) : ZMod n) →
      pathGaps P.path = [2,3,10,n-14,12] ++ connectorPrefixGaps n y →
      Nonempty P.ComplementaryPath) :
    ∀ (y : Cell r → ℕ) (records : List (ConnectorRecord r)),
      (∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r) →
      records.length = r*r-1 →
      records.map (fun s => (s.previous,s.next)) = lexEdges r →
      (∀ t (ht : t < records.length),
        y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t]) →
      ∃ S : EndpointSpliceInput n,
        S.first = ((n-3 : ℕ) : ZMod n) ∧
        pathGaps S.prefixPath = [2,3,10,n-14,12] ++ connectorPrefixGaps n y := by
  intro y records hy hlen hmap hfresh
  obtain ⟨P,hfirst,hprefix⟩ := hprefix_supplier y records hy hlen hmap hfresh
  obtain ⟨Q⟩ := hendpoint_supplier y P hfirst hprefix
  exact P.supply_connectorPrefix y Q hfirst hprefix

end CorralFormalization.LatinCompletion.TerraceCompletion
