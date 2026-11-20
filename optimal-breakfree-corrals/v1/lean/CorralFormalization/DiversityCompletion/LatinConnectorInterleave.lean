import CorralFormalization.DiversityCompletion.LatinConnectorFreshPools
import CorralFormalization.DiversityCompletion.LatinConnectorPathGaps

/-! The literal interleaved connector-prefix path and its real gap word are permutations
of the proved-disjoint fixed and fresh connector pools. -/

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix

open Finset LatinTransfer TerraceLift LatinPrefix ConnectorGreedy TerraceCompletion

def chainBlocks {I A : Type*} (B : I → List A) (K : I → I → List A)
    (first : I) : List I → List A
  | [] => B first
  | next :: rest => B first ++ K first next ++ chainBlocks B K next rest

theorem append_shuffle_perm {A : Type*} (a b c d : List A) :
    (a++b++c++d).Perm (a++c++b++d) := by
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add]
  ac_rfl

theorem chainBlocks_perm {I A : Type*} (B : I → List A) (K : I → I → List A)
    (first : I) (rest : List I) :
    (chainBlocks B K first rest).Perm
      ((first::rest).flatMap B ++ ((first::rest).zip rest).flatMap (fun e => K e.1 e.2)) := by
  induction rest generalizing first with
  | nil => simp [chainBlocks]
  | cons next rest ih =>
    have h1 := (List.Perm.refl (B first++K first next)).append (ih next)
    have h2 := append_shuffle_perm (B first) (K first next)
      ((next::rest).flatMap B) (((next::rest).zip rest).flatMap (fun e => K e.1 e.2))
    have h1' : (B first++K first next++chainBlocks B K next rest).Perm
        (B first++K first next++(next::rest).flatMap B++
          ((next::rest).zip rest).flatMap (fun e => K e.1 e.2)) := by
      simpa only [List.append_assoc] using h1
    have h2' : (B first++K first next++(next::rest).flatMap B++
          ((next::rest).zip rest).flatMap (fun e => K e.1 e.2)).Perm
        (B first++(next::rest).flatMap B++K first next++
          ((next::rest).zip rest).flatMap (fun e => K e.1 e.2)) := by
      simpa only [List.append_assoc] using h2
    simpa [chainBlocks, List.append_assoc] using h1'.trans h2'

variable {r n : ℕ} [NeZero r]

theorem cellVertices_eq_chainBlocks (y : Cell r → ℕ) (first : Cell r) (rest : List (Cell r)) :
    connectorCellVertices y first rest = chainBlocks vertexBlock (fun a _ => [y a]) first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    rw [connectorCellVertices_cons, chainBlocks, ← ih next]
    rfl

theorem cellWord_eq_chainBlocks (y : Cell r → ℕ) (first : Cell r) (rest : List (Cell r)) :
    word cellA cellB canonicalSymbol
      (cellChain n (fun i : Cell r => predecessor i.1 i.2)
        (fun i => successor i.1 i.2) y first rest) =
      chainBlocks colorBlock
        (fun a b => [wrapOut n (y a) (successor a.1 a.2),
          wrapIn n (y a) (predecessor b.1 b.2)]) first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    simpa only [cellChain, word, Piece.gaps, chainBlocks, colorBlock, incoming, outgoing,
      List.flatMap_cons, List.cons_append, List.nil_append] using
      congrArg (fun xs => incoming first::outgoing first::
        wrapOut n (y first) (successor first.1 first.2)::
        wrapIn n (y first) (predecessor next.1 next.2)::xs) (ih next)

theorem edgeBlocks_eq_records (y : Cell r → ℕ) (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hmatch : ∀ t (ht : t < records.length), y records[t].previous = records[t].value)
    (K : Cell r → Cell r → ℕ → List ℕ) :
    (lexEdges r).flatMap (fun e => K e.1 e.2 (y e.1)) =
      records.flatMap (fun s => K s.previous s.next s.value) := by
  rw [← hmap, List.flatMap_map]
  apply List.flatMap_congr
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hs
  exact congrArg (K records[t].previous records[t].next) (hmatch t ht)

theorem connectorPrefixVertices_perm_pools (y : Cell r → ℕ) (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hmatch : ∀ t (ht : t < records.length), y records[t].previous = records[t].value) :
    (connectorPrefixVertices n y).Perm (fixedVertexList n r ++ records.map ConnectorRecord.value) := by
  have h := chainBlocks_perm vertexBlock (fun a _ => [y a]) (firstCell r) (lexCells r).tail
  rw [← lexCells_cons r] at h
  change (chainBlocks vertexBlock (fun a _ => [y a]) (firstCell r) (lexCells r).tail).Perm
    ((lexCells r).flatMap vertexBlock ++ (lexEdges r).flatMap (fun e => [y e.1])) at h
  have he := edgeBlocks_eq_records y records hmap hmatch (fun _ _ v => [v])
  change (lexEdges r).flatMap (fun e => [y e.1]) = records.flatMap (fun s => [s.value]) at he
  simp only [← List.map_eq_flatMap] at he h
  rw [he] at h
  change (startVertices n ++ connectorCellVertices y (firstCell r) (lexCells r).tail).Perm _
  rw [cellVertices_eq_chainBlocks]
  simpa only [fixedVertexList, List.append_assoc] using h.append_left (startVertices n)

theorem connectorPrefixPathGaps_perm_pools (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hmatch : ∀ t (ht : t < records.length), y records[t].previous = records[t].value) :
    (pathGaps (connectorPrefixPath n y)).Perm (fixedColorList n r ++ records.flatMap (recordColors n)) := by
  have h := chainBlocks_perm colorBlock
    (fun a b => [wrapOut n (y a) (successor a.1 a.2),
      wrapIn n (y a) (predecessor b.1 b.2)]) (firstCell r) (lexCells r).tail
  rw [← lexCells_cons r] at h
  change (chainBlocks colorBlock
      (fun a b => [wrapOut n (y a) (successor a.1 a.2),
        wrapIn n (y a) (predecessor b.1 b.2)]) (firstCell r) (lexCells r).tail).Perm
    ((lexCells r).flatMap colorBlock ++ (lexEdges r).flatMap
      (fun e => [wrapOut n (y e.1) (successor e.1.1 e.1.2),
        wrapIn n (y e.1) (predecessor e.2.1 e.2.2)])) at h
  have he := edgeBlocks_eq_records y records hmap hmatch
    (fun a b v => [wrapOut n v (successor a.1 a.2), wrapIn n v (predecessor b.1 b.2)])
  change _ = records.flatMap (recordColors n) at he
  rw [he] at h
  rw [connectorPrefixPath_pathGaps hr hn y hy]
  change ((startColors n++[firstJoin r]) ++
    word cellA cellB canonicalSymbol
      (cellChain n (fun i : Cell r => predecessor i.1 i.2)
        (fun i => successor i.1 i.2) y (firstCell r) (lexCells r).tail)).Perm _
  rw [cellWord_eq_chainBlocks]
  simpa only [fixedColorList, List.append_assoc] using h.append_left (startColors n++[firstJoin r])

theorem connectorPrefixVertices_nodup (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hfresh : ∀ t (ht : t < records.length),
      y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t]) :
    (connectorPrefixVertices n y).Nodup :=
  (connectorPrefixVertices_perm_pools y records hmap (fun t ht => (hfresh t ht).1)).nodup_iff.mpr
    (fixed_and_recordValues_nodup hr hn records (fun t ht => (hfresh t ht).2))

theorem connectorPrefixPath_rainbow (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (records : List (ConnectorRecord r))
    (hmap : records.map (fun s => (s.previous,s.next)) = lexEdges r)
    (hfresh : ∀ t (ht : t < records.length),
      y records[t].previous = records[t].value ∧ FreshRecord n (records.take t) records[t]) :
    (pathGaps (connectorPrefixPath n y)).Nodup :=
  (connectorPrefixPathGaps_perm_pools hr hn y hy records hmap (fun t ht => (hfresh t ht).1)).nodup_iff.mpr
    (fixed_and_recordColors_nodup hr hn records (fun t ht => (hfresh t ht).2))

end CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix
