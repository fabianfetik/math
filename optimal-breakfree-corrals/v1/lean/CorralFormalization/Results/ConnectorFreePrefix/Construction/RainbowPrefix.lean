import CorralFormalization.Results.ConnectorFreePrefix.Construction.VertexAndCenterColors
import CorralFormalization.Results.ConnectorFreePrefix.Construction.JoinPool
import CorralFormalization.DiversityCompletion.LatinConnectorInterleave
import CorralFormalization.DiversityCompletion.EndpointPathSupplier

/-!
# A genuine connector-free RainbowPrefix

This file assembles the explicit eight markers, all `3*r*r` array vertices,
and the actual directed clock colours. Its construction uses no endpoint
completion, terrace, corral, or assumed rainbow-prefix supplier.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply LatinPrefixSupply.ConnectorGreedy

variable {r n : ℕ} [NeZero r]

def initialColors (n r : ℕ) : List ℕ := FixedConnectorPrefix.startColors n++[10*r*r-18]

def prefixColorPools (n r : ℕ) [NeZero r] : List ℕ :=
  (initialColors n r++(lexCells r).flatMap centerColorBlock)++
    (lexEdges r).map (fun e => directGap n e.1 e.2)

theorem directChain_word_chainBlocks (n : ℕ) (first : Cell r) (rest : List (Cell r)) :
    word prefixA prefixB canonicalSymbol (directChain n first rest)=
      FixedConnectorPrefix.chainBlocks centerColorBlock (fun i k => [directGap n i k]) first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    simpa only [directChain,word,Piece.gaps,FixedConnectorPrefix.chainBlocks,centerColorBlock,
      prefixIncoming,prefixOutgoing,List.flatMap_cons,List.cons_append,List.nil_append] using
      congrArg (fun xs=>prefixIncoming first::prefixOutgoing first::directGap n first next::xs) (ih next)

/-- The literal gap sequence is a permutation of the proved-disjoint actual
marker, centre-edge, and direct-join colour pools. -/
theorem prefixPathGaps_perm_pools (hr : 3 ≤ r) (hn : 200*r*r≤n) :
    (pathGaps (prefixPath n r)).Perm (prefixColorPools n r) := by
  have h := FixedConnectorPrefix.chainBlocks_perm centerColorBlock
    (fun i k => [directGap n i k]) (firstCell r) (lexCells r).tail
  rw [←lexCells_cons r] at h
  change (FixedConnectorPrefix.chainBlocks centerColorBlock
    (fun i k => [directGap n i k]) (firstCell r) (lexCells r).tail).Perm
      ((lexCells r).flatMap centerColorBlock++
        (lexEdges r).flatMap (fun e=>[directGap n e.1 e.2])) at h
  simp only [←List.map_eq_flatMap] at h
  rw [prefixPath_pathGaps hr hn]
  change (initialColors n r++word prefixA prefixB canonicalSymbol
      (directChain n (firstCell r) (lexCells r).tail)).Perm _
  rw [directChain_word_chainBlocks]
  simpa only [prefixColorPools,List.append_assoc] using h.append_left (initialColors n r)

theorem initialColors_nodup (hr : 3 ≤ r) (hn : 200*r*r≤n) :
    (initialColors n r).Nodup := by
  have hr2 : 2≤r := by omega
  have hn2 : 100*r*r≤n := by nlinarith
  unfold initialColors
  rw [←FixedConnectorPrefix.firstJoin_eq]
  apply (FixedConnectorPrefix.startColors_nodup hr2 hn2).append (by simp)
  intro d hd hj
  have he : d=FixedConnectorPrefix.firstJoin r := by simpa using hj
  exact FixedConnectorPrefix.firstJoin_not_mem_startColors hr2 hn2 (he ▸ hd)

theorem centerColorBlock_bounds (hr : 3 ≤ r) (i : Cell r) (d : ℕ) (hd : d ∈ centerColorBlock i) :
    10*r*r≤d ∧ d≤51*r*r := by
  have hb := prefix_center_color_bands hr i
  simp only [centerColorBlock,List.mem_cons,List.mem_nil_iff,or_false] at hd
  rcases hd with rfl|rfl <;> constructor <;> nlinarith

theorem centerColorBlock_avoids_initial (hr : 3 ≤ r) (hn : 200*r*r≤n)
    (i : Cell r) (d : ℕ) (hd : d ∈ centerColorBlock i) : d ∉ initialColors n r := by
  have hb := centerColorBlock_bounds hr i d hd
  have hR : 9≤r*r := by nlinarith
  have hn14 : 14≤n := by nlinarith
  have hsub := Nat.sub_add_cancel hn14
  have hlo : 12<d := by nlinarith
  have hhi : d<n-14 := by nlinarith
  have hstart := FixedConnectorPrefix.not_mem_startColors hlo hhi
  have hfirst := FixedConnectorPrefix.firstJoin_range (r:=r) (by omega : 2≤r) (by nlinarith : 100*r*r≤n)
  rw [FixedConnectorPrefix.firstJoin_eq] at hfirst
  intro h
  rcases List.mem_append.mp h with hm|hm
  · exact hstart hm
  · have he : d=10*r*r-18 := by simpa using hm
    omega

theorem join_avoids_front_pools (hr : 3 ≤ r) (hn : 200*r*r≤n)
    {e : Cell r×Cell r} (he : e ∈ lexEdges r) :
    directGap n e.1 e.2 ∉ initialColors n r++(lexCells r).flatMap centerColorBlock := by
  have hs := directColor_separation hr hn _ (directGap_bounds hr hn he)
  have hbig : 51*r*r<directGap n e.1 e.2 := by exact_mod_cast hs.1
  have hsmall : directGap n e.1 e.2<n-14 := by omega
  have hR : 9≤r*r := by nlinarith
  have h12 : 12<directGap n e.1 e.2 := by nlinarith
  have hstart := FixedConnectorPrefix.not_mem_startColors h12 hsmall
  have hfirst := FixedConnectorPrefix.firstJoin_range (r:=r) (by omega : 2≤r) (by nlinarith : 100*r*r≤n)
  rw [FixedConnectorPrefix.firstJoin_eq] at hfirst
  intro h
  rcases List.mem_append.mp h with hi|hc
  · rcases List.mem_append.mp hi with hm|hm
    · exact hstart hm
    · have heq : directGap n e.1 e.2=10*r*r-18 := by simpa using hm
      nlinarith
  · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hc
    have hb := centerColorBlock_bounds hr i _ hi
    omega

theorem prefixColorPools_nodup (hr : 3 ≤ r) (hn : 200*r*r≤n) :
    (prefixColorPools n r).Nodup := by
  have hcells : (lexCells r).Nodup := (lexCells_perm r).nodup_iff.mpr (Finset.nodup_toList _)
  have hfront : (initialColors n r++(lexCells r).flatMap centerColorBlock).Nodup := by
    apply (initialColors_nodup hr hn).append (centerColors_nodup hr _ hcells)
    intro d hd hc
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hc
    exact centerColorBlock_avoids_initial hr hn i d hi hd
  apply hfront.append (directGap_pool_nodup hr hn)
  intro d hd hj
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hj
  exact join_avoids_front_pools hr hn he hd

/-- The actual physical directed gap list is rainbow. -/
theorem prefixPath_rainbow (hr : 3 ≤ r) (hn : 200*r*r≤n) :
    (pathGaps (prefixPath n r)).Nodup :=
  (prefixPathGaps_perm_pools hr hn).nodup_iff.mpr (prefixColorPools_nodup hr hn)

theorem initialColors_range (hr : 3 ≤ r) (hn : 200*r*r≤n)
    (d : ℕ) (hd : d ∈ initialColors n r) : 0<d ∧ d<n := by
  have hR : 9≤r*r := by nlinarith
  have hlarge : 1800≤n := by nlinarith
  rcases List.mem_append.mp hd with hm|hm
  · simp only [FixedConnectorPrefix.startColors,List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> omega
  · have heq : d=10*r*r-18 := by simpa using hm
    have hfirst := FixedConnectorPrefix.firstJoin_range (r:=r) (by omega : 2≤r) (by nlinarith : 100*r*r≤n)
    rw [FixedConnectorPrefix.firstJoin_eq] at hfirst
    omega

theorem prefixPath_colors (hr : 3 ≤ r) (hn : 200*r*r≤n)
    (d : ℕ) (hd : d ∈ pathGaps (prefixPath n r)) : 0<d ∧ d<n := by
  have hp := (prefixPathGaps_perm_pools hr hn).mem_iff.mp hd
  rcases List.mem_append.mp hp with hfront|hj
  · rcases List.mem_append.mp hfront with hi|hc
    · exact initialColors_range hr hn d hi
    · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hc
      have hb := centerColorBlock_bounds hr i d hi
      have hR : 9≤r*r := by nlinarith
      constructor <;> nlinarith
  · obtain ⟨e,_,rfl⟩ := List.mem_map.mp hj
    exact ⟨(directGap_geometry hr hn e.1 e.2).1,(directGap_geometry hr hn e.1 e.2).2.1⟩

/-- A decomposition of the actual prefix for the endpoint/interface structure.
The terminal vertex is read from this concrete path itself. -/
theorem prefixPath_decomposition (n r : ℕ) [NeZero r] :
    ∃ (last : ZMod n) (interior : List (ZMod n)),
      prefixPath n r=(((n-3:ℕ):ZMod n)::interior)++[last] := by
  have hlen := prefixPath_length n r
  have hnon : prefixPath n r≠[] := by intro h; rw [h] at hlen; simp at hlen
  obtain ⟨initialPart,hpart⟩ := List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast hnon)
  cases initialPart with
  | nil =>
    rw [hpart] at hlen
    simp only [List.nil_append,List.length_cons,List.length_nil] at hlen
    omega
  | cons first interior =>
    have hhead : (prefixPath n r).head?=some ((n-3:ℕ):ZMod n) := rfl
    rw [hpart] at hhead
    have hf : first=((n-3:ℕ):ZMod n) := by simpa using hhead
    rw [hf] at hpart
    exact ⟨_,interior,hpart⟩

/-- The explicit connector-free prefix exists for the literal manuscript
regime; the proof in fact does not need the parity of `n`.
It has the eight markers and exactly `3*r*r+8` vertices. -/
theorem rainbowPrefix_exists (hr : 3 ≤ r) (hn : 200*r*r≤n) :
    ∃ P : RainbowPrefix n, P.path=prefixPath n r ∧
      P.first=((n-3:ℕ):ZMod n) ∧ P.path.length=3*r*r+8 ∧
      pathGaps P.path=[2,3,10,n-14,12]++prefixGaps n r := by
  obtain ⟨last,interior,hdec⟩ := prefixPath_decomposition n r
  let P : RainbowPrefix n := {
    first := ((n-3:ℕ):ZMod n)
    last := last
    interior := interior
    simple := by rw [←hdec]; exact prefixPath_nodup hr hn
    nonzero := by intro z hz; rw [←hdec] at hz; exact prefixPath_nonzero hr hn z hz
    rainbow := by rw [←hdec]; exact prefixPath_rainbow hr hn
    colors := by intro d hd; rw [←hdec] at hd; exact prefixPath_colors hr hn d hd
  }
  have hpath : P.path=prefixPath n r := hdec.symm
  exact ⟨P,hpath,rfl,hpath ▸ prefixPath_length n r,by rw [hpath]; exact prefixPath_pathGaps hr hn⟩

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction
