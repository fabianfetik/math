import CorralFormalization.Results.SwitchFamily.Prefix.Completion

namespace CorralFormalization.Results.SwitchFamily.Prefix

open CorralFormalization.LatinCompletion.TerraceCompletion

/-- Every printed five-vertex block is a literal segment of the prefix. -/
theorem blockVertices_infix {n m i : ℕ} (hi : i < m) :
    blockVertices n i <:+: vertices n m := by
  obtain ⟨a,b,hab⟩ := List.mem_iff_append.mp (List.mem_range.mpr hi)
  rw [vertices_initial,hab,List.flatMap_append]
  simp only [List.flatMap_cons]
  exact ⟨CorralFormalization.LatinCompletion.GeneralTiles.explicitPrefix n ++
    a.flatMap (blockVertices n), b.flatMap (blockVertices n), by simp [List.append_assoc]⟩

/-- The literal A3 segment survives in the completed terrace. -/
theorem blockVertices_in_terrace {n m i : ℕ} (D : DirectedTerrace n)
    (hD : PrescribedTerrace m D) (hi : i < m) :
    blockVertices n i <:+: List.ofFn (fun k : Fin (n-1) => (D.vertices k).val) :=
  (blockVertices_infix hi).trans hD.2.1.isInfix

/-- A4 likewise occurs as an actual consecutive calendar segment. -/
theorem blockColors_infix {n m i : ℕ} (hi : i < m) :
    blockColors n i <:+: colors n m := by
  obtain ⟨a,b,hab⟩ := List.mem_iff_append.mp (List.mem_range.mpr hi)
  rw [colors,hab,List.flatMap_append]
  simp only [List.flatMap_cons]
  exact ⟨CorralFormalization.LatinCompletion.GeneralTiles.explicitGapPrefix n ++
    a.flatMap (blockColors n), b.flatMap (blockColors n), by simp [List.append_assoc]⟩

theorem blockColors_in_terrace {n m i : ℕ} (D : DirectedTerrace n)
    (hD : PrescribedTerrace m D) (hi : i < m) : blockColors n i <:+: D.word :=
  (blockColors_infix hi).trans hD.2.2.1.isInfix

def supportColors (i : ℕ) : List ℕ := [alpha i,alpha i+1,beta i+1,beta i]

theorem supportColors_nodup (i : ℕ) : (supportColors i).Nodup := by
  have hba := beta_alpha i
  simp [supportColors,List.nodup_cons]
  omega

theorem supportColors_disjoint {i j : ℕ} (hij : i ≠ j) :
    List.Disjoint (supportColors i) (supportColors j) := by
  rw [List.disjoint_left]
  intro d hd he
  have hp := parity_lt i
  have hp' := parity_lt j
  simp only [supportColors,List.mem_cons,List.not_mem_nil,or_false] at hd he
  dsimp [alpha,beta] at *
  omega

theorem supportColors_bounds {n m i d : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (hi : i < m) (hd : d ∈ supportColors i) :
    20 ≤ d ∧ d < n := by
  have hsep := color_separation hn hsize hi
  simp only [supportColors,List.mem_cons,List.not_mem_nil,or_false] at hd
  omega

def movingNaturals (i : ℕ) : List ℕ := [center i,center i+1]

def fixedNaturals (i : ℕ) : List ℕ :=
  [predecessorNatural i,center i+alpha i+1,backward i,ending i]

private theorem moving_mem_block {i x : ℕ} (hx : x ∈ movingNaturals i) :
    x ∈ blockNaturals i := by
  simp only [movingNaturals,List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [blockNaturals,List.mem_cons,List.not_mem_nil,or_false]
  omega

private theorem moving_avoid_block_fixed {i j x y : ℕ}
    (hx : x ∈ movingNaturals i)
    (hy : y ∈ [center j+alpha j+1,backward j,ending j]) : x ≠ y := by
  by_cases hij : i=j
  · subst j
    have ha : 20 ≤ alpha i := by dsimp [alpha]; omega
    have hb := beta_alpha i
    have hbc := backward_add_beta i
    simp only [movingNaturals,List.mem_cons,List.not_mem_nil,or_false] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    simp only [ending] at hy
    omega
  · have hx' := moving_mem_block hx
    have hy' : y ∈ blockNaturals j := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      simp only [blockNaturals,List.mem_cons,List.not_mem_nil,or_false]
      omega
    have hdis : List.Disjoint (blockNaturals i) (blockNaturals j) := by
      rcases lt_or_gt_of_ne hij with hij|hji
      · exact blocks_disjoint hij
      · exact (blocks_disjoint hji).symm
    intro hxy
    exact (List.disjoint_left.mp hdis) hx' (hxy ▸ hy')

/-- No center moved by any switch can be a fixed neighbor of any other
switch, including adjacent blocks sharing an endpoint. -/
theorem moving_centers_avoid_fixed_neighbors (i j : ℕ) :
    List.Disjoint (movingNaturals i) (fixedNaturals j) := by
  rw [List.disjoint_left]
  intro x hx hy
  simp only [fixedNaturals,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with hy|hy
  · subst x
    cases j with
    | zero =>
      have hc : 38 ≤ center i := by
        dsimp [center]
        nlinarith [Nat.zero_le (i/2),Nat.zero_le (i^2)]
      norm_num [predecessorNatural,center,alpha] at hx
      simp only [movingNaturals,List.mem_cons,List.not_mem_nil,or_false] at hx
      omega
    | succ j =>
      rw [predecessorNatural_succ] at hx
      exact (moving_avoid_block_fixed (j:=j) hx
        (by simp : ending j ∈ [center j+alpha j+1,backward j,ending j])) rfl
  · exact (moving_avoid_block_fixed (j:=j) hx
      (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hy)) rfl

private theorem block_mem_naturals {n m i x : ℕ} (hi : i < m)
    (hx : x ∈ blockNaturals i) : x ∈ naturals n m := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hx⟩

private theorem fixed_mem_naturals {n m i x : ℕ} (hi : i < m)
    (hx : x ∈ fixedNaturals i) : x ∈ naturals n m := by
  simp only [fixedNaturals,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|hx
  · cases i with
    | zero =>
      apply List.mem_append_left
      simp [initialNaturals,predecessorNatural,center,alpha]
    | succ i =>
      rw [predecessorNatural_succ]
      apply block_mem_naturals (i:=i) (by omega)
      simp [blockNaturals]
  · apply block_mem_naturals hi
    simp only [blockNaturals,List.mem_cons,List.not_mem_nil,or_false]
    omega

/-- The same noninterference holds for actual residues, since all printed
representatives have been proved strictly between zero and n. -/
theorem moving_vertices_avoid_fixed_neighbors {n m i j : ℕ} [NeZero n]
    (hn : 65 ≤ n) (hsize : (5*m+8)^2 ≤ n) (hi : i < m) (hj : j < m) :
    List.Disjoint ((movingNaturals i).map (Nat.cast : ℕ → ZMod n))
      ((fixedNaturals j).map (Nat.cast : ℕ → ZMod n)) := by
  rw [List.disjoint_left]
  intro z hz hz'
  obtain ⟨a,ha,haz⟩ := List.mem_map.mp hz
  obtain ⟨b,hb,hbz⟩ := List.mem_map.mp hz'
  have hla := natural_values hn hsize (block_mem_naturals hi (moving_mem_block ha))
  have hlb := natural_values hn hsize (fixed_mem_naturals hj hb)
  have hval := congrArg ZMod.val (haz.trans hbz.symm)
  have hab : a=b := by
    simpa only [ZMod.val_natCast_of_lt hla.2,ZMod.val_natCast_of_lt hlb.2] using hval
  subst b
  exact (List.disjoint_left.mp (moving_centers_avoid_fixed_neighbors i j)) ha hb

end CorralFormalization.Results.SwitchFamily.Prefix
