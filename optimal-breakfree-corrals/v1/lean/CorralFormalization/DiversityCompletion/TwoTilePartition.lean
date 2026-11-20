import CorralFormalization.DiversityCompletion.TerraceLift

namespace CorralFormalization.LatinCompletion.TerraceLift.CompletedTerrace

open LatinTransfer DiversitySymmetry

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

theorem tileRow_append (o : ZMod (h*n)) (g k : List ℕ) :
    TileGapWords.row o (g++k) = TileGapWords.row o g ∪
      TileGapWords.row (o+(g.sum : ZMod (h*n))) k := by
  ext x
  simp only [TileGapWords.row, physicalOffsets, prefix_append, Finset.mem_image,
    List.mem_toFinset, List.mem_append, List.mem_map, Finset.mem_union,
    Nat.cast_add, ZMod.natCast_zmod_val]
  constructor
  · rintro ⟨a,ha,he⟩
    rcases ha with ha | ⟨b,hb,hab⟩
    · exact Or.inl ⟨a,ha,he⟩
    · refine Or.inr ⟨b,hb,?_⟩
      subst a
      simpa only [Nat.cast_add, add_assoc] using he
  · rintro (⟨a,ha,he⟩ | ⟨b,hb,he⟩)
    · exact ⟨a,Or.inl ha,he⟩
    · refine ⟨g.sum+b,Or.inr ⟨b,hb,rfl⟩,?_⟩
      simpa only [Nat.cast_add,add_assoc] using he

theorem tileRow_singleton (o : ZMod (h*n)) (d : ℕ) :
    TileGapWords.row o [d] = {o} := by
  simp [TileGapWords.row, physicalOffsets, properPrefixSites]

theorem tileRow_three (o : ZMod (h*n)) (a b c : ℕ) :
    TileGapWords.row o [a,b,c] = {o,o+(a : ZMod (h*n)),o+(a : ZMod (h*n))+(b : ZMod (h*n))} := by
  simp [TileGapWords.row, physicalOffsets, properPrefixSites, Nat.cast_add, add_assoc]

theorem roundSites_row (T : CompletedTerrace n) (q : ZMod h) :
    T.roundSites q = TileGapWords.row (zeroSite h n q + ((n-1 : ℕ) : ZMod (h*n)))
      (TileGapWords.cycle n T.body) := by
  rw [T.roundSites_physicalPrefixes, TileGapWords.row]
  symm
  apply physicalOffsets_origin
  simp only [zeroSite, Nat.cast_add]

def twoRemainder (T : CompletedTerrace n) (q : ZMod h) : Finset (ZMod (h*n)) :=
  TileGapWords.row (zeroSite h n q+2) (TileGapWords.middle n T.body ++ [2])

theorem cycle_head (T : CompletedTerrace n) :
    TileGapWords.cycle n T.body = [3] ++ (TileGapWords.middle n T.body ++ [2]) := by
  simp [TileGapWords.cycle, TileGapWords.middle, List.append_assoc]

theorem round_pred_decomposition (T : CompletedTerrace n) (q : ZMod h) :
    T.roundSites (q-1) = {zeroSite h n q-1} ∪ T.twoRemainder q := by
  have hs : zeroSite h n (q-1)+((n-1 : ℕ) : ZMod (h*n)) = zeroSite h n q-1 := by
    rw [zeroSite_pred, Nat.cast_sub (by have := NeZero.pos n; omega : 1 ≤ n), Nat.cast_one]
    ring
  have hshift : zeroSite h n (q-1)+((n-1 : ℕ) : ZMod (h*n))+(3 : ZMod (h*n)) =
      zeroSite h n q+2 := by rw [hs]; ring
  have hshift' : zeroSite h n q-1+(3 : ZMod (h*n)) = zeroSite h n q+2 := by ring
  rw [T.roundSites_row, T.cycle_head, tileRow_append, tileRow_singleton]
  simpa only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.cast_ofNat, hs, hshift',twoRemainder]

theorem twoSecond_decomposition (T : CompletedTerrace n) (hn : n=2*h-1) (q : ZMod h) :
    TileGapWords.row (zeroSite h n q+2) (TileGapWords.twoSecond n T.body) =
      T.twoRemainder q ∪ {zeroSite h n (q-1),zeroSite h n q} := by
  have hm : (TileGapWords.middle n T.body).sum+5 = (TileGapWords.cycle n T.body).sum := by
    simp [TileGapWords.middle, TileGapWords.cycle]
    omega
  have hmc := congrArg (fun t : ℕ => (t : ZMod (h*n))) hm
  simp only [Nat.cast_add, Nat.cast_ofNat] at hmc
  have hc := T.round_displacement hn
  have h₁ : zeroSite h n q+2+((TileGapWords.middle n T.body).sum : ZMod (h*n))+3 =
      zeroSite h n (q-1) := by
    rw [zeroSite_pred]
    linear_combination hmc + hc
  have h₂ : zeroSite h n q+2+((TileGapWords.middle n T.body).sum : ZMod (h*n))+3+
      (n : ZMod (h*n)) = zeroSite h n q := by linear_combination hmc + hc
  rw [TileGapWords.twoSecond, tileRow_append, tileRow_three]
  unfold twoRemainder
  rw [tileRow_append, tileRow_singleton]
  simp only [Nat.cast_ofNat]
  rw [h₂,h₁]
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem prefix_card_sum_le (o : ZMod (h*n)) (g : List ℕ)
    (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum ≤ h*n) :
    (TileGapWords.row o g).card = g.length := by
  rw [TileGapWords.row, physicalOffsets_card, properPrefixSites_length]
  · exact (properPrefixSites_strict g hpos).imp (by intro a b hab; omega)
  · intro p hp
    exact lt_of_lt_of_le (properPrefixSites_lt_sum g hpos p hp) hsum

theorem twoRemainder_card (T : CompletedTerrace n) (hn : n=2*h-1) (q : ZMod h) :
    (T.twoRemainder q).card = n-2 := by
  let g := TileGapWords.middle n T.body ++ [2]
  have hg : TileGapWords.cycle n T.body = [3]++g := T.cycle_head
  have hpos : ∀ x ∈ g, 0 < x := by
    intro x hx
    have hxc : x ∈ TileGapWords.cycle n T.body := by rw [hg]; simp [hx]
    exact ((fullGapList_mem (n-1) x).mp (T.differences.mem_iff.mp hxc)).1
  have hlen : g.length = n-2 := by
    have hl := T.differences.length_eq
    rw [hg] at hl
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    simp only [fullGapList, List.length_map, List.length_range] at hl
    omega
  have hsum : g.sum ≤ h*n := by
    have hf := TileGapWords.first_perm (NeZero.pos n) T.body T.differences
    have hs := (TileGapWords.word_properties hn (NeZero.pos h) _ hf).2.1
    rw [TileGapWords.first,hg] at hs
    simp only [List.sum_append,List.sum_cons,List.sum_nil] at hs
    omega
  exact (prefix_card_sum_le (zeroSite h n q+2) g hpos hsum).trans hlen

theorem boundary_not_mem_remainder (T : CompletedTerrace n) (hn : n=2*h-1)
    (hsmall : 15 ≤ n) (q : ZMod h) : zeroSite h n q-1 ∉ T.twoRemainder q := by
  intro hx
  have hc := T.roundSites_card (q-1)
  rw [T.round_pred_decomposition] at hc
  simp only [Finset.singleton_union, Finset.insert_eq_of_mem hx] at hc
  rw [T.twoRemainder_card hn q] at hc
  omega

theorem remainder_subset_round (T : CompletedTerrace n) (q : ZMod h) :
    T.twoRemainder q ⊆ T.roundSites (q-1) := by
  rw [T.round_pred_decomposition]
  exact Finset.subset_union_right

theorem zero_not_mem_round (T : CompletedTerrace n) (p q : ZMod h) :
    zeroSite h n p ∉ T.roundSites q := by
  intro hp
  obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hp
  have hv := congrArg (residueMap h n) ht
  rw [T.site_residue,zeroSite_residue] at hv
  exact (T.vertices t).property hv

theorem phase_ne_pred (hn : n=2*h-1) (hsmall : 15 ≤ n) (q : ZMod h) : q ≠ q-1 := by
  intro he
  have hone : (1 : ZMod h) = 0 := by linear_combination he
  have hv := congrArg ZMod.val hone
  rw [ZMod.val_one'' (by omega : h ≠ 1),ZMod.val_zero] at hv
  omega

/-- The two actual gapword rows are disjoint and cover precisely two full
terrace rounds plus their two zero-column sites. No physical partition of
the tile is assumed. -/
theorem two_tile_partition (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    (q : ZMod h) :
    Disjoint
      (TileGapWords.row (zeroSite h n q+((n-1 : ℕ) : ZMod (h*n))) (TileGapWords.first n T.body))
      (TileGapWords.row (zeroSite h n q+2) (TileGapWords.twoSecond n T.body)) ∧
    TileGapWords.row (zeroSite h n q+((n-1 : ℕ) : ZMod (h*n))) (TileGapWords.first n T.body) ∪
      TileGapWords.row (zeroSite h n q+2) (TileGapWords.twoSecond n T.body) =
      T.roundSites q ∪ T.roundSites (q-1) ∪ {zeroSite h n (q-1),zeroSite h n q} := by
  rw [T.first_tile_row_eq_round hn,T.twoSecond_decomposition hn]
  have hb : zeroSite h n q-1 ∈ T.roundSites (q-1) := by
    rw [T.round_pred_decomposition]
    simp
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hround : x ∈ T.roundSites q ∨ x ∈ T.roundSites (q-1) := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Or.inl hx
      · have he := Finset.mem_singleton.mp hx
        exact Or.inr (he ▸ hb)
    rcases Finset.mem_union.mp hy with hr | hz
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.disjoint_left.mp (T.roundSites_disjoint (phase_ne_pred hn hsmall q))
          hx (T.remainder_subset_round q hr)
      · have he := Finset.mem_singleton.mp hx
        exact T.boundary_not_mem_remainder hn hsmall q (he ▸ hr)
    · rcases Finset.mem_insert.mp hz with he | hz
      · subst x
        rcases hround with ha | ha <;> exact T.zero_not_mem_round _ _ ha
      · have he := Finset.mem_singleton.mp hz
        subst x
        rcases hround with ha | ha <;> exact T.zero_not_mem_round _ _ ha
  · rw [T.round_pred_decomposition]
    ext x
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert]
    tauto

end CorralFormalization.LatinCompletion.TerraceLift.CompletedTerrace
