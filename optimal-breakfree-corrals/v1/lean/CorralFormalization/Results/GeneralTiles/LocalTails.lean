import CorralFormalization.Results.GeneralTiles.CyclicTiling

/-!
# Exact gap-two and gap-one tails of the literal rows

Gap-n tails were already derived in `TileGapWords.tile_tails`. Here the
remaining distinguished tails are derived from the actual positive gap
words, rather than supplied as marker certificates.
-/

namespace CorralFormalization.LatinCompletion.GeneralTiles

open LatinTransfer DiversitySymmetry TerraceLift

namespace LocalTails

theorem body_avoids_two {n : ℕ} (body : List ℕ)
    (hp : (TileGapWords.cycle n body).Perm (fullGapList (n-1))) :
    ∀ x ∈ body, x ≠ 2 := by
  have hnd : (([3,10,n-14,12]++body)++[2]).Nodup :=
    hp.nodup_iff.mpr (fullGapList_nodup (n-1))
  have hd := (List.nodup_append'.mp hnd).2.2
  intro x hx he
  subst x
  exact List.disjoint_left.mp hd (List.mem_append_right _ hx) (by simp)

theorem gap_two_offsets {n : ℕ} (hsmall : 65 ≤ n) (body : List ℕ)
    (hp : (TileGapWords.cycle n body).Perm (fullGapList (n-1))) :
    gapOffsets 2 (TileGapWords.first n body) = [(TileGapWords.middle n body).sum+3] ∧
    gapOffsets 2 (TileGapWords.twoSecond n body) = [(TileGapWords.middle n body).sum+3+n] ∧
    gapOffsets 2 (TileGapWords.threeSecond n body) = [(TileGapWords.middle n body).sum] ∧
    gapOffsets 2 (TileGapWords.threeThird n body) = [n-14] := by
  have hbody := body_avoids_two body hp
  have hmiddle : ∀ x ∈ TileGapWords.middle n body, x ≠ 2 := by
    intro x hx
    simp only [TileGapWords.middle,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false] at hx
    rcases hx with (rfl | rfl | rfl) | hx <;> try omega
    exact hbody x hx
  have hm := TileGapWords.gapOffsets_eq_nil 2 _ hmiddle
  have hb := TileGapWords.gapOffsets_eq_nil 2 _ hbody
  have hc : TileGapWords.cycle n body = [3]++TileGapWords.middle n body++[2] := by
    simp [TileGapWords.cycle,TileGapWords.middle]
  have hn2 : n ≠ 2 := by omega
  have ha2 : n-14 ≠ 2 := by omega
  simp [TileGapWords.first,TileGapWords.twoSecond,TileGapWords.threeSecond,
    TileGapWords.threeThird,TileGapWords.thirdPrefix,hc,
    TileGapWords.gapOffsets_append,gapOffsets,hm,hb,hn2,ha2,Nat.add_comm,Nat.add_assoc]

/-- A singleton offset calculation for any distinguished gap, with the
actual physical adjacency and closing wrap supplied by positive winding. -/
theorem row_tail {h n : ℕ} [NeZero (h*n)] (hn : n=2*h-1) (hsmall : 65 ≤ n)
    (origin : ZMod (h*n)) (w : List ℕ) (hp : w.Perm (fullGapList n))
    (d k : ℕ) (hk : gapOffsets d w = [k]) :
    gapTails (TileGapWords.row origin w) d = {origin+(k : ZMod (h*n))} := by
  obtain ⟨hpos,hsum,hlen⟩ := TileGapWords.word_properties hn (by omega) w hp
  rw [TileGapWords.row,gapTails_physicalOffsets _ _ hpos hsum (by omega) d,hk]
  simp [physicalOffsets,Nat.cast_add]

/-- The literal gap-two tail of each of the four physical row roles.
Together with the existing gap-n formula this proves every listed local
tail of lengths two and n in Lemma 11. -/
theorem gap_two_tails {h n : ℕ} [NeZero (h*n)] (hn : n=2*h-1) (hsmall : 65 ≤ n)
    (body : List ℕ) (hp : (TileGapWords.cycle n body).Perm (fullGapList (n-1)))
    (z : ZMod (h*n)) :
    gapTails (TileGapWords.row (z+((n-1 : ℕ) : ZMod (h*n))) (TileGapWords.first n body)) 2 =
      {z-3} ∧
    gapTails (TileGapWords.row (z+2) (TileGapWords.twoSecond n body)) 2 = {z} ∧
    gapTails (TileGapWords.row (z+2) (TileGapWords.threeSecond n body)) 2 =
      {z-(n : ZMod (h*n))-3} ∧
    gapTails (TileGapWords.row (z-(n : ZMod (h*n))+12) (TileGapWords.threeThird n body)) 2 =
      {z-2} := by
  have hf := TileGapWords.first_perm (by omega : 0<n) body hp
  have hs : (TileGapWords.cycle n body).sum+n=h*n := by
    simpa [TileGapWords.first] using
      (TileGapWords.word_properties hn (by omega) (TileGapWords.first n body) hf).2.1
  have hm : (TileGapWords.middle n body).sum+5=(TileGapWords.cycle n body).sum := by
    simp [TileGapWords.middle,TileGapWords.cycle]
    omega
  have hsc := congrArg (fun k : ℕ => (k : ZMod (h*n))) hs
  have hmc := congrArg (fun k : ℕ => (k : ZMod (h*n))) hm
  simp only [Nat.cast_add,Nat.cast_ofNat,ZMod.natCast_self] at hsc hmc
  have hsub : ((n-1 : ℕ) : ZMod (h*n))=(n : ZMod (h*n))-1 := by
    rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  have hsub14 : ((n-14 : ℕ) : ZMod (h*n))=(n : ZMod (h*n))-14 := by
    rw [Nat.cast_sub (by omega : 14≤n),Nat.cast_ofNat]
  obtain ⟨h₁,h₂,h₃,h₄⟩ := gap_two_offsets hsmall body hp
  refine ⟨?_,?_,?_,?_⟩
  · rw [row_tail hn hsmall _ _ hf _ _ h₁,hsub]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    congr 1
    linear_combination hsc+hmc
  · rw [row_tail hn hsmall _ _ ((TileGapWords.twoSecond_perm_first n body).trans hf) _ _ h₂]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    congr 1
    linear_combination hsc+hmc
  · rw [row_tail hn hsmall _ _ ((TileGapWords.threeSecond_perm_first n body).trans hf) _ _ h₃]
    congr 1
    linear_combination hsc+hmc
  · rw [row_tail hn hsmall _ _ ((TileGapWords.threeThird_perm_first n body).trans hf) _ _ h₄,hsub14]
    congr 1
    ring

theorem gap_one_offsets {n : ℕ} (hsmall : 65 ≤ n) (rest : List ℕ)
    (hp : (TileGapWords.cycle n ([7,1]++rest)).Perm (fullGapList (n-1))) :
    gapOffsets 1 (TileGapWords.first n ([7,1]++rest)) = [n+18] ∧
    gapOffsets 1 (TileGapWords.twoSecond n ([7,1]++rest)) = [n+15] ∧
    gapOffsets 1 (TileGapWords.threeSecond n ([7,1]++rest)) = [n+15] ∧
    gapOffsets 1 (TileGapWords.threeThird n ([7,1]++rest)) = [n+5] := by
  have hnd := hp.nodup_iff.mpr (fullGapList_nodup (n-1))
  have hbody : (7::1::rest).Nodup :=
    (List.Nodup.of_append_right (List.Nodup.of_append_left hnd))
  have hr : 1 ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hbody).2).1
  have hrest : ∀ x ∈ rest, x ≠ 1 := by
    intro x hx he
    exact hr (he ▸ hx)
  have ho := TileGapWords.gapOffsets_eq_nil 1 rest hrest
  have h14 : n-14 ≠ 1 := by omega
  have hn1 : n ≠ 1 := by omega
  have h₃ : n-14+19=n+5 := by omega
  simp [TileGapWords.first,TileGapWords.cycle,TileGapWords.twoSecond,
    TileGapWords.middle,TileGapWords.threeSecond,TileGapWords.threeThird,
    TileGapWords.thirdPrefix,TileGapWords.gapOffsets_append,gapOffsets,
    ho,h14,hn1,h₃]
  omega

/-- The prescribed `10,17,18` vertices mean exactly that the body begins
with positive differences `7,1`. No subsequent vertex or gap is fixed. -/
theorem gap_one_tails {h n : ℕ} [NeZero (h*n)] (hn : n=2*h-1) (hsmall : 65 ≤ n)
    (rest : List ℕ)
    (hp : (TileGapWords.cycle n ([7,1]++rest)).Perm (fullGapList (n-1)))
    (z : ZMod (h*n)) :
    gapTails (TileGapWords.row (z+((n-1 : ℕ) : ZMod (h*n)))
      (TileGapWords.first n ([7,1]++rest))) 1 = {z+2*(n : ZMod (h*n))+17} ∧
    gapTails (TileGapWords.row (z+2) (TileGapWords.twoSecond n ([7,1]++rest))) 1 =
      {z+(n : ZMod (h*n))+17} ∧
    gapTails (TileGapWords.row (z+2) (TileGapWords.threeSecond n ([7,1]++rest))) 1 =
      {z+(n : ZMod (h*n))+17} ∧
    gapTails (TileGapWords.row (z-(n : ZMod (h*n))+12)
      (TileGapWords.threeThird n ([7,1]++rest))) 1 = {z+17} := by
  have hf := TileGapWords.first_perm (by omega : 0<n) ([7,1]++rest) hp
  have hsub : ((n-1 : ℕ) : ZMod (h*n))=(n : ZMod (h*n))-1 := by
    rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  obtain ⟨h₁,h₂,h₃,h₄⟩ := gap_one_offsets hsmall rest hp
  refine ⟨?_,?_,?_,?_⟩
  · rw [row_tail hn hsmall _ _ hf _ _ h₁,hsub]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    congr 1
    ring
  · rw [row_tail hn hsmall _ _ ((TileGapWords.twoSecond_perm_first n _).trans hf) _ _ h₂]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    congr 1
    ring
  · rw [row_tail hn hsmall _ _ ((TileGapWords.threeSecond_perm_first n _).trans hf) _ _ h₃]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    congr 1
    ring
  · rw [row_tail hn hsmall _ _ ((TileGapWords.threeThird_perm_first n _).trans hf) _ _ h₄]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    congr 1
    ring

end LocalTails

end CorralFormalization.LatinCompletion.GeneralTiles
