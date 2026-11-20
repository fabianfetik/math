import CorralFormalization.DiversityCompletion.TwoTilePartition

namespace CorralFormalization.LatinCompletion.TerraceLift.CompletedTerrace

open LatinTransfer DiversitySymmetry

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

theorem tileRow_two (o : ZMod (h*n)) (a b : ℕ) :
    TileGapWords.row o [a,b] = {o,o+(a : ZMod (h*n))} := by
  simp [TileGapWords.row,physicalOffsets,properPrefixSites]

def threeBoundary (q : ZMod h) : Finset (ZMod (h*n)) :=
  {zeroSite h n q-(n : ZMod (h*n))-1,zeroSite h n q-(n : ZMod (h*n))+2}

def threeRemainder (T : CompletedTerrace n) (q : ZMod h) : Finset (ZMod (h*n)) :=
  TileGapWords.row (zeroSite h n (q-1)+12) ([n-14,12]++T.body++[2])

theorem zeroSite_two_pred (q : ZMod h) :
    zeroSite h n (q-2) = zeroSite h n q-2*(n : ZMod (h*n)) := by
  have hq : q-2 = (q-1)-1 := by ring
  rw [hq,zeroSite_pred,zeroSite_pred]
  ring

theorem round_two_pred_decomposition (T : CompletedTerrace n) (q : ZMod h) :
    T.roundSites (q-2) = threeBoundary q ∪ T.threeRemainder q := by
  have hg : TileGapWords.cycle n T.body = [3,10]++([n-14,12]++T.body++[2]) := by
    simp [TileGapWords.cycle]
  have hsub : ((n-1 : ℕ) : ZMod (h*n)) = (n : ZMod (h*n))-1 := by
    rw [Nat.cast_sub (by have := NeZero.pos n; omega : 1 ≤ n),Nat.cast_one]
  have ha : zeroSite h n (q-2)+((n-1 : ℕ) : ZMod (h*n)) = zeroSite h n q-(n : ZMod (h*n))-1 := by
    rw [zeroSite_two_pred,hsub]; ring
  have hb : zeroSite h n q-(n : ZMod (h*n))-1+(3 : ZMod (h*n)) =
      zeroSite h n q-(n : ZMod (h*n))+2 := by ring
  have hd : zeroSite h n q-(n : ZMod (h*n))-1+(13 : ZMod (h*n)) =
      zeroSite h n (q-1)+12 := by rw [zeroSite_pred]; ring
  rw [T.roundSites_row,hg,tileRow_append,tileRow_two]
  simpa only [List.sum_cons,List.sum_nil,Nat.add_zero,Nat.reduceAdd,Nat.cast_ofNat,
    ha,hb,hd,threeBoundary,threeRemainder]

theorem threeSecond_decomposition (T : CompletedTerrace n) (hn : n=2*h-1) (q : ZMod h) :
    TileGapWords.row (zeroSite h n q+2) (TileGapWords.threeSecond n T.body) =
      T.twoRemainder q ∪ threeBoundary q := by
  let g := TileGapWords.middle n T.body++[2]
  have hg : TileGapWords.cycle n T.body = [3]++g := T.cycle_head
  have hs : g.sum+3 = (TileGapWords.cycle n T.body).sum := by
    rw [hg]; simp; omega
  have hsc := congrArg (fun k : ℕ => (k : ZMod (h*n))) hs
  simp only [Nat.cast_add,Nat.cast_ofNat] at hsc
  have hc := T.round_displacement hn
  have ha : zeroSite h n q+2+(g.sum : ZMod (h*n)) = zeroSite h n q-(n : ZMod (h*n))-1 := by
    linear_combination hsc+hc
  have hb : zeroSite h n q+2+(g.sum : ZMod (h*n))+3 = zeroSite h n q-(n : ZMod (h*n))+2 := by
    linear_combination hsc+hc
  have hw : TileGapWords.threeSecond n T.body = g++[3,n] := by
    simp [g,TileGapWords.threeSecond,List.append_assoc]
  rw [hw,tileRow_append,tileRow_two]
  simp only [Nat.cast_ofNat]
  rw [hb,ha]
  rfl

theorem split_twelve (o : ZMod (h*n)) (a : ℕ) (g : List ℕ) :
    TileGapWords.row o ([a,2,10]++g) =
      TileGapWords.row o ([a,12]++g) ∪ {o+(a : ZMod (h*n))+2} := by
  rw [tileRow_append,tileRow_append,tileRow_three,tileRow_two]
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero,Nat.cast_add,Nat.cast_ofNat]
  have hs : o+((a : ZMod (h*n))+(2+10)) = o+((a : ZMod (h*n))+12) := by ring
  rw [hs]
  ext x
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem tail_repair (o : ZMod (h*n)) (g : List ℕ) :
    TileGapWords.row o (g++[3,n,12]) = TileGapWords.row o (g++[2]) ∪
      {o+(g.sum : ZMod (h*n))+3,o+(g.sum : ZMod (h*n))+3+(n : ZMod (h*n))} := by
  rw [tileRow_append,tileRow_append,tileRow_three,tileRow_singleton]
  simp only [Nat.cast_ofNat]
  ext x
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem threeThird_decomposition (T : CompletedTerrace n) (hn : n=2*h-1)
    (hsmall : 15 ≤ n) (q : ZMod h) :
    TileGapWords.row (zeroSite h n (q-1)+12) (TileGapWords.threeThird n T.body) =
      T.threeRemainder q ∪ {zeroSite h n q,zeroSite h n (q-2),zeroSite h n (q-1)} := by
  let D := zeroSite h n (q-1)+12
  let g := [n-14,12]++T.body
  have hw : TileGapWords.threeThird n T.body = [n-14,2,10]++(T.body++[3,n,12]) := by
    simp [TileGapWords.threeThird,TileGapWords.thirdPrefix,List.append_assoc]
  have hgn : [n-14,12]++(T.body++[3,n,12]) = g++[3,n,12] := by simp [g,List.append_assoc]
  have hs : g.sum+15 = (TileGapWords.cycle n T.body).sum := by
    simp [g,TileGapWords.cycle]; omega
  have hsc := congrArg (fun k : ℕ => (k : ZMod (h*n))) hs
  simp only [Nat.cast_add,Nat.cast_ofNat] at hsc
  have hc := T.round_displacement hn
  have hsub : ((n-14 : ℕ) : ZMod (h*n)) = (n : ZMod (h*n))-14 := by
    rw [Nat.cast_sub (by omega : 14 ≤ n),Nat.cast_ofNat]
  have hz : D+((n-14 : ℕ) : ZMod (h*n))+2 = zeroSite h n q := by
    dsimp [D]; rw [zeroSite_pred,hsub]; ring
  have h₁ : D+(g.sum : ZMod (h*n))+3 = zeroSite h n (q-2) := by
    dsimp [D]
    rw [zeroSite_two_pred,zeroSite_pred]
    linear_combination hsc+hc
  have h₂ : D+(g.sum : ZMod (h*n))+3+(n : ZMod (h*n)) = zeroSite h n (q-1) := by
    dsimp [D]
    linear_combination hsc+hc
  change TileGapWords.row D _ = _
  rw [hw,split_twelve,hgn,tail_repair,h₂,h₁,hz]
  change (T.threeRemainder q ∪ {zeroSite h n (q-2),zeroSite h n (q-1)}) ∪
    {zeroSite h n q} = _
  ext x
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem threeRemainder_card (T : CompletedTerrace n) (hn : n=2*h-1) (q : ZMod h) :
    (T.threeRemainder q).card = n-3 := by
  let g := [n-14,12]++T.body++[2]
  have hg : TileGapWords.cycle n T.body = [3,10]++g := by simp [g,TileGapWords.cycle]
  have hpos : ∀ x ∈ g, 0 < x := by
    intro x hx
    have hxc : x ∈ TileGapWords.cycle n T.body := by rw [hg]; simp [hx]
    exact ((fullGapList_mem (n-1) x).mp (T.differences.mem_iff.mp hxc)).1
  have hlen : g.length = n-3 := by
    have hl := T.differences.length_eq
    rw [hg] at hl
    simp only [List.length_append,List.length_cons,List.length_nil] at hl
    simp only [fullGapList,List.length_map,List.length_range] at hl
    omega
  have hsum : g.sum ≤ h*n := by
    have hf := TileGapWords.first_perm (NeZero.pos n) T.body T.differences
    have hs := (TileGapWords.word_properties hn (NeZero.pos h) _ hf).2.1
    rw [TileGapWords.first,hg] at hs
    simp only [List.sum_append,List.sum_cons,List.sum_nil] at hs
    omega
  exact (prefix_card_sum_le (zeroSite h n (q-1)+12) g hpos hsum).trans hlen

theorem threeBoundary_card (hn : n=2*h-1) (hsmall : 15 ≤ n) (q : ZMod h) :
    (threeBoundary (n := n) q).card = 2 := by
  have hne : zeroSite h n q-(n : ZMod (h*n))-1 ≠ zeroSite h n q-(n : ZMod (h*n))+2 := by
    intro he
    have h3 : (3 : ZMod (h*n)) = 0 := by linear_combination -he
    have hv := congrArg ZMod.val h3
    have hclock : 3 < h*n := by
      have hh : 1 ≤ h := by omega
      have hm := Nat.mul_le_mul_right n hh
      nlinarith
    rw [show (3 : ZMod (h*n)).val = 3 from ZMod.val_natCast_of_lt hclock,
      ZMod.val_zero] at hv
    omega
  simp [threeBoundary,hne]

theorem threeBoundary_disjoint_remainder (T : CompletedTerrace n) (hn : n=2*h-1)
    (hsmall : 15 ≤ n) (q : ZMod h) : Disjoint (threeBoundary q) (T.threeRemainder q) := by
  apply Finset.card_union_eq_card_add_card.mp
  rw [← T.round_two_pred_decomposition,T.roundSites_card,threeBoundary_card hn hsmall,
    T.threeRemainder_card hn]
  omega

theorem phase_ne_two_pred (hn : n=2*h-1) (hsmall : 15 ≤ n) (q : ZMod h) : q ≠ q-2 := by
  intro he
  have h2 : (2 : ZMod h) = 0 := by linear_combination he
  have hv := congrArg ZMod.val h2
  rw [show (2 : ZMod h).val = 2 from ZMod.val_natCast_of_lt (by omega : 2 < h),ZMod.val_zero] at hv
  omega

theorem regroup_three {X : Type*} [DecidableEq X]
    (R₀ R₁ R₂ F₁ S₁ F₂ S₂ Z : Finset X)
    (hs₁ : R₁ = F₁ ∪ S₁) (hs₂ : R₂ = F₂ ∪ S₂)
    (h₀₁ : Disjoint R₀ R₁) (h₀₂ : Disjoint R₀ R₂) (h₁₂ : Disjoint R₁ R₂)
    (hd₁ : Disjoint F₁ S₁) (hd₂ : Disjoint F₂ S₂)
    (hZ : Disjoint (R₀ ∪ R₁ ∪ R₂) Z) :
    Disjoint (R₀ ∪ F₁) (S₁ ∪ F₂) ∧
    Disjoint (R₀ ∪ F₁) (S₂ ∪ Z) ∧
    Disjoint (S₁ ∪ F₂) (S₂ ∪ Z) ∧
    (R₀ ∪ F₁) ∪ (S₁ ∪ F₂) ∪ (S₂ ∪ Z) = R₀ ∪ R₁ ∪ R₂ ∪ Z := by
  have hF₁ : F₁ ⊆ R₁ := by rw [hs₁]; exact Finset.subset_union_left
  have hS₁ : S₁ ⊆ R₁ := by rw [hs₁]; exact Finset.subset_union_right
  have hF₂ : F₂ ⊆ R₂ := by rw [hs₂]; exact Finset.subset_union_left
  have hS₂ : S₂ ⊆ R₂ := by rw [hs₂]; exact Finset.subset_union_right
  have hab : Disjoint (R₀ ∪ F₁) (S₁ ∪ F₂) := by
    apply Finset.disjoint_union_left.mpr
    exact ⟨Finset.disjoint_union_right.mpr ⟨h₀₁.mono_right hS₁,h₀₂.mono_right hF₂⟩,
      Finset.disjoint_union_right.mpr ⟨hd₁,h₁₂.mono hF₁ hF₂⟩⟩
  have he : (R₀ ∪ F₁) ∪ (S₁ ∪ F₂) = R₀ ∪ R₁ ∪ F₂ := by
    rw [hs₁]
    ext x
    simp only [Finset.mem_union]
    tauto
  have hsub : R₀ ∪ R₁ ∪ F₂ ⊆ R₀ ∪ R₁ ∪ R₂ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (hF₂ hx)
  have hc : Disjoint ((R₀ ∪ F₁) ∪ (S₁ ∪ F₂)) (S₂ ∪ Z) := by
    rw [he]
    apply Finset.disjoint_union_right.mpr
    refine ⟨?_,hZ.mono_left hsub⟩
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨h₀₂.mono_right hS₂,h₁₂.mono_right hS₂⟩,hd₂⟩
  obtain ⟨hac,hbc⟩ := Finset.disjoint_union_left.mp hc
  refine ⟨hab,hac,hbc,?_⟩
  rw [he,hs₂]
  ext x
  simp only [Finset.mem_union]
  tauto

/-- Three actual tile rows partition exactly three consecutive terrace
rounds and their three zero sites. All insertion and regrouping identities
are proved above; no desired tile coverage/disjointness is assumed. -/
theorem three_tile_partition (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    (q : ZMod h) :
    let A := TileGapWords.row (zeroSite h n q+((n-1 : ℕ) : ZMod (h*n))) (TileGapWords.first n T.body)
    let B := TileGapWords.row (zeroSite h n q+2) (TileGapWords.threeSecond n T.body)
    let C := TileGapWords.row (zeroSite h n (q-1)+12) (TileGapWords.threeThird n T.body)
    Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = T.roundSites q ∪ T.roundSites (q-1) ∪ T.roundSites (q-2) ∪
        {zeroSite h n q,zeroSite h n (q-2),zeroSite h n (q-1)} := by
  dsimp only
  rw [T.first_tile_row_eq_round hn,T.threeSecond_decomposition hn,
    T.threeThird_decomposition hn hsmall]
  have hd₁ : Disjoint {zeroSite h n q-1} (T.twoRemainder q) := by
    apply Finset.disjoint_left.mpr
    intro x hx hr
    have he := Finset.mem_singleton.mp hx
    exact T.boundary_not_mem_remainder hn hsmall q (he ▸ hr)
  have hbc : q-1 ≠ q-2 := by
    have he : (q-1)-1 = q-2 := by ring
    simpa only [he] using phase_ne_pred hn hsmall (q-1)
  have hZ : Disjoint (T.roundSites q ∪ T.roundSites (q-1) ∪ T.roundSites (q-2))
      {zeroSite h n q,zeroSite h n (q-2),zeroSite h n (q-1)} := by
    have hz (p : ZMod h) : zeroSite h n p ∉
        T.roundSites q ∪ T.roundSites (q-1) ∪ T.roundSites (q-2) := by
      intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx <;> exact T.zero_not_mem_round _ _ hx
      · exact T.zero_not_mem_round _ _ hx
    apply Finset.disjoint_left.mpr
    intro x hx hxZ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hxZ
    rcases hxZ with rfl | rfl | rfl <;> exact hz _ hx
  exact regroup_three _ _ _ _ _ _ _ _
    (T.round_pred_decomposition q) (T.round_two_pred_decomposition q)
    (T.roundSites_disjoint (phase_ne_pred hn hsmall q))
    (T.roundSites_disjoint (phase_ne_two_pred hn hsmall q))
    (T.roundSites_disjoint hbc) hd₁ (T.threeBoundary_disjoint_remainder hn hsmall q) hZ

end CorralFormalization.LatinCompletion.TerraceLift.CompletedTerrace
