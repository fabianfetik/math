import CorralFormalization.Results.SwitchFamily.Prefix.Basic

namespace CorralFormalization.Results.SwitchFamily.Prefix

open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles

/-- Uniform separation of the high backwards colors from all support colors. -/
theorem color_separation {n m i : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (hi : i < m) :
    20 ≤ alpha i ∧ alpha i+1 < beta i ∧ beta i+1 ≤ 8*m+17 ∧
    8*m+17 < n-(alpha i+beta i+1) ∧
    n-(alpha i+beta i+1) < n-14 ∧ 8*m+17 < n-14 := by
  have hp := parity_lt i
  have hbig : 24*m+46 < n := by nlinarith
  dsimp [alpha,beta]
  omega

theorem blockColors_values {n m i d : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (hi : i < m) (hd : d ∈ blockColors n i) :
    0 < d ∧ d < n := by
  have hsep := color_separation hn hsize hi
  simp only [blockColors,List.mem_cons,List.not_mem_nil,or_false] at hd
  omega

theorem blockColors_nodup {n m i : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (hi : i < m) : (blockColors n i).Nodup := by
  have hsep := color_separation hn hsize hi
  simp only [blockColors,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,not_false_eq_true,and_true]
  omega

theorem color_blocks_disjoint {n m i j : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (hij : i < j) (hj : j < m) :
    List.Disjoint (blockColors n i) (blockColors n j) := by
  have hi : i < m := by omega
  have hs := color_separation hn hsize hi
  have hs' := color_separation hn hsize hj
  have hp := parity_lt i
  have hp' := parity_lt j
  rw [List.disjoint_left]
  intro d hd he
  simp only [blockColors,List.mem_cons,List.not_mem_nil,or_false] at hd he
  dsimp [alpha,beta] at *
  omega

theorem color_blocks_nodup {n m : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) :
    ((List.range m).flatMap (blockColors n)).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsize' : (5*m+8)^2 ≤ n :=
      (Nat.pow_le_pow_left (by omega : 5*m+8 ≤ 5*(m+1)+8) 2).trans hsize
    have hnodup := ih hsize'
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [List.nodup_append]
    refine ⟨hnodup, blockColors_nodup hn hsize (by omega : m < m+1), ?_⟩
    intro d hd e he hde
    subst e
    obtain ⟨i,hi,hd⟩ := List.mem_flatMap.mp hd
    exact (List.disjoint_left.mp
      (color_blocks_disjoint hn hsize (List.mem_range.mp hi) (by omega : m < m+1))) hd he

theorem colors_nodup {n m : ℕ} (hn : 65 ≤ n) (hsize : (5*m+8)^2 ≤ n) :
    (colors n m).Nodup := by
  rw [colors,List.nodup_append]
  refine ⟨?_,color_blocks_nodup hn hsize,?_⟩
  · simp [explicitGapPrefix,List.nodup_cons]
    omega
  · intro d hd e he hde
    subst e
    obtain ⟨i,hi,he⟩ := List.mem_flatMap.mp he
    have hsep := color_separation hn hsize (List.mem_range.mp hi)
    simp only [explicitGapPrefix,List.mem_cons,List.not_mem_nil,or_false] at hd
    simp only [blockColors,List.mem_cons,List.not_mem_nil,or_false] at he
    omega

theorem colors_values {n m d : ℕ} (hn : 65 ≤ n) (hsize : (5*m+8)^2 ≤ n)
    (hd : d ∈ colors n m) : 0 < d ∧ d < n := by
  simp only [colors,List.mem_append] at hd
  rcases hd with hd|hd
  · simp only [explicitGapPrefix,List.mem_cons,List.not_mem_nil,or_false] at hd
    omega
  · obtain ⟨i,hi,hd⟩ := List.mem_flatMap.mp hd
    exact blockColors_values hn hsize (List.mem_range.mp hi) hd

/-- The predecessor of block i as a natural representative. -/
def predecessorNatural (i : ℕ) : ℕ := center i-alpha i

theorem alpha_lt_center (i : ℕ) : alpha i < center i := by
  have hb := beta_lt_center i
  have ha := beta_alpha i
  omega

theorem predecessorNatural_succ (i : ℕ) : predecessorNatural (i+1)=ending i := by
  dsimp [predecessorNatural]
  rw [predecessor]
  omega

theorem vertices_succ (n m : ℕ) :
    vertices n (m+1)=vertices n m ++ blockVertices n m := by
  simp [vertices_initial,List.range_succ,List.flatMap_append]

theorem vertices_end (n m : ℕ) :
    ∃ front : List (ZMod n),
      vertices n m=front ++ [((predecessorNatural m : ℕ) : ZMod n)] := by
  cases m with
  | zero =>
    refine ⟨[((n-3 : ℕ) : ZMod n),((n-1 : ℕ) : ZMod n),2,12,
      ((n-2 : ℕ) : ZMod n),10,17], ?_⟩
    simp [vertices,naturals,initialNaturals,predecessorNatural,center,alpha]
  | succ m =>
    rw [vertices_succ]
    refine ⟨vertices n m ++ [((center m : ℕ) : ZMod n),
      ((center m+alpha m+1 : ℕ) : ZMod n),((backward m : ℕ) : ZMod n),
      ((center m+1 : ℕ) : ZMod n)], ?_⟩
    simp [blockVertices,blockNaturals,predecessorNatural_succ,List.append_assoc]

/-- A4 is computed from the actual group differences of the six vertices. -/
theorem block_pathGaps {n m i : ℕ} [NeZero n] (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (hi : i < m) :
    pathGaps (((predecessorNatural i : ℕ) : ZMod n)::blockVertices n i)=
      blockColors n i := by
  have hsep := color_separation hn hsize hi
  have hpre : ((predecessorNatural i : ℕ) : ZMod n)=
      (center i : ZMod n)-(alpha i : ZMod n) := by
    exact Nat.cast_sub (alpha_lt_center i).le
  have hback : ((backward i : ℕ) : ZMod n)=
      (center i : ZMod n)-(beta i : ZMod n) := by
    exact Nat.cast_sub (beta_lt_center i).le
  have hhighle : alpha i+beta i+1 ≤ n := by omega
  have hhigh : ((n-(alpha i+beta i+1) : ℕ) : ZMod n)=
      -((alpha i : ZMod n)+(beta i : ZMod n)+1) := by
    rw [Nat.cast_sub hhighle,ZMod.natCast_self]
    push_cast
    ring
  have hvα : (alpha i : ZMod n).val=alpha i :=
    ZMod.val_natCast_of_lt (by omega)
  have hvα' : ((alpha i+1 : ℕ) : ZMod n).val=alpha i+1 :=
    ZMod.val_natCast_of_lt (by omega)
  have hvβ : (beta i : ZMod n).val=beta i :=
    ZMod.val_natCast_of_lt (by omega)
  have hvβ' : ((beta i+1 : ℕ) : ZMod n).val=beta i+1 :=
    ZMod.val_natCast_of_lt (by omega)
  have hvhigh : ((n-(alpha i+beta i+1) : ℕ) : ZMod n).val=
      n-(alpha i+beta i+1) := ZMod.val_natCast_of_lt (by omega)
  simp only [blockVertices,blockNaturals,List.map_cons,List.map_nil,pathGaps,hpre,hback]
  push_cast
  have h1 : (center i : ZMod n)-((center i : ZMod n)-(alpha i : ZMod n))=
      (alpha i : ZMod n) := by ring
  have h2 : ((center i : ZMod n)+(alpha i : ZMod n)+1)-(center i : ZMod n)=
      ((alpha i+1 : ℕ) : ZMod n) := by push_cast; ring
  have h3 : ((center i : ZMod n)-(beta i : ZMod n))-
      ((center i : ZMod n)+(alpha i : ZMod n)+1)=
      ((n-(alpha i+beta i+1) : ℕ) : ZMod n) := by rw [hhigh]; ring
  have h4 : ((center i : ZMod n)+1)-((center i : ZMod n)-(beta i : ZMod n))=
      ((beta i+1 : ℕ) : ZMod n) := by push_cast; ring
  have h5 : (ending i : ZMod n)-((center i : ZMod n)+1)=(beta i : ZMod n) := by
    simp only [ending,Nat.cast_add,Nat.cast_one]
    ring
  rw [h1,h2,h3,h4,h5,hvα,hvα',hvhigh,hvβ',hvβ]
  rfl

theorem initial_pathGaps {n : ℕ} [NeZero n] (hn : 65 ≤ n) :
    pathGaps (explicitPrefix n)=explicitGapPrefix n := by
  have hs1 : ((n-1 : ℕ) : ZMod n)= -1 := by
    rw [Nat.cast_sub (by omega : 1≤n),ZMod.natCast_self,Nat.cast_one]
    simp
  have hs2 : ((n-2 : ℕ) : ZMod n)= -2 := by
    rw [Nat.cast_sub (by omega : 2≤n),ZMod.natCast_self,Nat.cast_ofNat]
    simp
  have hs3 : ((n-3 : ℕ) : ZMod n)= -3 := by
    rw [Nat.cast_sub (by omega : 3≤n),ZMod.natCast_self,Nat.cast_ofNat]
    simp
  have hs14 : (-14 : ZMod n)=((n-14 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 14≤n),ZMod.natCast_self,Nat.cast_ofNat]
    simp
  simp only [explicitPrefix,explicitGapPrefix,pathGaps,hs1,hs2,hs3]
  norm_num only
  rw [hs14]
  simp only [List.cons.injEq,and_true]
  refine ⟨ZMod.val_natCast_of_lt (by omega : 2 < n),
    ZMod.val_natCast_of_lt (by omega : 3 < n),
    ZMod.val_natCast_of_lt (by omega : 10 < n),
    ZMod.val_natCast_of_lt (by omega : n-14 < n),
    ZMod.val_natCast_of_lt (by omega : 12 < n),
    ZMod.val_natCast_of_lt (by omega : 7 < n), ?_⟩
  simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (by omega : 1 < n))

/-- The entire A4 list is the actual consecutive-gap list, with no supplied
calendar assumption. -/
theorem vertices_pathGaps {n m : ℕ} [NeZero n] (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) : pathGaps (vertices n m)=colors n m := by
  induction m with
  | zero => simpa [vertices_initial,colors] using initial_pathGaps hn
  | succ m ih =>
    have hsize' : (5*m+8)^2 ≤ n :=
      (Nat.pow_le_pow_left (by omega : 5*m+8 ≤ 5*(m+1)+8) 2).trans hsize
    obtain ⟨front,hfront⟩ := vertices_end n m
    have hext : pathGaps (vertices n m ++ blockVertices n m)=
        pathGaps (vertices n m) ++ blockColors n m := by
      rw [hfront,List.append_assoc]
      change pathGaps (front ++ ((predecessorNatural m : ℕ) : ZMod n)::blockVertices n m)=_
      rw [pathGaps_append_pivot,block_pathGaps hn hsize (by omega : m < m+1)]
    rw [vertices_succ,hext,ih hsize']
    simp [colors,List.range_succ,List.flatMap_append,List.append_assoc]

theorem vertices_rainbow {n m : ℕ} [NeZero n] (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) : (pathGaps (vertices n m)).Nodup := by
  rw [vertices_pathGaps hn hsize]
  exact colors_nodup hn hsize

theorem vertices_colors_nonzero {n m : ℕ} [NeZero n] (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) : ∀ d ∈ pathGaps (vertices n m), d ≠ 0 := by
  rw [vertices_pathGaps hn hsize]
  intro d hd
  exact (colors_values hn hsize hd).1.ne'

/-- Exact positive lift of each five-gap block. -/
theorem blockColors_sum {n m i : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (hi : i < m) :
    (blockColors n i).sum=n+alpha i+beta i+1 := by
  have hsep := color_separation hn hsize hi
  simp only [blockColors,List.sum_cons,List.sum_nil]
  omega

/-- The first moving center's positive lift, needed when the calendar is
assembled into the physical tile body. -/
theorem centers_positive_lift {n m i : ℕ} (hn : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (hi : i ≤ m) :
    18+((List.range i).flatMap (blockColors n)).sum+alpha i=center i+i*n := by
  induction i with
  | zero => simp [center,alpha]
  | succ i ih =>
    have hil : i < m := by omega
    have hrec := predecessor i
    have hprev := ih (by omega)
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.sum_append]
    rw [blockColors_sum hn hsize hil]
    simp only [ending] at hrec
    simp only [Nat.add_mul,Nat.one_mul]
    omega

end CorralFormalization.Results.SwitchFamily.Prefix
