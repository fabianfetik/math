import CorralFormalization.DiversityCompletion.LatinConnectorFixedData

/-! Complete distinctness of the fixed connector-prefix data, including the eight
initial vertices, seven initial colours, and the first join colour. -/

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix

open LatinTransfer TerraceLift LatinPrefix

variable {r n : ℕ} [NeZero r]

def startVertices (n : ℕ) : List ℕ := [n-3,n-1,2,12,n-2,10,17,18]
def startColors (n : ℕ) : List ℕ := [2,3,10,n-14,12,7,1]
def firstJoin (r : ℕ) [NeZero r] : ℕ := P (firstCell r)-18
def vertexBlock (i : Cell r) : List ℕ := [P i,C i,N i]
def colorBlock (i : Cell r) : List ℕ := [incoming i,outgoing i]

theorem point_range (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (i : Cell r) :
    18 < P i ∧ P i < n-3 ∧ 18 < C i ∧ C i < n-3 ∧ 18 < N i ∧ N i < n-3 := by
  have hb := point_bands hr i
  have hR : 4 ≤ r*r := by nlinarith
  have hsq : r ≤ r*r := by nlinarith
  have hn3 : 3 ≤ n := by nlinarith
  have hsub := Nat.sub_add_cancel hn3
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem color_range (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (i : Cell r) :
    12 < incoming i ∧ incoming i < n-14 ∧
    12 < outgoing i ∧ outgoing i < n-14 := by
  have hb := color_bands hr i
  have hR : 4 ≤ r*r := by nlinarith
  have hsq : r ≤ r*r := by nlinarith
  have hn14 : 14 ≤ n := by nlinarith
  have hsub := Nat.sub_add_cancel hn14
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

theorem startVertices_nodup (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    (startVertices n).Nodup := by
  have hR : 4 ≤ r*r := by nlinarith
  have hlarge : 400 ≤ n := by nlinarith
  simp [startVertices] <;> omega

theorem startColors_nodup (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    (startColors n).Nodup := by
  have hR : 4 ≤ r*r := by nlinarith
  have hlarge : 400 ≤ n := by nlinarith
  simp [startColors] <;> omega

theorem not_mem_startVertices {x : ℕ} (hx0 : 18 < x) (hxn : x < n-3) :
    x ∉ startVertices n := by
  intro hm
  simp only [startVertices, List.mem_cons, List.mem_nil_iff, or_false] at hm
  omega

theorem not_mem_startColors {d : ℕ} (hd0 : 12 < d) (hdn : d < n-14) :
    d ∉ startColors n := by
  intro hm
  simp only [startColors, List.mem_cons, List.mem_nil_iff, or_false] at hm
  omega

theorem firstJoin_eq : firstJoin r = 10*r*r-18 := by
  unfold firstJoin
  have hP : P (firstCell r) = 10*r*r := by
    have he : 20*r*r = 10*r*r+10*r*r := by ring
    simp [P, firstCell, predecessor, centerBase, incomingBase, he]
  rw [hP]

theorem firstJoin_range (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    12 < firstJoin r ∧ firstJoin r < 10*r*r ∧ firstJoin r < n-14 := by
  have hR : 4 ≤ r*r := by nlinarith
  have h18 : 18 ≤ 10*r*r := by nlinarith
  have hsub := Nat.sub_add_cancel h18
  have hn14 : 14 ≤ n := by nlinarith
  have hsubn := Nat.sub_add_cancel hn14
  rw [firstJoin_eq]
  refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem firstJoin_not_mem_startColors (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    firstJoin r ∉ startColors n :=
  not_mem_startColors (firstJoin_range hr hn).1 (firstJoin_range hr hn).2.2

theorem firstJoin_lt_internal (hr : 2 ≤ r) (hn : 100*r*r ≤ n) (i : Cell r) :
    firstJoin r < incoming i ∧ firstJoin r < outgoing i := by
  have hj := (firstJoin_range hr hn).2.1
  have hi := (color_bands hr i).1
  have hio := incoming_lt_outgoing hr i i
  omega

theorem vertexBlock_nodup (hr : 2 ≤ r) (i : Cell r) : (vertexBlock i).Nodup := by
  have hPC := P_lt_C hr i i
  have hCN := C_lt_N hr i i
  have hPN := lt_trans hPC hCN
  simp [vertexBlock, ne_of_lt hPC, ne_of_lt hCN, ne_of_lt hPN]

theorem colorBlock_nodup (hr : 2 ≤ r) (i : Cell r) : (colorBlock i).Nodup := by
  simp [colorBlock, ne_of_lt (incoming_lt_outgoing hr i i)]

theorem vertexBlock_disjoint (hr : 2 ≤ r) (i j : Cell r) (hij : i ≠ j) :
    List.Disjoint (vertexBlock i) (vertexBlock j) := by
  intro x hx hy
  simp only [vertexBlock, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · exact hij (P_injective hr (hx.symm.trans hy))
  · have h := P_lt_C hr i j; omega
  · have h := lt_trans (P_lt_C hr i j) (C_lt_N hr j j); omega
  · have h := P_lt_C hr j i; omega
  · exact hij (C_injective (hx.symm.trans hy))
  · have h := C_lt_N hr i j; omega
  · have h := lt_trans (P_lt_C hr j i) (C_lt_N hr i i); omega
  · have h := C_lt_N hr j i; omega
  · exact hij (N_injective hr (hx.symm.trans hy))

theorem colorBlock_disjoint (hr : 2 ≤ r) (i j : Cell r) (hij : i ≠ j) :
    List.Disjoint (colorBlock i) (colorBlock j) := by
  intro d hd he
  simp only [colorBlock, List.mem_cons, List.not_mem_nil, or_false] at hd he
  rcases hd with hd | hd <;> rcases he with he | he
  · exact hij (incoming_injective (hd.symm.trans he))
  · have h := incoming_lt_outgoing hr i j; omega
  · have h := incoming_lt_outgoing hr j i; omega
  · exact hij (outgoing_injective hr (hd.symm.trans he))

theorem vertexBlock_avoids_start (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (i : Cell r) (x : ℕ) (hx : x ∈ vertexBlock i) : x ∉ startVertices n := by
  have hp := point_range hr hn i
  simp only [vertexBlock, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact not_mem_startVertices hp.1 hp.2.1
  · exact not_mem_startVertices hp.2.2.1 hp.2.2.2.1
  · exact not_mem_startVertices hp.2.2.2.2.1 hp.2.2.2.2.2

theorem colorBlock_avoids_start_join (hr : 2 ≤ r) (hn : 100*r*r ≤ n)
    (i : Cell r) (d : ℕ) (hd : d ∈ colorBlock i) :
    d ∉ startColors n ∧ d ≠ firstJoin r := by
  have hp := color_range hr hn i
  have hj := firstJoin_lt_internal hr hn i
  simp only [colorBlock, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨not_mem_startColors hp.1 hp.2.1, ne_of_gt hj.1⟩
  · exact ⟨not_mem_startColors hp.2.2.1 hp.2.2.2, ne_of_gt hj.2⟩

theorem internalVertices_nodup (hr : 2 ≤ r) (xs : List (Cell r)) (hx : xs.Nodup) :
    (xs.flatMap vertexBlock).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => vertexBlock_nodup hr i, hx.imp ?_⟩
  intro i j hij
  exact vertexBlock_disjoint hr i j hij

theorem internalColors_nodup (hr : 2 ≤ r) (xs : List (Cell r)) (hx : xs.Nodup) :
    (xs.flatMap colorBlock).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => colorBlock_nodup hr i, hx.imp ?_⟩
  intro i j hij
  exact colorBlock_disjoint hr i j hij

theorem lexCells_nodup (r : ℕ) : (lexCells r).Nodup :=
  (lexCells_perm r).nodup_iff.mpr (Finset.nodup_toList _)

def fixedVertexList (n r : ℕ) [NeZero r] : List ℕ :=
  startVertices n ++ (lexCells r).flatMap vertexBlock

def fixedColorList (n r : ℕ) [NeZero r] : List ℕ :=
  (startColors n ++ [firstJoin r]) ++ (lexCells r).flatMap colorBlock

/-- Every prescribed non-connector vertex is distinct, in the literal
initial/lexicographic order. No simple-path premise is used. -/
theorem fixedVertexList_nodup (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    (fixedVertexList n r).Nodup := by
  apply (startVertices_nodup hr hn).append (internalVertices_nodup hr _ (lexCells_nodup r))
  intro x hx hy
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hy
  exact vertexBlock_avoids_start hr hn i x hi hx

/-- All prescribed non-connector colours are distinct, including the
seven initial colours and the first join. No rainbow premise is used. -/
theorem fixedColorList_nodup (hr : 2 ≤ r) (hn : 100*r*r ≤ n) :
    (fixedColorList n r).Nodup := by
  have hinit : (startColors n ++ [firstJoin r]).Nodup := by
    apply (startColors_nodup hr hn).append (by simp)
    intro d hd hj
    have he : d = firstJoin r := by simpa using hj
    exact firstJoin_not_mem_startColors hr hn (he ▸ hd)
  apply hinit.append (internalColors_nodup hr _ (lexCells_nodup r))
  intro d hd hy
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hy
  obtain ⟨hs, hj⟩ := colorBlock_avoids_start_join hr hn i d hi
  rcases List.mem_append.mp hd with hd | hd
  · exact hs hd
  · exact hj (by simpa using hd)

end CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix
