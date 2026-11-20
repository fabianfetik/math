import CorralFormalization.Results.ConnectorFreePrefix.Construction.PrefixChain
import CorralFormalization.DiversityCompletion.LatinConnectorFixedSeparation

/-! Distinct actual array vertices and the two disjoint centre-colour pools.
The `m+1` column spacing and `m` row spacing are kept literal throughout. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply

variable {r : ℕ} [NeZero r]

abbrev prefixIncoming (i : Cell r) : ℕ := prefixA i+canonicalSymbol i
abbrev prefixOutgoing (i : Cell r) : ℕ := prefixB i-canonicalSymbol i

def arrayVertexBlock (i : Cell r) : List ℕ :=
  [prefixPredecessor i,prefixCenter i,prefixSuccessor i]

def centerColorBlock (i : Cell r) : List ℕ := [prefixIncoming i,prefixOutgoing i]

private theorem column_of_grid {m u v j k : ℕ} (hu : u < m) (hv : v < m)
    (h : (m+1)*u+m*j=(m+1)*v+m*k) : u=v := by
  have h' : ((m:ℤ)+1)*u+(m:ℤ)*j=((m:ℤ)+1)*v+(m:ℤ)*k := by exact_mod_cast h
  have hc : (u:ℤ) ≡ (v:ℤ) [ZMOD (m:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨(u:ℤ)-v+j-k,?_⟩
    nlinarith
  exact ((Int.natCast_modEq_iff).mp hc).eq_of_lt_of_lt hu hv

theorem prefixPredecessor_injective (hr : 3 ≤ r) :
    Function.Injective (prefixPredecessor (r:=r)) := by
  intro i k h
  have hi := (waleckiCoordinates r).xi_normalization hr i.2
  have hk := (waleckiCoordinates r).xi_normalization hr k.2
  have hip := (waleckiCoordinates r).local_gap_geometry hr
    (le_refl (200*r*r)) i.1 i.2 ((cyclicLatinSquare r).entry i.1 i.2)
  have hkp := (waleckiCoordinates r).local_gap_geometry hr
    (le_refl (200*r*r)) k.1 k.2 ((cyclicLatinSquare r).entry k.1 k.2)
  have hp : (modulus r+1)*column r i.2.val+modulus r*k.1.val=
      (modulus r+1)*column r k.2.val+modulus r*i.1.val := by
    dsimp [prefixPredecessor,ConnectorFreePhysical.Coordinates.a] at h
    change (waleckiCoordinates r).predecessor i.1 i.2=
      (waleckiCoordinates r).predecessor k.1 k.2 at h
    change (waleckiCoordinates r).xi i.2+(modulus r+1)*column r 0=
      20*r*r+(modulus r+1)*column r i.2.val at hi
    change (waleckiCoordinates r).xi k.2+(modulus r+1)*column r 0=
      20*r*r+(modulus r+1)*column r k.2.val at hk
    have hai := hip.2.2.1
    have hak := hkp.2.2.1
    change (waleckiCoordinates r).predecessor i.1 i.2+(10*r*r+modulus r*i.1.val)=
      (waleckiCoordinates r).xi i.2 at hai
    change (waleckiCoordinates r).predecessor k.1 k.2+(10*r*r+modulus r*k.1.val)=
      (waleckiCoordinates r).xi k.2 at hak
    omega
  have hcol := column_of_grid (column_lt (NeZero.pos r) _) (column_lt (NeZero.pos r) _) hp
  have ht : i.2=k.2 := Fin.ext (column_injective (NeZero.pos r) i.2.isLt k.2.isLt hcol)
  have hM := modulus_pos (NeZero.pos r)
  have hj : i.1=k.1 := by
    rw [ht] at hp
    have he : modulus r*k.1.val=modulus r*i.1.val := Nat.add_left_cancel hp
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hM he.symm)
  exact Prod.ext hj ht

theorem prefixSuccessor_injective (hr : 3 ≤ r) :
    Function.Injective (prefixSuccessor (r:=r)) := by
  intro i k h
  have hi := (waleckiCoordinates r).xi_normalization hr i.2
  have hk := (waleckiCoordinates r).xi_normalization hr k.2
  have hp : (modulus r+1)*column r i.2.val+modulus r*i.1.val=
      (modulus r+1)*column r k.2.val+modulus r*k.1.val := by
    change (waleckiCoordinates r).xi i.2+(50*r*r+modulus r*i.1.val)=
      (waleckiCoordinates r).xi k.2+(50*r*r+modulus r*k.1.val) at h
    change (waleckiCoordinates r).xi i.2+(modulus r+1)*column r 0=
      20*r*r+(modulus r+1)*column r i.2.val at hi
    change (waleckiCoordinates r).xi k.2+(modulus r+1)*column r 0=
      20*r*r+(modulus r+1)*column r k.2.val at hk
    omega
  have hcol := column_of_grid (column_lt (NeZero.pos r) _) (column_lt (NeZero.pos r) _) hp
  have ht : i.2=k.2 := Fin.ext (column_injective (NeZero.pos r) i.2.isLt k.2.isLt hcol)
  have hj : i.1=k.1 := by
    rw [ht] at hp
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (modulus_pos (NeZero.pos r)) (Nat.add_left_cancel hp))
  exact Prod.ext hj ht

theorem prefixCenter_injective (hr : 3 ≤ r) :
    Function.Injective (prefixCenter (r:=r)) := by
  intro i k h
  have he : (waleckiCoordinates r).residue i.2 ((cyclicLatinSquare r).entry i.1 i.2)=
      (waleckiCoordinates r).residue k.2 ((cyclicLatinSquare r).entry k.1 k.2) := h
  have hp := (waleckiCoordinates r).residue_injective hr
    (a₁:=(i.2,(cyclicLatinSquare r).entry i.1 i.2))
    (a₂:=(k.2,(cyclicLatinSquare r).entry k.1 k.2)) he
  have ht : i.2=k.2 := congrArg Prod.fst hp
  have hs := congrArg Prod.snd hp
  have hj : i.1=k.1 := by
    apply ((cyclicLatinSquare r).column_bijective k.2).injective
    simpa only [ht] using hs
  exact Prod.ext hj ht

private theorem row_digits {j k s t : Fin r}
    (he : modulus r*j.val+s.val=modulus r*k.val+t.val) : j=k ∧ s=t := by
  have hm := modulus_bounds r
  have hd := congrArg (fun x => x/modulus r) he
  rw [Nat.mul_add_div (modulus_pos (NeZero.pos r)),Nat.mul_add_div (modulus_pos (NeZero.pos r)),
    Nat.div_eq_of_lt (s.isLt.trans_le hm.1),Nat.div_eq_of_lt (t.isLt.trans_le hm.1)] at hd
  have hj : j=k := Fin.ext (by simpa using hd)
  subst k
  exact ⟨rfl,Fin.ext (by omega)⟩

theorem prefixIncoming_injective : Function.Injective (prefixIncoming (r:=r)) := by
  intro i k h
  have he : modulus r*i.1.val+((cyclicLatinSquare r).entry i.1 i.2).val=
      modulus r*k.1.val+((cyclicLatinSquare r).entry k.1 k.2).val := by
    change 10*r*r+modulus r*i.1.val+canonicalSymbol i=
      10*r*r+modulus r*k.1.val+canonicalSymbol k at h
    exact Nat.add_left_cancel (by simpa only [Nat.add_assoc,canonicalSymbol] using h)
  obtain ⟨hj,hs⟩ := row_digits he
  have ht : i.2=k.2 := by
    apply ((cyclicLatinSquare r).row_bijective k.1).injective
    simpa only [hj] using hs
  exact Prod.ext hj ht

theorem symbol_le_prefixB (hr : 3 ≤ r) (i : Cell r) : canonicalSymbol i ≤ prefixB i := by
  have hs := ((cyclicLatinSquare r).entry i.1 i.2).isLt
  change canonicalSymbol i<r at hs
  change canonicalSymbol i≤50*r*r+modulus r*i.1.val
  nlinarith

theorem prefixOutgoing_injective (hr : 3 ≤ r) :
    Function.Injective (prefixOutgoing (r:=r)) := by
  intro i k h
  have hi := Nat.sub_add_cancel (symbol_le_prefixB hr i)
  have hk := Nat.sub_add_cancel (symbol_le_prefixB hr k)
  have he : modulus r*i.1.val+((cyclicLatinSquare r).entry k.1 k.2).val=
      modulus r*k.1.val+((cyclicLatinSquare r).entry i.1 i.2).val := by
    change prefixB i-canonicalSymbol i=prefixB k-canonicalSymbol k at h
    change prefixB i-canonicalSymbol i+canonicalSymbol i=50*r*r+modulus r*i.1.val at hi
    change prefixB k-canonicalSymbol k+canonicalSymbol k=50*r*r+modulus r*k.1.val at hk
    change modulus r*i.1.val+canonicalSymbol k=modulus r*k.1.val+canonicalSymbol i
    omega
  obtain ⟨hj,hs⟩ := row_digits he
  have ht : i.2=k.2 := by
    apply ((cyclicLatinSquare r).row_bijective k.1).injective
    simpa only [hj] using hs.symm
  exact Prod.ext hj ht

theorem prefix_center_color_bands (hr : 3 ≤ r) (i : Cell r) :
    10*r*r ≤ prefixIncoming i ∧ prefixIncoming i ≤ 12*r*r ∧
    49*r*r ≤ prefixOutgoing i ∧ prefixOutgoing i ≤ 51*r*r := by
  have hp := (row_product_bound hr i.1.isLt).trans (Nat.sub_le (r*r) 1)
  have hs := ((cyclicLatinSquare r).entry i.1 i.2).isLt
  have hsub := Nat.sub_add_cancel (symbol_le_prefixB hr i)
  change prefixOutgoing i+canonicalSymbol i=50*r*r+modulus r*i.1.val at hsub
  change canonicalSymbol i<r at hs
  change 10*r*r≤10*r*r+modulus r*i.1.val+canonicalSymbol i ∧ _
  constructor
  · omega
  constructor
  · change 10*r*r+modulus r*i.1.val+canonicalSymbol i≤12*r*r
    nlinarith
  constructor <;> nlinarith

theorem arrayVertexBlock_nodup (hr : 3 ≤ r) (i : Cell r) : (arrayVertexBlock i).Nodup := by
  have h := prefix_vertex_bands hr i
  have hR : 0<r*r := Nat.mul_pos (NeZero.pos r) (NeZero.pos r)
  have hPC : prefixPredecessor i≠prefixCenter i := by nlinarith
  have hCN : prefixCenter i≠prefixSuccessor i := by nlinarith
  have hPN : prefixPredecessor i≠prefixSuccessor i := by nlinarith
  simp [arrayVertexBlock,hPC,hCN,hPN]

theorem arrayVertexBlock_disjoint (hr : 3 ≤ r) (i k : Cell r) (hik : i≠k) :
    List.Disjoint (arrayVertexBlock i) (arrayVertexBlock k) := by
  intro x hx hy
  simp only [arrayVertexBlock,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  have hi := prefix_vertex_bands hr i
  have hk := prefix_vertex_bands hr k
  have hR : 0<r*r := Nat.mul_pos (NeZero.pos r) (NeZero.pos r)
  rcases hx with rfl|rfl|rfl <;> rcases hy with he|he|he
  · exact hik (prefixPredecessor_injective hr he)
  · nlinarith
  · nlinarith
  · nlinarith
  · exact hik (prefixCenter_injective hr he)
  · nlinarith
  · nlinarith
  · nlinarith
  · exact hik (prefixSuccessor_injective hr he)

theorem centerColorBlock_nodup (hr : 3 ≤ r) (i : Cell r) : (centerColorBlock i).Nodup := by
  have hb := prefix_center_color_bands hr i
  have hR : 0<r*r := Nat.mul_pos (NeZero.pos r) (NeZero.pos r)
  have hne : prefixIncoming i≠prefixOutgoing i := by nlinarith
  simp [centerColorBlock,hne]

theorem centerColorBlock_disjoint (hr : 3 ≤ r) (i k : Cell r) (hik : i≠k) :
    List.Disjoint (centerColorBlock i) (centerColorBlock k) := by
  intro x hx hy
  simp only [centerColorBlock,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  have hi := prefix_center_color_bands hr i
  have hk := prefix_center_color_bands hr k
  have hR : 0<r*r := Nat.mul_pos (NeZero.pos r) (NeZero.pos r)
  rcases hx with rfl|rfl <;> rcases hy with he|he
  · exact hik (prefixIncoming_injective he)
  · nlinarith
  · nlinarith
  · exact hik (prefixOutgoing_injective hr he)

theorem arrayVertices_nodup (hr : 3 ≤ r) (xs : List (Cell r)) (hx : xs.Nodup) :
    (xs.flatMap arrayVertexBlock).Nodup := by
  apply List.nodup_flatMap.mpr
  exact ⟨fun i _ => arrayVertexBlock_nodup hr i,hx.imp (fun {i k} hik => arrayVertexBlock_disjoint hr i k hik)⟩

theorem centerColors_nodup (hr : 3 ≤ r) (xs : List (Cell r)) (hx : xs.Nodup) :
    (xs.flatMap centerColorBlock).Nodup := by
  apply List.nodup_flatMap.mpr
  exact ⟨fun i _ => centerColorBlock_nodup hr i,hx.imp (fun {i k} hik => centerColorBlock_disjoint hr i k hik)⟩

theorem directVertices_eq_flatMap (first : Cell r) (rest : List (Cell r)) :
    directVertices first rest=(first::rest).flatMap arrayVertexBlock := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    change arrayVertexBlock first++directVertices next rest=_
    rw [ih]
    rfl

theorem prefixVertices_eq_pools (n r : ℕ) [NeZero r] :
    prefixVertices n r=[n-3,n-1,2,12,n-2,10,17,18]++(lexCells r).flatMap arrayVertexBlock := by
  rw [prefixVertices,directVertices_eq_flatMap,←lexCells_cons]

theorem prefixVertices_nodup {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r≤n) :
    (prefixVertices n r).Nodup := by
  rw [prefixVertices_eq_pools]
  have hR : 9≤r*r := by nlinarith
  have hlarge : 1800≤n := by nlinarith
  have hsub1 : n-1+1=n := by omega
  have hsub2 : n-2+2=n := by omega
  have hsub3 : n-3+3=n := by omega
  have hinit : [n-3,n-1,2,12,n-2,10,17,18].Nodup :=
    FixedConnectorPrefix.startVertices_nodup (by omega : 2≤r) (by nlinarith : 100*r*r≤n)
  apply hinit.append (arrayVertices_nodup hr _ ((lexCells_perm r).nodup_iff.mpr (Finset.nodup_toList _)))
  intro x hx hy
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hy
  have hb := prefix_vertex_bands hr i
  simp only [Nat.mul_assoc] at hb hn
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [arrayVertexBlock,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hi with he|he|he <;> omega

theorem prefixVertices_range {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r≤n)
    (x : ℕ) (hx : x ∈ prefixVertices n r) : 0<x ∧ x<n := by
  rw [prefixVertices_eq_pools] at hx
  have hR : 9≤r*r := by nlinarith
  have hlarge : 1800≤n := by nlinarith
  rcases List.mem_append.mp hx with hm|ha
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> omega
  · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp ha
    have hb := prefix_vertex_bands hr i
    simp only [Nat.mul_assoc] at hb hn
    simp only [arrayVertexBlock,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> constructor <;> omega

theorem prefixPath_nodup {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r≤n) :
    (prefixPath n r).Nodup := by
  apply List.Nodup.map_on (f:=fun x:ℕ=>(x:ZMod n)) ?_ (prefixVertices_nodup hr hn)
  intro x hx y hy he
  have hx' := prefixVertices_range hr hn x hx
  have hy' := prefixVertices_range hr hn y hy
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt hx'.2,ZMod.val_natCast_of_lt hy'.2] using hv

theorem prefixPath_nonzero {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r≤n)
    (z : ZMod n) (hz : z ∈ prefixPath n r) : z≠0 := by
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
  have hb := prefixVertices_range hr hn x hx
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hb.2,ZMod.val_zero] at hv
  omega

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction
