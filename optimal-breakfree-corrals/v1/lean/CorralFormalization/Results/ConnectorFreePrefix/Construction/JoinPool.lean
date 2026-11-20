import CorralFormalization.Results.ConnectorFreePrefix.Construction.PrefixChain
import CorralFormalization.Results.ConnectorFreePrefix.ActualJoinDifferences
import CorralFormalization.Results.ConnectorFreePrefix.LexicographicJoins

/-! The actual lexicographic N-to-P edge pool is pairwise distinct.
This joins ordinary colour arithmetic to the literal list of consecutive
cells; no rainbow or simple-path hypothesis is used. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply LatinPrefixSupply.ConnectorGreedy

variable {r n : ℕ} [NeZero r]

theorem directGap_within (hr : 3 ≤ r) (hn : 200*r*r≤n) (i k : Cell r)
    (hj : k.1.val=i.1.val) (ht : k.2.val=i.2.val+1) :
    directGap n i k=(withinColor n r i.1.val i.2.val).toNat := by
  have hbound : i.2.val+1<r := by rw [←ht]; exact k.2.isLt
  have hk : k=(i.1,⟨i.2.val+1,hbound⟩) := Prod.ext (Fin.ext hj) (Fin.ext ht)
  rw [←direct_edge_value hr hn, hk]
  exact within_join_actual_color hr hn i.1 i.2 hbound

theorem directGap_between (hr : 3 ≤ r) (hn : 200*r*r≤n) (i k : Cell r)
    (ht : i.2.val+1=r) (hk0 : k.2.val=0) (hj : k.1.val=i.1.val+1) :
    directGap n i k=(betweenColor n r i.1.val).toNat := by
  have hbound : i.1.val+1<r := by rw [←hj]; exact k.1.isLt
  have hi2 : i.2=(⟨r-1,by have := NeZero.pos r; omega⟩:Fin r) := by
    apply Fin.ext
    change i.2.val=r-1
    omega
  have hk : k=(⟨i.1.val+1,hbound⟩,⟨0,NeZero.pos r⟩) := Prod.ext (Fin.ext hj) (Fin.ext hk0)
  rw [←direct_edge_value hr hn, hk]
  change (((waleckiCoordinates r).predecessor ⟨i.1.val+1,hbound⟩ ⟨0,NeZero.pos r⟩:ZMod n)-
    ((waleckiCoordinates r).successor i.1 i.2:ZMod n)).val=_
  rw [hi2]
  exact between_join_actual_color hr hn i.1 hbound

/-- Each entry in the literal lexicographic edge list has its actual L11
or L12 colour, with the corresponding valid row/column range. -/
theorem directGap_form (hr : 3 ≤ r) (hn : 200*r*r≤n)
    {e : Cell r×Cell r} (he : e ∈ lexEdges r) :
    (e.1.2.val<r-1 ∧ directGap n e.1 e.2=(withinColor n r e.1.1.val e.1.2.val).toNat) ∨
    (e.1.2.val+1=r ∧ e.1.1.val<r-1 ∧ directGap n e.1 e.2=(betweenColor n r e.1.1.val).toNat) := by
  rcases lexEdges_successor he with ⟨hj,ht⟩|⟨ht,hk0,hj⟩
  · exact Or.inl ⟨by have := e.2.2.isLt; omega,directGap_within hr hn e.1 e.2 hj ht⟩
  · exact Or.inr ⟨ht,by have := e.2.1.isLt; omega,directGap_between hr hn e.1 e.2 ht hk0 hj⟩

theorem directGap_bounds (hr : 3 ≤ r) (hn : 200*r*r≤n)
    {e : Cell r×Cell r} (he : e ∈ lexEdges r) :
    (n:ℤ)-64*(r:ℤ)*r ≤ (directGap n e.1 e.2:ℤ) ∧
      (directGap n e.1 e.2:ℤ) ≤ (n:ℤ)-58*(r:ℤ)*r := by
  rcases directGap_form hr hn he with ⟨ht,hc⟩|⟨_,hj,hc⟩
  · have hb := withinColor_bounds (n:=n) hr e.1.1.isLt ht
    have hs := directColor_separation hr hn _ hb
    rw [hc,Int.toNat_of_nonneg hs.2.2.1.le]
    exact hb
  · have hb := betweenColor_bounds (n:=n) hr hj
    have hs := directColor_separation hr hn _ hb
    rw [hc,Int.toNat_of_nonneg hs.2.2.1.le]
    exact hb

/-- Equality of actual direct-join colours identifies the source cell. -/
theorem directGap_source_injective (hr : 3 ≤ r) (hn : 200*r*r≤n)
    {e f : Cell r×Cell r} (he : e ∈ lexEdges r) (hf : f ∈ lexEdges r)
    (h : directGap n e.1 e.2=directGap n f.1 f.2) : e.1=f.1 := by
  rcases directGap_form hr hn he with ⟨het,hec⟩|⟨het,hej,hec⟩ <;>
    rcases directGap_form hr hn hf with ⟨hft,hfc⟩|⟨hft,hfj,hfc⟩
  · have hb := withinColor_bounds (n:=n) hr e.1.1.isLt het
    have hc := withinColor_bounds (n:=n) hr f.1.1.isLt hft
    have hp := (directColor_separation hr hn _ hb).2.2.1
    have hq := (directColor_separation hr hn _ hc).2.2.1
    have heq : withinColor n r e.1.1.val e.1.2.val=withinColor n r f.1.1.val f.1.2.val := by
      rw [hec,hfc] at h
      omega
    obtain ⟨hj,ht⟩ := withinColor_injective hr het hft heq
    exact Prod.ext (Fin.ext hj) (Fin.ext ht)
  · have hb := withinColor_bounds (n:=n) hr e.1.1.isLt het
    have hc := betweenColor_bounds (n:=n) hr hfj
    have hp := (directColor_separation hr hn _ hb).2.2.1
    have hq := (directColor_separation hr hn _ hc).2.2.1
    have heq : withinColor n r e.1.1.val e.1.2.val=betweenColor n r f.1.1.val := by
      rw [hec,hfc] at h
      omega
    exact (withinColor_ne_betweenColor hr het heq).elim
  · have hb := betweenColor_bounds (n:=n) hr hej
    have hc := withinColor_bounds (n:=n) hr f.1.1.isLt hft
    have hp := (directColor_separation hr hn _ hb).2.2.1
    have hq := (directColor_separation hr hn _ hc).2.2.1
    have heq : withinColor n r f.1.1.val f.1.2.val=betweenColor n r e.1.1.val := by
      rw [hec,hfc] at h
      omega
    exact (withinColor_ne_betweenColor hr hft heq).elim
  · have hb := betweenColor_bounds (n:=n) hr hej
    have hc := betweenColor_bounds (n:=n) hr hfj
    have hp := (directColor_separation hr hn _ hb).2.2.1
    have hq := (directColor_separation hr hn _ hc).2.2.1
    have heq : betweenColor n r e.1.1.val=betweenColor n r f.1.1.val := by
      rw [hec,hfc] at h
      omega
    have hj := betweenColor_injective hr heq
    exact Prod.ext (Fin.ext hj) (Fin.ext (by omega))

/-- The actual list of direct-join colours has no repetition. -/
theorem directGap_pool_nodup (hr : 3 ≤ r) (hn : 200*r*r≤n) :
    ((lexEdges r).map (fun e => directGap n e.1 e.2)).Nodup := by
  apply List.Nodup.map_on ?_ (List.Nodup.of_map Prod.fst (lexEdges_sources_nodup r))
  intro e he f hf h
  exact List.inj_on_of_nodup_map (lexEdges_sources_nodup r) he hf
    (directGap_source_injective hr hn he hf h)

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction
