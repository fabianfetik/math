import CorralFormalization.Results.SwitchFamily.OrbitAssembly

/-!
# Gap-n tail markers and switch-site residues

The fixed baseline tiles already supply exactly one physical gap-n tail per
row.  This module chooses those actual tails and proves that a switch layer
avoiding their three possible residue classes fixes every chosen marker.  It
does not assume a supplied marker function or assert that the concrete switch
endpoints satisfy the residue test.
-/

open EndpointRouter
open CorralFormalization.PhysicalCorral CorralFormalization.DiversitySymmetry
open CorralFormalization.LatinCompletion
open CorralFormalization.LatinCompletion.TerraceLift
open CorralFormalization.LatinCompletion.GeneralTiles

namespace CorralFormalization.Results.SwitchFamily.MarkerIsolation

noncomputable section

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The three residue classes in which a baseline gap-n tail can lie. -/
def IsMarkerResidue (z : ZMod n) : Prop := z=0 ∨ z=2 ∨ z= -1

omit [NeZero h] [NeZero n] [NeZero (h*n)] [DecidableEq ι] in
theorem nTailPattern_residue (tiles : CyclicTiling h ι) (x : ZMod (h*n))
    (hx : x ∈ tiles.nTailPattern n) : IsMarkerResidue (residueMap h n x) := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
  cases hs : tiles.size i <;>
    simp only [localNTails,hs,Finset.mem_insert,Finset.mem_singleton] at hi
  · rcases hi with rfl | rfl
    · right; right; simp [map_sub,zeroSite_residue]
    · left; simp [map_sub,zeroSite_residue]
  · rcases hi with rfl | rfl | rfl
    · right; right; simp [map_sub,zeroSite_residue]
    · right; left; simp [map_add,map_sub,map_ofNat,zeroSite_residue]
    · left; simp [map_sub,map_mul,zeroSite_residue]

/-- A canonical choice from the actual gap-n tail set. The fallback is
irrelevant whenever the row has the full cyclic gap inventory. -/
def gapNMarker (R : Finset (ZMod (h*n))) : ZMod (h*n) :=
  if hx : (gapTails R n).Nonempty then Classical.choose hx else 0

omit [NeZero h] [NeZero n] in
theorem gapNMarker_mem_tail (R : Finset (ZMod (h*n))) (hn : 2 ≤ n)
    (hpal : finiteCyclicGapInventory (h*n) (R.image ZMod.val) =
      Multiset.ofList (fullGapList n)) : gapNMarker R ∈ gapTails R n := by
  obtain ⟨x,hx⟩ := gapTails_singleton_of_finiteCyclicGapInventory n R hn hpal n (by omega) le_rfl
  have hne : (gapTails R n).Nonempty := ⟨x,by rw [hx]; simp⟩
  simp only [gapNMarker, dif_pos hne]
  exact Classical.choose_spec hne

omit [NeZero h] [NeZero n] in
theorem gapNMarker_in_row (R : Finset (ZMod (h*n))) (hn : 2 ≤ n)
    (hpal : finiteCyclicGapInventory (h*n) (R.image ZMod.val) =
      Multiset.ofList (fullGapList n)) : gapNMarker R ∈ R := by
  have hx := gapNMarker_mem_tail R hn hpal
  obtain ⟨y,hy,_⟩ := (mem_gapTails R n (gapNMarker R)).mp hx
  exact hy.1

/-- The marker function required for the unlabelled switch decoder is
constructed from actual gap-n tails. Every layer endpoint is assumed to
avoid the three specific residue classes; checking that concrete fact is a
separate site-geometry task. -/
theorem markers_exist_of_endpoint_residues
    (tiles : CyclicTiling h ι) (T : TerraceLift.CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65 ≤ n)
    (layer : MatchingLayer (ZMod (h*n)))
    (havoid : ∀ e ∈ layer.edges,
      ¬ IsMarkerResidue (residueMap h n e.1) ∧
      ¬ IsMarkerResidue (residueMap h n e.2)) :
    ∀ R ∈ tiles.family T, gapNMarker R ∈ R ∧ layer.Isolated (gapNMarker R) := by
  intro R hR
  have hpal := tiles.inventory T hn (by omega) R hR
  have htail := gapNMarker_mem_tail R (by omega) hpal
  have hglobal : gapNMarker R ∈ familyTails (tiles.family T) n :=
    Finset.mem_biUnion.mpr ⟨R,hR,htail⟩
  rw [tiles.gap_n_tails T hn hsmall] at hglobal
  have hres := nTailPattern_residue tiles (gapNMarker R) hglobal
  refine ⟨gapNMarker_in_row R (by omega) hpal,?_⟩
  intro hinc
  obtain ⟨e,he,hi⟩ := hinc
  rcases hi with hi | hi
  · exact (havoid e he).1 (by simpa [hi] using hres)
  · exact (havoid e he).2 (by simpa [hi] using hres)

end
end CorralFormalization.Results.SwitchFamily.MarkerIsolation
