import CorralFormalization.Results.SwitchFamily.MarkerIsolation
import CorralFormalization.Results.SwitchFamily.Physical.Geometry

/-!
# The concrete Appendix A switch sites avoid all row markers

The n-gap markers lie at residues 0, 2 or -1. The two actual sites of every
Appendix A switch lie strictly between these residues, so the whole switch
layer fixes the canonically chosen n-gap marker of every baseline row.
-/

open EndpointRouter
open CorralFormalization.LatinCompletion
open CorralFormalization.LatinCompletion.TerraceLift
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.SwitchFamily.MarkerIsolation
open CorralFormalization.Results.SwitchFamily.Physical

namespace CorralFormalization.Results.SwitchFamily.ConcreteMarkers

noncomputable section

variable {h n m : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

omit [NeZero h] [NeZero n] [NeZero (h*n)] in
theorem endpoint_avoids_marker_residues (hsmall : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) (k : Bit m h) (s : Bool) :
    ¬ IsMarkerResidue (residueMap h n (endpoint (n:=n) k s)) := by
  rw [endpoint_residue]
  let v := Prefix.center k.1.val + s.toNat
  have hlarge : 3 < v := by dsimp [v,Prefix.center]; omega
  have hupper : v < n-3 := by
    cases s
    · have hv := Prefix.block_values hsize k.1.isLt
        (show Prefix.center k.1.val ∈ Prefix.blockNaturals k.1.val by simp [Prefix.blockNaturals])
      simpa [v] using hv.2
    · have hv := Prefix.block_values hsize k.1.isLt
        (show Prefix.center k.1.val+1 ∈ Prefix.blockNaturals k.1.val by simp [Prefix.blockNaturals])
      simpa [v] using hv.2
  have hvn : v<n := by omega
  change ¬ IsMarkerResidue ((v : ℕ) : ZMod n)
  intro hres
  rcases hres with hzero | htwo | hneg
  · have hv := congrArg ZMod.val hzero
    rw [ZMod.val_natCast_of_lt hvn, ZMod.val_zero] at hv
    omega
  · have hv := congrArg ZMod.val htwo
    change ((v : ℕ) : ZMod n).val = (((2 : ℕ) : ZMod n)).val at hv
    rw [ZMod.val_natCast_of_lt hvn,ZMod.val_natCast_of_lt (by omega : 2<n)] at hv
    omega
  · have hp : (((v+1 : ℕ) : ZMod n)) = 0 := by
      rw [Nat.cast_add, hneg]
      norm_num
    have hv := congrArg ZMod.val hp
    rw [ZMod.val_natCast_of_lt (by omega : v+1<n),ZMod.val_zero] at hv
    omega

/-- All actual pairs in the concrete finite layer meet the residue condition
used by `markers_exist_of_endpoint_residues`. -/
theorem switchLayer_avoids_marker_residues (hsmall : 65 ≤ n)
    (hsize : (5*m+8)^2 ≤ n) :
    ∀ e ∈ (switchLayer (h:=h) hsize).edges,
      ¬ IsMarkerResidue (residueMap h n e.1) ∧
      ¬ IsMarkerResidue (residueMap h n e.2) := by
  intro e he
  change e ∈ (Finset.univ : Finset (Bit m h)).toList.map (sitePair (n:=n)) at he
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp he
  exact ⟨endpoint_avoids_marker_residues hsmall hsize k false,
    endpoint_avoids_marker_residues hsmall hsize k true⟩

/-- Every baseline row has its actual gap-n tail as an isolated marker for
the concrete, complete collection of physical switches. -/
theorem concrete_gapN_markers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tiles : CyclicTiling h ι) (T : TerraceLift.CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65 ≤ n) (hsize : (5*m+8)^2 ≤ n) :
    ∀ R ∈ tiles.family T,
      gapNMarker R ∈ R ∧ (switchLayer (h:=h) hsize).Isolated (gapNMarker R) :=
  markers_exist_of_endpoint_residues tiles T hn hsmall (switchLayer hsize)
    (switchLayer_avoids_marker_residues hsmall hsize)

end
end CorralFormalization.Results.SwitchFamily.ConcreteMarkers
