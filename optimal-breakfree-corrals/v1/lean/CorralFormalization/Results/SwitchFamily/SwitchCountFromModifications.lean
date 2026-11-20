import CorralFormalization.Results.SwitchFamily.FiniteAndLogAssembly
import CorralFormalization.Results.SwitchFamily.ConcreteOwners
import CorralFormalization.Results.SwitchFamily.Prefix.Geometry

/-!
# A.2 reduced to the actual simultaneous row modifications

For the paper's exact nested-floor radius, this module supplies the concrete
switch layer, its size, actual isolated gap-n markers and distinct owners.
The explicitly visible remaining input constructs, for every chosen switch
set, the actual palette- and edge-preserving modifications of the given
tiles. This module does not assume an orbit or census bound.
-/

open EndpointRouter CorralLatinTailMarker
open CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.SwitchFamily.Physical
open CorralFormalization.Results.SwitchFamily.FamilySwitches
open CorralFormalization.Results.SwitchFamily.MarkerIsolation
open CorralFormalization.Results.SwitchFamily.ConcreteMarkers
open CorralFormalization.Results.SwitchFamily.ConcreteOwners

namespace CorralFormalization.Results.SwitchFamily

noncomputable section

variable {h : ℕ} [NeZero h] [NeZero (2*h-1)] [NeZero (h*(2*h-1))]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit pair layer with precisely the number of switches printed in
the paper. The large-height inequality follows from the actual floor. -/
def explicitSwitchLayer (hh : 33 ≤ h) : MatchingLayer (ZMod (h*(2*h-1))) :=
  switchLayer (h:=h) (n:=2*h-1) (m:=switchMultiplicity (2*h-1))
    (by
      change (5*Prefix.count (2*h-1)+8)^2 ≤ 2*h-1
      exact Prefix.count_square_bound (by omega))

theorem explicitSwitchLayer_length (hh : 33 ≤ h) :
    (explicitSwitchLayer hh).edges.length = h * switchMultiplicity (2*h-1) := by
  exact switchLayer_length _

/-- Both displayed conclusions of A.2, conditional only on constructing the
actual row modifications for every chosen set of the *concrete* paper
switches, on an actual terrace and one of the stated fixed layouts. -/
theorem count_and_log_from_actual_row_modifications
    (hh : 33 ≤ h)
    (D : DirectedTerrace (2*h-1)) (hp : HasSpecifiedPrefix D)
    (tiles : CyclicTiling h ι) (p : ZMod h)
    (hthree : tiles.threeStarts={p} ∨ tiles.threeStarts={p,p-3})
    (hmod : ∀ T ∈ (explicitSwitchLayer hh).edges.toFinset.powerset,
      ∃ P : RowModification (2*h-1) (tiles.family (completedOfSpecifiedPrefix D (by omega) hp)),
        P.family = switchedFamily (explicitSwitchLayer hh)
          (tiles.family (completedOfSpecifiedPrefix D (by omega) hp)) T) :
    2^(h * switchMultiplicity (2*h-1)) ≤ A_h h (by omega) ∧
    (Real.sqrt 2 / 5) * (h : ℝ)^((3 : ℝ)/2) - (14 / 5) * (h : ℝ) ≤
      Real.logb 2 (A_h h (by omega) : ℝ) := by
  have hs : (5*switchMultiplicity (2*h-1)+8)^2 ≤ 2*h-1 := by
    change (5*Prefix.count (2*h-1)+8)^2 ≤ 2*h-1
    exact Prefix.count_square_bound (by omega)
  have hm := concrete_gapN_markers (m:=switchMultiplicity (2*h-1)) tiles
    (completedOfSpecifiedPrefix D (by omega) hp) rfl (by omega) hs
  have ho := concrete_switch_owners (m:=switchMultiplicity (2*h-1)) D rfl (by omega) hp tiles hs
  exact fixed_layout_count_and_log_of_site_geometry hh D hp tiles p hthree
    (explicitSwitchLayer hh) (explicitSwitchLayer_length hh) gapNMarker hm ho hmod

end
end CorralFormalization.Results.SwitchFamily
