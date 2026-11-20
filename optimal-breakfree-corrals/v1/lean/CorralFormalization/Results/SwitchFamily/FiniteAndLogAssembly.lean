import CorralFormalization.Results.SwitchFamily.OrbitAssembly
import CorralFormalization.Results.SwitchFamily.Asymptotic

/-!
# From genuine switch geometry to the two statements of Theorem A.2

This is a conditional assembly lemma, not a new proof of the concrete switch
construction. The hypotheses name the actual layer, site markers, opposite
owners and row modifications preserving palettes and edges. Once these are supplied
for the paper's specific terrace and the required number of site pairs, both
the exact finite census bound and the printed logarithmic bound follow.
-/

open EndpointRouter CorralLatinTailMarker
open CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.SwitchFamily.FamilySwitches
open CorralFormalization.Results.SwitchFamily.OrbitAssembly

namespace CorralFormalization.Results.SwitchFamily

noncomputable section

variable {h : ℕ} [NeZero h] [NeZero (2*h-1)] [NeZero (h*(2*h-1))]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal finite and logarithmic conclusions of A.2 follow from the
specified genuine physical switch geometry. All still-needed geometry is
visible in the theorem arguments. -/
theorem fixed_layout_count_and_log_of_site_geometry
    (hh : 33 ≤ h)
    (D : DirectedTerrace (2*h-1)) (hp : HasSpecifiedPrefix D)
    (tiles : CyclicTiling h ι) (p : ZMod h)
    (hthree : tiles.threeStarts={p} ∨ tiles.threeStarts={p,p-3})
    (layer : MatchingLayer (ZMod (h*(2*h-1))))
    (hlen : layer.edges.length = h * switchMultiplicity (2*h-1))
    (mark : Finset (ZMod (h*(2*h-1))) → ZMod (h*(2*h-1)))
    (hmark : ∀ R ∈ tiles.family (completedOfSpecifiedPrefix D (by omega) hp),
      mark R ∈ R ∧ layer.Isolated (mark R))
    (howner : ∀ e ∈ layer.edges,
      ∃ R ∈ tiles.family (completedOfSpecifiedPrefix D (by omega) hp), e.1 ∈ R ∧ e.2 ∉ R)
    (hmod : ∀ T ∈ layer.edges.toFinset.powerset,
      ∃ P : RowModification (2*h-1) (tiles.family (completedOfSpecifiedPrefix D (by omega) hp)),
        P.family = switchedFamily layer (tiles.family (completedOfSpecifiedPrefix D (by omega) hp)) T) :
    2^(h * switchMultiplicity (2*h-1)) ≤ A_h h (by omega) ∧
    (Real.sqrt 2 / 5) * (h : ℝ)^((3 : ℝ)/2) - (14 / 5) * (h : ℝ) ≤
      Real.logb 2 (A_h h (by omega) : ℝ) := by
  have hcount := fixed_layout_switches_give_asymmetric_orbits D rfl (by omega)
    hp tiles p hthree layer mark hmark howner hmod
  rw [hlen] at hcount
  rw [← A_h_eq (by omega : 2 ≤ h) (rfl : (2*h-1)=2*h-1)] at hcount
  exact ⟨hcount, switch_log_lower_of_count h hh hcount⟩

end
end CorralFormalization.Results.SwitchFamily
