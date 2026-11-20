import CorralFormalization.Results.ConnectorFreePrefix.PhysicalTransfer.PrefixCalendar
import CorralFormalization.DiversityCompletion.CyclicEndpointConnectorOrbits

/-!
# From the actual connector-free prefix to physical asymmetric orbits

The physical construction consumes the terrace obtained by splicing the
same explicit prefix to an actual complementary endpoint path. The only
prefix input here is the existence of the literal `RainbowPrefix`; no frame,
physical partition, palette, decoding, or orbit assumption is supplied.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply CorralLatinTailMarker PhysicalCorral

noncomputable section

/-- An actual complementary path for the literal printed prefix yields
the stated family of actual asymmetric physical corral orbits. -/
theorem literal_prefix_orbits_of_completion {h n r : ℕ}
    [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
    (hr : 3 ≤ r) (hn : n = 2*h-1) (hlarge : 200*r*r ≤ n)
    (P : RainbowPrefix n) (Q : P.ComplementaryPath)
    (hpath : P.path = Construction.prefixPath n r) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r =>
        physicalOrbit (realizedFamily (C L)))).card = latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  have hfirst : P.first = ((n-3 : ℕ) : ZMod n) := by
    have hh := congrArg List.head? hpath
    simpa [RainbowPrefix.path, Construction.prefixPath, Construction.prefixVertices] using hh
  let S := P.splice Q
  have hstart : (S.directedTerrace.vertices ⟨0,by
      have : 15 ≤ n := by nlinarith
      omega⟩).val = ((n-3 : ℕ) : ZMod n) := by
    have hnonempty : 0 < n-1 := by
      have hnlarge : 15 ≤ n := by nlinarith
      omega
    exact (S.directedTerrace_first hnonempty).trans hfirst
  have hcalendar : S.directedTerrace.word =
      [2,3,10,n-14,12] ++ Construction.prefixGaps n r ++ pathGaps S.completion := by
    rw [S.directedTerrace_word]
    change pathGaps P.path ++ pathGaps S.completion = _
    rw [hpath, Construction.prefixPath_pathGaps hr hlarge]
  exact PhysicalTransfer.directed_prefix_asymmetric_orbits S.directedTerrace hr hn hlarge
    (pathGaps S.completion) hstart hcalendar

/-- The actual orbit family is contained in the full census of asymmetric
optimal corrals. -/
theorem literal_prefix_census_of_completion {h n r : ℕ}
    [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
    (hr : 3 ≤ r) (hn : n = 2*h-1) (hlarge : 200*r*r ≤ n)
    (P : RainbowPrefix n) (Q : P.ComplementaryPath)
    (hpath : P.path = Construction.prefixPath n r) :
    latinSquareCount r ^ h ≤ PhysicalCensus.A_h h
      (height_ge_two (r := r) (by omega) hn (by nlinarith)) := by
  have hh : 2 ≤ h := height_ge_two (r := r) (by omega) hn (by nlinarith)
  obtain ⟨C,hcount,ha⟩ := literal_prefix_orbits_of_completion hr hn hlarge P Q hpath
  have hc := PhysicalCensus.full_orbit_image_le_all (optimal_width (NeZero.pos h) hn) C ha
  rw [hcount] at hc
  rw [PhysicalCensus.A_h_eq hh hn]
  exact hc

end
end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
