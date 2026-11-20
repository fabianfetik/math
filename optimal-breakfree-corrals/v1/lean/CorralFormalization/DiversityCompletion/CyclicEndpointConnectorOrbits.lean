import CorralFormalization.DiversityCompletion.CyclicEndpointInvariants
import CorralFormalization.DiversityCompletion.LatinConnectorRainbowPrefix
import CorralFormalization.DiversityCompletion.ConnectorSpliceOrbits
import CorralFormalization.DiversityCompletion.OptimalCorralCensus

/-! The actual connector-prefix prefix and the physical orbit construction, using a
single explicit endpoint-completion hypothesis at the required size. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply
  LatinPrefixSupply.FixedConnectorPrefix CorralLatinTailMarker PhysicalCorral

theorem height_ge_two {h n r : ℕ} (hr : 2 ≤ r)
    (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n) : 2 ≤ h := by
  have hs : 4 ≤ r*r := by nlinarith
  have hnlarge : 400 ≤ n := by nlinarith
  omega

theorem endpoint_hypothesis_asymmetric_orbits {h n r : ℕ}
    [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (H : EndpointCompletionAt n (4*r*r+6)) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  have hodd : Odd n := by
    have hh : 0 < h := Nat.pos_of_ne_zero (NeZero.ne h)
    refine ⟨h-1, ?_⟩
    omega
  obtain ⟨y,P,hy,hpath,hfirst,hgap⟩ := connectorPrefix_rainbowPrefix_exists hr hlarge
  have ht : P.path.length-1 ≤ 4*r*r+6 := by
    rw [hpath, connectorPrefixPath_length]
    omega
  obtain ⟨Q⟩ := P.complementaryPath_of_endpoint hodd ht H
  exact spliced_connectorPrefix_asymmetric_orbits (P.splice Q) hr hn hlarge y hy hfirst hgap

/-- The constructed orbits are included in the actual total census A_h. -/
theorem endpoint_hypothesis_total_lower {h n r : ℕ}
    [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (H : EndpointCompletionAt n (4*r*r+6)) :
    latinSquareCount r ^ h ≤ PhysicalCensus.A_h h (height_ge_two hr hn hlarge) := by
  have hh : 2 ≤ h := height_ge_two hr hn hlarge
  obtain ⟨C,hcount,ha⟩ := endpoint_hypothesis_asymmetric_orbits hr hn hlarge H
  have hc := PhysicalCensus.full_orbit_image_le_all (optimal_width (NeZero.pos h) hn) C ha
  rw [hcount] at hc
  rw [PhysicalCensus.A_h_eq hh hn]
  exact hc

/-- The exact factorial-family lower bound follows from the quantified
endpoint hypothesis whenever the explicit connector-prefix path fits its deletion budget. -/
theorem oddCyclicEndpointCompletion_total_lower (H : OddCyclicRainbowEndpointCompletion) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      ∀ (h n r : ℕ) [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
        (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n),
        n0 ≤ n → ((4*r*r+6 : ℕ) : ℝ) ≤ ε0*(n : ℝ) →
        latinSquareCount r ^ h ≤ PhysicalCensus.A_h h (height_ge_two hr hn hlarge) := by
  obtain ⟨ε0,he,n0,Hlocal⟩ := oddCyclicEndpointCompletion_local H
  refine ⟨ε0,he,n0,?_⟩
  intro h n r ih in' ir ihn hr hn hlarge hn0 hbudget
  have hodd : Odd n := by
    have hh : 0 < h := Nat.pos_of_ne_zero (NeZero.ne h)
    refine ⟨h-1, ?_⟩
    omega
  have ht : 4*r*r+6 ≤ n := by nlinarith
  exact endpoint_hypothesis_total_lower hr hn hlarge
    (Hlocal n (4*r*r+6) hodd hn0 ht hbudget)

end CorralFormalization.LatinCompletion.TerraceCompletion
