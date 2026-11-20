import CorralFormalization.DiversityCompletion.EndpointSplice
import CorralFormalization.DiversityCompletion.ConnectorTerracePhysical

/-! A real complementary endpoint path plus the explicit connector-prefix prefix gives
the complete physical Latin-corral orbit conclusion. The existence of the
prefix and endpoint path is not asserted here. -/

namespace CorralFormalization.LatinCompletion.TerraceCompletion

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply CorralLatinTailMarker PhysicalCorral

theorem spliced_connectorPrefix_asymmetric_orbits {h n r : ℕ} [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
    (S : EndpointSpliceInput n) (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (hfirst : S.first = ((n-3 : ℕ) : ZMod n))
    (hprefix : pathGaps S.prefixPath = [2,3,10,n-14,12] ++ connectorPrefixGaps n y) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  let T := S.completedConnectorPrefix (by nlinarith) y hfirst hprefix
  exact connectorPrefix_terrace_asymmetric_orbits T hr hn hlarge y hy (pathGaps S.completion) rfl

end CorralFormalization.LatinCompletion.TerraceCompletion
