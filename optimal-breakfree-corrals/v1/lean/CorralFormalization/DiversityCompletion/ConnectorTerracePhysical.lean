import CorralFormalization.DiversityCompletion.LatinConnectorPrefix
import CorralFormalization.DiversityCompletion.CanonicalTailOrbits

/-! The physical Latin construction from an actual completed terrace
whose difference calendar contains the explicit connector-prefix/connector prefix.
This does not assert the existence of the connectors or the terrace. -/

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply

open LatinTransfer TerraceLift LatinPrefix CorralLatinTailMarker PhysicalCorral

theorem connectorPrefix_terrace_asymmetric_orbits {h n r : ℕ} [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
    (T : CompletedTerrace n) (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (suffix : List ℕ) (hcalendar : T.body = connectorPrefixGaps n y ++ suffix) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) :=
  canonical_body_orbits (bodyInputOfConnectorPrefix T hr hlarge y hy suffix hcalendar) hr hn hlarge

end CorralFormalization.LatinCompletion.LatinPrefixSupply
