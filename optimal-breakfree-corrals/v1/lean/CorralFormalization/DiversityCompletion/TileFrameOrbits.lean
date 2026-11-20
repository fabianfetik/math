import CorralFormalization.DiversityCompletion.TailInvariance
import CorralFormalization.DiversityCompletion.FrameOrbits
import CorralFormalization.DiversityCompletion.TileMarkers

/-!
Physical Latin corrals and their exact orbit count from a single baseline,
one positive gap frame, and the actual two-tile and three-tile tail formulas.

The remaining supplier is the construction of such a frame and the
literal tile-tail identity from the manuscript's completed residue terrace.
-/

namespace CorralFormalization.LatinCompletion

open LatinTransfer CorralLatinTailMarker PhysicalCorral

variable {h n r : ℕ} [NeZero h] [NeZero (h*n)]

/-- Odd-layout interface: the concrete tails are those of any collection
of two-tiles and one three-tile. -/
theorem PhysicalFrame.one_three_tile_corrals
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (G : PhysicalFrame h n r) (B : G.FullBaseline)
    (A : Finset (ZMod (h*n))) (p : ZMod (h*n))
    (hstarts : ∀ x ∈ A ∪ {p}, residueMap h n x = 0)
    (htiles : G.allTailPositions = tileTails A {p}) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q = naturalRows (G.row L) q) ∧
      (Finset.univ.image (fun L : Family h r => physicalOrbit (G.unlabelled L))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (G.unlabelled L) := by
  have hz := connectorPrefix_markerSizeBounds hr hn hlarge
  have hT (L : Family h r) : actualFamilyTails h n (G.unlabelled L) = tileTails A {p} := by
    change (G.unlabelled L).biUnion (fun R => CorralFormalization.DiversitySymmetry.gapTails R n) = _
    exact (G.actual_family_tails hr hlarge L).trans htiles
  obtain ⟨hres, ha, ha2, hunique⟩ := one_three_tile_marker hz.1 A p hstarts
  exact G.one_tail_valid_corral_orbits hr hn hlarge B (tileTails A {p}) hT
    hres (p - (n : ZMod (h*n)) + 2) ha ha2 hunique

/-- Even-layout interface: the two three-tiles start three phases apart. -/
theorem PhysicalFrame.two_three_tile_corrals
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (G : PhysicalFrame h n r) (B : G.FullBaseline)
    (A : Finset (ZMod (h*n))) (p : ZMod (h*n))
    (hstarts : ∀ x ∈ A ∪ {p, p - 3 * (n : ZMod (h*n))}, residueMap h n x = 0)
    (htiles : G.allTailPositions = tileTails A {p, p - 3 * (n : ZMod (h*n))}) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q = naturalRows (G.row L) q) ∧
      (Finset.univ.image (fun L : Family h r => physicalOrbit (G.unlabelled L))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (G.unlabelled L) := by
  have hz := connectorPrefix_markerSizeBounds hr hn hlarge
  have hT (L : Family h r) : actualFamilyTails h n (G.unlabelled L) =
      tileTails A {p, p - 3 * (n : ZMod (h*n))} := by
    change (G.unlabelled L).biUnion (fun R => CorralFormalization.DiversitySymmetry.gapTails R n) = _
    exact (G.actual_family_tails hr hlarge L).trans htiles
  obtain ⟨hres, hpair⟩ := two_three_tile_marker hz.1 A p hstarts
  exact G.two_tail_valid_corral_orbits hr hn hlarge B _ hT hres
    (p - 3 * (n : ZMod (h*n)) - (n : ZMod (h*n)) + 2) hpair

end CorralFormalization.LatinCompletion
