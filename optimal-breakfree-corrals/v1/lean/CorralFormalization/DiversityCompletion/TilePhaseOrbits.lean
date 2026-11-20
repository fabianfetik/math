import CorralFormalization.DiversityCompletion.RealizedCorralOrbits
import CorralFormalization.DiversityCompletion.TerraceLift

/-! Joining the actual zero-column phase sites of the global terrace lift
to the previously proved physical orbit count. The remaining tile input is
the literal equality between the frame's computed tails and the tile tails. -/

namespace CorralFormalization.LatinCompletion

open LatinTransfer CorralLatinTailMarker PhysicalCorral

variable {h n r : ℕ}

def phaseStarts (h n : ℕ) (P : Finset (ZMod h)) : Finset (ZMod (h*n)) :=
  P.image (TerraceLift.zeroSite h n)

theorem zeroSite_residue_on_marker (q : ZMod h) :
    residueMap h n (TerraceLift.zeroSite h n q) = 0 := by
  exact TerraceLift.zeroSite_residue h n q

theorem phaseStarts_residue (P : Finset (ZMod h)) (x : ZMod (h*n))
    (hx : x ∈ phaseStarts h n P) : residueMap h n x = 0 := by
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
  exact zeroSite_residue_on_marker q

theorem one_three_tile_phase_starts (P : Finset (ZMod h)) (q : ZMod h) :
    ∀ x ∈ phaseStarts h n P ∪ {TerraceLift.zeroSite h n q}, residueMap h n x = 0 := by
  intro x hx
  rcases Finset.mem_union.mp hx with hp | hq
  · exact phaseStarts_residue P x hp
  · have he : x = TerraceLift.zeroSite h n q := Finset.mem_singleton.mp hq
    rw [he]
    exact zeroSite_residue_on_marker q

theorem two_three_tile_phase_starts (P : Finset (ZMod h)) (q : ZMod h) :
    ∀ x ∈ phaseStarts h n P ∪
        {TerraceLift.zeroSite h n q, TerraceLift.zeroSite h n q - 3 * (n : ZMod (h*n))},
      residueMap h n x = 0 := by
  intro x hx
  rcases Finset.mem_union.mp hx with hp | hq
  · exact phaseStarts_residue P x hp
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with he | he
    · rw [he]
      exact zeroSite_residue_on_marker q
    · rw [he, map_sub, map_mul, zeroSite_residue_on_marker]
      simp [residueMap]

variable [NeZero h] [NeZero (h*n)]

/-- Valid asymmetric corrals and their exact Latin orbit count, with the
tile starts now taken from actual zero-column phases. -/
theorem PhysicalFrame.one_three_tile_phase_orbits
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (G : PhysicalFrame h n r) (B : G.FullBaseline)
    (P : Finset (ZMod h)) (q : ZMod h)
    (htiles : G.allTailPositions =
      tileTails (phaseStarts h n P) {TerraceLift.zeroSite h n q}) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) :=
  G.one_three_tile_realized_orbits hr hn hlarge B (phaseStarts h n P)
    (TerraceLift.zeroSite h n q) (one_three_tile_phase_starts P q) htiles

theorem PhysicalFrame.two_three_tile_phase_orbits
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (G : PhysicalFrame h n r) (B : G.FullBaseline)
    (P : Finset (ZMod h)) (q : ZMod h)
    (htiles : G.allTailPositions = tileTails (phaseStarts h n P)
      {TerraceLift.zeroSite h n q, TerraceLift.zeroSite h n q - 3 * (n : ZMod (h*n))}) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) :=
  G.two_three_tile_realized_orbits hr hn hlarge B (phaseStarts h n P)
    (TerraceLift.zeroSite h n q) (two_three_tile_phase_starts P q) htiles

end CorralFormalization.LatinCompletion
