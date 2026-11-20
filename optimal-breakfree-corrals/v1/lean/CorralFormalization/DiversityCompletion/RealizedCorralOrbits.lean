import CorralFormalization.DiversityCompletion.TileFrameOrbits

/-! The counted physical families are exactly the sites of the constructed
`CorralRows`, on the same clock on which the dihedral group acts. -/

namespace CorralFormalization.LatinCompletion

open LatinTransfer CorralLatinTailMarker PhysicalCorral

variable {h n r : ℕ} [NeZero h] [NeZero (h*n)]

def realizedFamily (C : CorralRows h n) : PhysicalFamily h n :=
  Finset.univ.image (fun q : Fin h => physicalSites (h*n) (C.sites q))

theorem naturalRows_realized (R : ZMod h → Finset (ZMod (h*n))) :
    Finset.univ.image (fun q : Fin h => physicalSites (h*n) (naturalRows R q)) =
      Finset.univ.image R := by
  classical
  have hid (q : Fin h) : physicalSites (h*n) (naturalRows R q) = R (q.val : ZMod h) := by
    simp only [physicalSites, naturalRows, Finset.image_image, Function.comp_def,
      ZMod.natCast_zmod_val, Finset.image_id']
  simp_rw [hid]
  ext S
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨(q.val : ZMod h), hq⟩
  · rintro ⟨q, hq⟩
    refine ⟨⟨q.val, ZMod.val_lt q⟩, ?_⟩
    simpa using hq

theorem realizedFamily_of_rows (G : PhysicalFrame h n r) (C : Family h r → CorralRows h n)
    (hrows : ∀ L q, (C L).sites q = naturalRows (G.row L) q) (L : Family h r) :
    realizedFamily (C L) = G.unlabelled L := by
  unfold realizedFamily PhysicalFrame.unlabelled
  simp_rw [hrows L]
  exact naturalRows_realized (G.row L)

/-- The odd-layout count is literally a count of physical orbits of
constructed `CorralRows`, rather than merely a count of abstract row families. -/
theorem PhysicalFrame.one_three_tile_realized_orbits
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (G : PhysicalFrame h n r) (B : G.FullBaseline)
    (A : Finset (ZMod (h*n))) (p : ZMod (h*n))
    (hstarts : ∀ x ∈ A ∪ {p}, residueMap h n x = 0)
    (htiles : G.allTailPositions = tileTails A {p}) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  obtain ⟨C, hrows, hcount, hasym⟩ := G.one_three_tile_corrals hr hn hlarge B A p hstarts htiles
  have heq : ∀ L, realizedFamily (C L) = G.unlabelled L := realizedFamily_of_rows G C hrows
  refine ⟨C, ?_, ?_⟩
  · simpa only [heq] using hcount
  · intro L
    rw [heq L]
    exact hasym L

/-- The corresponding literal count for two consecutive three-tiles. -/
theorem PhysicalFrame.two_three_tile_realized_orbits
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (G : PhysicalFrame h n r) (B : G.FullBaseline)
    (A : Finset (ZMod (h*n))) (p : ZMod (h*n))
    (hstarts : ∀ x ∈ A ∪ {p, p - 3 * (n : ZMod (h*n))}, residueMap h n x = 0)
    (htiles : G.allTailPositions = tileTails A {p, p - 3 * (n : ZMod (h*n))}) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  obtain ⟨C, hrows, hcount, hasym⟩ := G.two_three_tile_corrals hr hn hlarge B A p hstarts htiles
  have heq : ∀ L, realizedFamily (C L) = G.unlabelled L := realizedFamily_of_rows G C hrows
  refine ⟨C, ?_, ?_⟩
  · simpa only [heq] using hcount
  · intro L
    rw [heq L]
    exact hasym L

end CorralFormalization.LatinCompletion
