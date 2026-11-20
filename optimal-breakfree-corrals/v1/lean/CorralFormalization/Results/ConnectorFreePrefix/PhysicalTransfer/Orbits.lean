import CorralFormalization.Results.ConnectorFreePrefix.PhysicalTransfer.BodyFrame
import CorralFormalization.DiversityCompletion.CanonicalTailOrbits

/-!
# Actual invariant tails, physical rigidity, and the connector-free count

The source-calendar/L14 `BodyInput` still has to be supplied by the actual
prefix.  Under that narrow interface, neither a physical partition nor
unlabelled injectivity nor asymmetry is assumed.  The conclusions count
full physical dihedral orbits of actual `CorralRows`, not labelled rows.
-/

namespace CorralFormalization.LatinCompletion.ConnectorFreePhysical

open LatinTransfer TerraceLift LatinPrefix PhaseTiling
open CorralLatinTailMarker PhysicalCorral DiversitySymmetry

namespace Frame

variable {h n r : ℕ} [NeZero r] {D : Coordinates r} (G : Frame h n D)

/-- All potential gap-n tails are computed from the fixed gap pieces. -/
def tailPositions (q : ZMod h) : Finset (ZMod (h*n)) :=
  physicalOffsets (h*n) (G.origin q) (fixedGapOffsets D.cellA D.cellB n (G.pieces q))

/-- The actual clockwise gap-n tails survive all Latin choices.  This uses
positive one-turn geometry and the strict upper bounds on both changed gaps. -/
theorem gap_n_tails [NeZero (h*n)] (hr : 3 ≤ r) (hlarge : 200*r*r ≤ n)
    (L : Family h r) (q : ZMod h) :
    gapTails (G.row L q) n=G.tailPositions q := by
  have hclen : (cells (G.pieces q)).length=r*r := by
    simpa using (G.cells_complete q).length_eq
  have hlen : 2 ≤ (word D.cellA D.cellB (D.choice L q) (G.pieces q)).length := by
    rw [word_length,hclen]; nlinarith
  have hin (i : Cell r) : D.cellA i+D.choice L q i ≠ n := by
    rcases D.local_gap_geometry hr hlarge i.1 i.2
      ((L (q+D.offset h i.1)).entry i.1 i.2) with ⟨_,_,_,_,_,_,ht,_,_⟩
    exact Nat.ne_of_lt ht
  have hout (i : Cell r) : D.cellB i-D.choice L q i ≠ n := by
    rcases D.local_gap_geometry hr hlarge i.1 i.2
      ((L (q+D.offset h i.1)).entry i.1 i.2) with ⟨_,_,_,_,_,_,_,_,ht⟩
    exact Nat.ne_of_lt ht
  rw [row,gapTails_physicalOffsets _ _ (G.word_positive hr L q)
    (G.word_winding hr L q) hlen n,
    gapOffsets_word_eq_fixed _ _ _ n _ (fun i => (choice_lt hr L q i).le) hin hout]
  rfl

def allTailPositions [NeZero h] : Finset (ZMod (h*n)) := Finset.univ.biUnion G.tailPositions

theorem actual_family_tails [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r)
    (hlarge : 200*r*r ≤ n) (L : Family h r) :
    actualFamilyTails h n (G.unlabelled L)=G.allTailPositions := by
  simp only [actualFamilyTails,unlabelled,Finset.image_biUnion,allTailPositions]
  apply Finset.biUnion_congr rfl
  intro q _
  exact G.gap_n_tails hr hlarge L q

/-- The natural-representative adapter realizes exactly this H4 family. -/
theorem completed_realized [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r)
    (hlarge : 200*r*r ≤ n) (B : G.FullBaseline) (hn : n=2*h-1) (L : Family h r) :
    realizedFamily (G.completed hr hlarge B hn L)=G.unlabelled L := by
  unfold realizedFamily unlabelled
  simp_rw [G.completed_sites hr hlarge B hn L]
  exact naturalRows_realized (G.row L)

/-- The gap-n tail marker proves all inter-member motions trivial.  The
partition, palettes and H4 decoder are derived from a single baseline. -/
theorem one_three_tile_orbits [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r)
    (hn : n=2*h-1) (hlarge : 200*r*r ≤ n) (B : G.FullBaseline)
    (A : Finset (ZMod (h*n))) (p : ZMod (h*n))
    (hstarts : ∀ x ∈ A ∪ {p}, CorralLatinTailMarker.residueMap h n x=0)
    (htiles : G.allTailPositions=tileTails A {p}) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q=naturalRows (G.row L) q) ∧
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card=
        latinSquareCount r^h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  have hn' : n+1=2*h := by have := NeZero.pos h; omega
  have hz : 7 ≤ n ∧ 7 ≤ h := by constructor <;> nlinarith
  have hh : r*r ≤ h := by nlinarith
  have hT (L : Family h r) : actualFamilyTails h n (G.unlabelled L)=tileTails A {p} :=
    (G.actual_family_tails hr hlarge L).trans htiles
  obtain ⟨hres,ha,ha2,hunique⟩ := one_three_tile_marker hz.1 A p hstarts
  have hc := unique_tail_family_orbits hz.1 (actualTailExtractor h n) G.unlabelled
    (G.unlabelled_injective hr hlarge hh B) _ hT hres
    (p-(n : ZMod (h*n))+2) ha ha2 hunique
  refine ⟨G.completed hr hlarge B hn,G.completed_sites hr hlarge B hn,?_,?_⟩
  · simpa only [G.completed_realized hr hlarge B hn] using hc.1.trans (latinFamily_card h r)
  · intro L
    rw [G.completed_realized hr hlarge B hn]
    exact hc.2 L

/-- Even heights use two consecutive three-tiles.  Their residue-2 tails
are separated by three phases and exclude every nonzero rotation. -/
theorem two_three_tile_orbits [NeZero h] [NeZero (h*n)] (hr : 3 ≤ r)
    (hn : n=2*h-1) (hlarge : 200*r*r ≤ n) (B : G.FullBaseline)
    (A : Finset (ZMod (h*n))) (p : ZMod (h*n))
    (hstarts : ∀ x ∈ A ∪ {p,p-3*(n : ZMod (h*n))}, CorralLatinTailMarker.residueMap h n x=0)
    (htiles : G.allTailPositions=tileTails A {p,p-3*(n : ZMod (h*n))}) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q=naturalRows (G.row L) q) ∧
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card=
        latinSquareCount r^h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  have hn' : n+1=2*h := by have := NeZero.pos h; omega
  have hz : 7 ≤ n ∧ 7 ≤ h := by constructor <;> nlinarith
  have hh : r*r ≤ h := by nlinarith
  have hT (L : Family h r) : actualFamilyTails h n (G.unlabelled L)=
      tileTails A {p,p-3*(n : ZMod (h*n))} := (G.actual_family_tails hr hlarge L).trans htiles
  obtain ⟨hres,hpair⟩ := two_three_tile_marker hz.1 A p hstarts
  have hc := two_tail_family_orbits hz.1 hz.2 (actualTailExtractor h n) G.unlabelled
    (G.unlabelled_injective hr hlarge hh B) _ hT hres
    (p-3*(n : ZMod (h*n))-(n : ZMod (h*n))+2) hpair
  refine ⟨G.completed hr hlarge B hn,G.completed_sites hr hlarge B hn,?_,?_⟩
  · simpa only [G.completed_realized hr hlarge B hn] using hc.1.trans (latinFamily_card h r)
  · intro L
    rw [G.completed_realized hr hlarge B hn]
    exact hc.2 L

end Frame

namespace BodyInput

variable {h n r : ℕ} [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
variable {T : CompletedTerrace n} {D : Coordinates r} (P : BodyInput T D)

/-- Literal tile-tail equality is inherited from the *proved* baseline
family identification.  No tail pattern is input to this theorem. -/
theorem schedule_allTailPositions (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) :
    (P.scheduleFrame hr hn hlarge htotal).allTailPositions=
      tileTails (phaseStarts h n (pairPhases h m k)) (phaseStarts h n (triplePhases h m k)) := by
  let G := P.scheduleFrame hr hn hlarge htotal
  calc
    G.allTailPositions=actualFamilyTails h n (G.unlabelled (cyclicLatinFamily h r)) :=
      (G.actual_family_tails hr hlarge (cyclicLatinFamily h r)).symm
    _ = actualFamilyTails h n (T.globalFamily (h := h) m k) :=
      congrArg (actualFamilyTails h n) (P.schedule_family_eq hr hn hlarge htotal)
    _ = _ := global_tile_tails T hn (by nlinarith) m k

include P

theorem one_triple_body_orbits (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {k : ℕ} (htotal : h=3*1+2*k) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card=
        latinSquareCount r^h ∧ ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  let G := P.scheduleFrame hr hn hlarge htotal
  let B := P.scheduleBaseline hr hn hlarge htotal
  obtain ⟨C,hrows,hcount,hasym⟩ := G.one_three_tile_orbits hr hn hlarge B
    (phaseStarts h n (pairPhases h 1 k)) (zeroSite h n (2 : ZMod h))
    (one_three_tile_phase_starts (pairPhases h 1 k) (2 : ZMod h))
    (by rw [P.schedule_allTailPositions hr hn hlarge htotal,triple_starts_one])
  exact ⟨C,hcount,hasym⟩

theorem two_triple_body_orbits (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    {k : ℕ} (htotal : h=3*2+2*k) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card=
        latinSquareCount r^h ∧ ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  let G := P.scheduleFrame hr hn hlarge htotal
  let B := P.scheduleBaseline hr hn hlarge htotal
  obtain ⟨C,hrows,hcount,hasym⟩ := G.two_three_tile_orbits hr hn hlarge B
    (phaseStarts h n (pairPhases h 2 k)) (zeroSite h n (5 : ZMod h))
    (two_three_tile_phase_starts (pairPhases h 2 k) (5 : ZMod h))
    (by rw [P.schedule_allTailPositions hr hn hlarge htotal,triple_starts_two])
  exact ⟨C,hcount,hasym⟩

/-- For the actual connector-free geometry, an exact calendar and L14 lift
supply one asymmetric full physical orbit for each h-tuple of Latin squares.
This theorem is conditional on `BodyInput`, not an unconditional diversity
or prefix-completion theorem. -/
theorem canonical_body_orbits (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card=
        latinSquareCount r^h ∧ ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  have ht := canonical_total (height_large hr hn hlarge)
  by_cases ho : h%2=1
  · have hm : canonicalTriples h=1 := by simp [canonicalTriples,ho]
    have htotal : h=3*1+2*canonicalPairs h := by simpa [hm] using ht
    exact P.one_triple_body_orbits hr hn hlarge htotal
  · have hm : canonicalTriples h=2 := by simp [canonicalTriples,ho]
    have htotal : h=3*2+2*canonicalPairs h := by simpa [hm] using ht
    exact P.two_triple_body_orbits hr hn hlarge htotal

end BodyInput
end CorralFormalization.LatinCompletion.ConnectorFreePhysical
