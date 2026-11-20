import CorralFormalization.DiversityCompletion.TailMarker
import CorralFormalization.DiversityCompletion.LatinCorralConstruction

/-!
Joining the explicit positive-gap frame to the physical dihedral count.

This proves the valid-corral conclusion from one valid physical baseline,
the literal frame and the *actual* gap-n tail data.  It does not construct
the frame or the tail pattern from a completed residue terrace.
-/

namespace CorralFormalization.LatinCompletion

open LatinTransfer CorralLatinTailMarker PhysicalCorral

variable {h n r : ℕ} [NeZero h] [NeZero (h * n)]

omit [NeZero (h * n)] in
private theorem frame_arithmetic (hr : 2 ≤ r) (hn : n = 2 * h - 1)
    (hlarge : 100 * r * r ≤ n) :
    21 * r * r + 2 * r ≤ n ∧ 2 * r * r ≤ h := by
  have hh : 0 < h := Nat.pos_of_ne_zero (NeZero.ne h)
  have hn' : n + 1 = 2 * h := by omega
  have hsq : 2 * r ≤ r * r := by nlinarith
  constructor <;> nlinarith

/-- A one-tail marker gives exactly one asymmetric physical orbit per
Latin family, and each counted family is an actual optimal corral. -/
theorem PhysicalFrame.one_tail_valid_corral_orbits
    (hr : 2 ≤ r) (hn : n = 2 * h - 1) (hlarge : 100 * r * r ≤ n)
    (G : PhysicalFrame h n r) (B : G.FullBaseline)
    (T : Finset (ZMod (h * n)))
    (hT : ∀ L : Family h r, actualFamilyTails h n (G.unlabelled L) = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h * n)) (ha : anchor ∈ T) (ha2 : residueMap h n anchor = 2)
    (hunique : ∀ x ∈ T, residueMap h n x = 2 → x = anchor) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q = naturalRows (G.row L) q) ∧
      (Finset.univ.image (fun L : Family h r => physicalOrbit (G.unlabelled L))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (G.unlabelled L) := by
  have hs := frame_arithmetic hr hn hlarge
  have hz := connectorPrefix_markerSizeBounds hr hn hlarge
  have hi : Function.Injective G.unlabelled := G.unlabelled_injective hr hlarge hs.1 B hs.2
  have hc := unique_tail_family_orbits hz.1 (actualTailExtractor h n)
    G.unlabelled hi T hT hres anchor ha ha2 hunique
  refine ⟨G.completed hr hlarge hs.1 B hn, ?_, hc.1.trans (latinFamily_card h r), hc.2⟩
  intro L q
  exact G.completed_sites hr hlarge hs.1 B hn L q

/-- The corresponding actual-corral and orbit theorem for the two tails
separated by three phases. -/
theorem PhysicalFrame.two_tail_valid_corral_orbits
    (hr : 2 ≤ r) (hn : n = 2 * h - 1) (hlarge : 100 * r * r ≤ n)
    (G : PhysicalFrame h n r) (B : G.FullBaseline)
    (T : Finset (ZMod (h * n)))
    (hT : ∀ L : Family h r, actualFamilyTails h n (G.unlabelled L) = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h * n))
    (hpair : T.filter (fun x => residueMap h n x = 2) =
      {anchor, anchor + ((3 * n : ℕ) : ZMod (h * n))}) :
    ∃ C : Family h r → CorralRows h n,
      (∀ L q, (C L).sites q = naturalRows (G.row L) q) ∧
      (Finset.univ.image (fun L : Family h r => physicalOrbit (G.unlabelled L))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (G.unlabelled L) := by
  have hs := frame_arithmetic hr hn hlarge
  have hz := connectorPrefix_markerSizeBounds hr hn hlarge
  have hi : Function.Injective G.unlabelled := G.unlabelled_injective hr hlarge hs.1 B hs.2
  have hc := two_tail_family_orbits hz.1 hz.2 (actualTailExtractor h n)
    G.unlabelled hi T hT hres anchor hpair
  refine ⟨G.completed hr hlarge hs.1 B hn, ?_, hc.1.trans (latinFamily_card h r), hc.2⟩
  intro L q
  exact G.completed_sites hr hlarge hs.1 B hn L q

end CorralFormalization.LatinCompletion
