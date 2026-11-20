import CorralFormalization.Results.ConnectorFreePrefix.PhysicalTransfer.Orbits
import CorralFormalization.Results.ConnectorFreePrefix.Construction.PrefixChain
import CorralFormalization.DiversityCompletion.DirectedTerraceCompletion

/-!
# The explicit connector-free prefix supplies the physical body interface

`Construction.prefixPieces_position` proves L14 from the actual one-wrap
joins.  This adapter supplies all remaining fields of the source-body input.
The final theorem remains conditional on an actual directed terrace whose
positive difference calendar retains the explicit prefix.  No physical
partition, site injectivity, cyclic edge certificate, or asymmetry is input.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.PhysicalTransfer

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply ConnectorFreePhysical

variable {n r : ℕ} [NeZero r]

/-- The source body is the concrete direct-join calendar, with an arbitrary
completion suffix.  The suffix's positivity is derived from the terrace. -/
def bodyInputOfPrefixCalendar (T : CompletedTerrace n) (hr : 3 ≤ r)
    (hlarge : 200*r*r ≤ n) (suffix : List ℕ)
    (hcalendar : T.body=Construction.prefixGaps n r++suffix) :
    ConnectorFreePhysical.BodyInput T (waleckiCoordinates r) where
  pieces := Construction.prefixPieces n r suffix
  fixed_positive d hd := by
    have hm : d ∈ word Construction.prefixA Construction.prefixB canonicalSymbol
        (Construction.prefixPieces n r suffix) :=
      List.mem_flatMap.mpr ⟨Piece.fixed d,hd,by simp [Piece.gaps]⟩
    rw [Construction.prefixPieces_word,← hcalendar] at hm
    exact completed_body_positive T d hm
  cells_complete := Construction.prefixPieces_cells n r suffix
  calendar := by
    change T.body=word Construction.prefixA Construction.prefixB canonicalSymbol
      (Construction.prefixPieces n r suffix)
    rw [Construction.prefixPieces_word,hcalendar]
  position := Construction.prefixPieces_position hr hlarge suffix

/-- Turn an actual directed terrace into the common-lift representation,
retaining its literal calendar.  This is independent of Latin choices. -/
def completedOfDirectedPrefix [NeZero n] (T : DirectedTerrace n) (hn : 15 ≤ n)
    (suffix : List ℕ)
    (hstart : (T.vertices ⟨0,by omega⟩).val=((n-3 : ℕ) : ZMod n))
    (hcalendar : T.word=[2,3,10,n-14,12]++Construction.prefixGaps n r++suffix) :
    CompletedTerrace n :=
  completedOfDirected T hn (Construction.prefixGaps n r++suffix) hstart
    (by simpa only [List.append_assoc] using hcalendar)

/-- The physical source-body input is fully constructed from the actual
terrace and its retained concrete calendar.  In particular, L14 is not an
extra premise. -/
def bodyInputOfDirectedPrefix [NeZero n] (T : DirectedTerrace n) (hr : 3 ≤ r)
    (hlarge : 200*r*r ≤ n) (suffix : List ℕ)
    (hstart : (T.vertices ⟨0,by
      have hsmall : 15 ≤ n := by nlinarith
      omega⟩).val=((n-3 : ℕ) : ZMod n))
    (hcalendar : T.word=[2,3,10,n-14,12]++Construction.prefixGaps n r++suffix) :
    ConnectorFreePhysical.BodyInput
      (completedOfDirectedPrefix T (by nlinarith) suffix hstart hcalendar) (waleckiCoordinates r) :=
  bodyInputOfPrefixCalendar _ hr hlarge suffix rfl

/-- End-to-end physical transfer for the explicit prefix: every actual
directed terrace retaining its calendar yields exactly `L_r^h` asymmetric
full physical dihedral orbits of constructed optimal `CorralRows`.

Existence of the completed directed terrace remains an explicit premise.
The statement does not assert the unconditional all-height lower bound. -/
theorem directed_prefix_asymmetric_orbits {h : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (T : DirectedTerrace n) (hr : 3 ≤ r) (hn : n=2*h-1) (hlarge : 200*r*r ≤ n)
    (suffix : List ℕ)
    (hstart : (T.vertices ⟨0,by
      have hsmall : 15 ≤ n := by nlinarith
      omega⟩).val=((n-3 : ℕ) : ZMod n))
    (hcalendar : T.word=[2,3,10,n-14,12]++Construction.prefixGaps n r++suffix) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r =>
        CorralLatinTailMarker.physicalOrbit (realizedFamily (C L)))).card=
          CorralLatinTailMarker.latinSquareCount r^h ∧
      ∀ L, PhysicalCorral.PhysicallyAsymmetric (realizedFamily (C L)) := by
  let P := bodyInputOfDirectedPrefix T hr hlarge suffix hstart hcalendar
  exact P.canonical_body_orbits hr hn hlarge

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.PhysicalTransfer
