import CorralFormalization.DiversityCompletion.CanonicalLatinFrame
import CorralFormalization.DiversityCompletion.TilePhaseOrbits

namespace CorralFormalization.LatinCompletion.LatinPrefix

open LatinTransfer TerraceLift PhaseTiling CorralLatinTailMarker PhysicalCorral DiversitySymmetry

def pairPhases (h m k : ℕ) : Finset (ZMod h) :=
  Finset.univ.image (fun j : Fin k => top h (.inr j : TileIndex m k))

def triplePhases (h m k : ℕ) : Finset (ZMod h) :=
  Finset.univ.image (fun i : Fin m => top h (.inl i : TileIndex m k))

theorem sum_biUnion {I J X : Type*} [Fintype I] [Fintype J] [DecidableEq X]
    (f : I ⊕ J → Finset X) :
    Finset.univ.biUnion f = (Finset.univ.biUnion (fun i : I => f (.inl i))) ∪
      Finset.univ.biUnion (fun j : J => f (.inr j)) := by
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_union,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | inl i => exact Or.inl ⟨i,hi⟩
    | inr j => exact Or.inr ⟨j,hi⟩
  · rintro (⟨i,hi⟩ | ⟨j,hj⟩)
    · exact ⟨.inl i,hi⟩
    · exact ⟨.inr j,hj⟩

theorem biUnion_pair {I X : Type*} [Fintype I] [DecidableEq X] (f g : I → X) :
    Finset.univ.biUnion (fun i => ({f i,g i} : Finset X)) =
      Finset.univ.image f ∪ Finset.univ.image g := by
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_union,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_insert,Finset.mem_singleton]
  aesop

theorem biUnion_triple {I X : Type*} [Fintype I] [DecidableEq X] (f g l : I → X) :
    Finset.univ.biUnion (fun i => ({f i,g i,l i} : Finset X)) =
      Finset.univ.image f ∪ Finset.univ.image g ∪ Finset.univ.image l := by
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_union,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_insert,Finset.mem_singleton]
  aesop

section ActualTails

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

theorem local_two_tails (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (j : Fin k) :
    (T.tileRows (h := h) (.inr j : TileIndex m k)).biUnion (fun R => gapTails R n) =
      {zeroSite h n (top h (.inr j : TileIndex m k))-1,
       zeroSite h n (top h (.inr j : TileIndex m k))-(n : ZMod (h*n))} := by
  let q := top h (.inr j : TileIndex m k)
  obtain ⟨ha,hb,hc,hd⟩ := TileGapWords.tile_tails hn hsmall T.body T.differences (zeroSite h n q)
  simp only [CompletedTerrace.tileRows,Finset.biUnion_insert,Finset.singleton_biUnion,
    CompletedTerrace.tileFirst,CompletedTerrace.tileTwoSecond]
  rw [ha,hb]
  simp [q]

theorem local_three_tails (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (i : Fin m) :
    (T.tileRows (h := h) (.inl i : TileIndex m k)).biUnion (fun R => gapTails R n) =
      {zeroSite h n (top h (.inl i : TileIndex m k))-1,
       zeroSite h n (top h (.inl i : TileIndex m k))-(n : ZMod (h*n))+2,
       zeroSite h n (top h (.inl i : TileIndex m k))-2*(n : ZMod (h*n))} := by
  let q := top h (.inl i : TileIndex m k)
  obtain ⟨ha,hb,hc,hd⟩ := TileGapWords.tile_tails hn hsmall T.body T.differences (zeroSite h n q)
  have hd' : gapTails (T.tileThreeThird q) n = {zeroSite h n q-2*(n : ZMod (h*n))} := by
    simpa only [CompletedTerrace.tileThreeThird,zeroSite_pred] using hd
  simp only [CompletedTerrace.tileRows,Finset.biUnion_insert,Finset.singleton_biUnion]
  change gapTails (T.tileFirst q) n ∪ (gapTails (T.tileThreeSecond q) n ∪ gapTails (T.tileThreeThird q) n) = _
  rw [show gapTails (T.tileFirst q) n = {zeroSite h n q-1} from ha,
    show gapTails (T.tileThreeSecond q) n = {zeroSite h n q-(n : ZMod (h*n))+2} from hc,hd']
  ext x
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  dsimp [q]
  tauto

/-- Literal actual tail set of the globally constructed tile family. -/
theorem global_tile_tails (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    (m k : ℕ) :
    actualFamilyTails h n (T.globalFamily (h := h) m k) =
      tileTails (phaseStarts h n (pairPhases h m k)) (phaseStarts h n (triplePhases h m k)) := by
  rw [actualFamilyTails,CompletedTerrace.globalFamily,Finset.biUnion_biUnion,sum_biUnion]
  have h₃ : (Finset.univ : Finset (Fin m)).biUnion
      (fun i => (T.tileRows (h := h) (.inl i : TileIndex m k)).biUnion (fun R => gapTails R n)) =
      Finset.univ.biUnion (fun i : Fin m =>
        {zeroSite h n (top h (.inl i : TileIndex m k))-1,
         zeroSite h n (top h (.inl i : TileIndex m k))-(n : ZMod (h*n))+2,
         zeroSite h n (top h (.inl i : TileIndex m k))-2*(n : ZMod (h*n))}) := by
    apply Finset.biUnion_congr rfl
    intro i _
    exact local_three_tails T hn hsmall i
  have h₂ : (Finset.univ : Finset (Fin k)).biUnion
      (fun j => (T.tileRows (h := h) (.inr j : TileIndex m k)).biUnion (fun R => gapTails R n)) =
      Finset.univ.biUnion (fun j : Fin k =>
        {zeroSite h n (top h (.inr j : TileIndex m k))-1,
         zeroSite h n (top h (.inr j : TileIndex m k))-(n : ZMod (h*n))}) := by
    apply Finset.biUnion_congr rfl
    intro j _
    exact local_two_tails T hn hsmall j
  rw [h₃,h₂,biUnion_triple,biUnion_pair]
  simp only [tileTails,phaseStarts,pairPhases,triplePhases,Finset.image_union,
    Finset.image_image,Function.comp_def]
  ext x
  simp only [Finset.mem_union]
  tauto

end ActualTails

section Frames

variable {h n r : ℕ} [NeZero h] [NeZero n] [NeZero r] [NeZero (h*n)]
variable {T : CompletedTerrace n}

/-- The previously unpaid tail-pattern equality is now derived from actual
tile tails and the proved canonical frame/baseline family identification. -/
theorem schedule_allTailPositions (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {m k : ℕ} (htotal : h=3*m+2*k) :
    (scheduleFrame P hr hn hlarge htotal).allTailPositions =
      tileTails (phaseStarts h n (pairPhases h m k)) (phaseStarts h n (triplePhases h m k)) := by
  let G := scheduleFrame P hr hn hlarge htotal
  calc
    G.allTailPositions = actualFamilyTails h n (G.unlabelled (cyclicLatinFamily h r)) :=
      (G.actual_family_tails hr hlarge (cyclicLatinFamily h r)).symm
    _ = actualFamilyTails h n (T.globalFamily (h := h) m k) :=
      congrArg (actualFamilyTails h n) (schedule_family_eq P hr hn hlarge htotal)
    _ = _ := global_tile_tails T hn (by nlinarith) m k

theorem triplePhases_one (h k : ℕ) : triplePhases h 1 k = {(2 : ZMod h)} := by
  ext x
  simp only [triplePhases,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · rintro ⟨i,hi⟩
    have hv : i.val=0 := by have := i.isLt; omega
    simpa [top,hv] using hi.symm
  · intro hx
    refine ⟨⟨0,by omega⟩,?_⟩
    simpa [top] using hx.symm

theorem triplePhases_two (h k : ℕ) : triplePhases h 2 k = {(2 : ZMod h),(5 : ZMod h)} := by
  ext x
  simp only [triplePhases,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨i,hi⟩
    have hv : i.val=0 ∨ i.val=1 := by have := i.isLt; omega
    rcases hv with hv | hv
    · exact Or.inl (by simpa [top,hv] using hi.symm)
    · exact Or.inr (by simpa [top,hv] using hi.symm)
  · rintro (hx | hx)
    · exact ⟨⟨0,by omega⟩,by simpa [top] using hx.symm⟩
    · exact ⟨⟨1,by omega⟩,by simpa [top] using hx.symm⟩

theorem triple_starts_one (k : ℕ) :
    phaseStarts h n (triplePhases h 1 k) = {zeroSite h n (2 : ZMod h)} := by
  rw [triplePhases_one,phaseStarts]
  simp

theorem triple_starts_two (k : ℕ) :
    phaseStarts h n (triplePhases h 2 k) =
      {zeroSite h n (5 : ZMod h),zeroSite h n (5 : ZMod h)-3*(n : ZMod (h*n))} := by
  rw [triplePhases_two,phaseStarts]
  simp only [Finset.image_insert,Finset.image_singleton]
  have he : zeroSite h n (2 : ZMod h) = zeroSite h n (5 : ZMod h)-3*(n : ZMod (h*n)) := by
    rw [show (2 : ZMod h) = ((2 : ℕ) : ZMod h) from rfl,
      show (5 : ZMod h) = ((5 : ℕ) : ZMod h) from rfl,zeroSite_natCast,zeroSite_natCast]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [he]
  ext x
  simp only [Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem one_triple_body_orbits (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {k : ℕ} (htotal : h=3*1+2*k) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  let G := scheduleFrame P hr hn hlarge htotal
  let B := scheduleBaseline P hr hn hlarge htotal
  apply G.one_three_tile_phase_orbits hr hn hlarge B (pairPhases h 1 k) (2 : ZMod h)
  rw [schedule_allTailPositions P hr hn hlarge htotal,triple_starts_one]

theorem two_triple_body_orbits (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) {k : ℕ} (htotal : h=3*2+2*k) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  let G := scheduleFrame P hr hn hlarge htotal
  let B := scheduleBaseline P hr hn hlarge htotal
  apply G.two_three_tile_phase_orbits hr hn hlarge B (pairPhases h 2 k) (5 : ZMod h)
  rw [schedule_allTailPositions P hr hn hlarge htotal,triple_starts_two]

theorem canonical_body_orbits (P : BodyInput T r) (hr : 2 ≤ r) (hn : n=2*h-1)
    (hlarge : 100*r*r ≤ n) :
    ∃ C : Family h r → CorralRows h n,
      (Finset.univ.image (fun L : Family h r => physicalOrbit (realizedFamily (C L)))).card =
        latinSquareCount r ^ h ∧
      ∀ L, PhysicallyAsymmetric (realizedFamily (C L)) := by
  have ht := canonical_total (height_large hr hn hlarge)
  by_cases ho : h%2=1
  · have hm : canonicalTriples h=1 := by simp [canonicalTriples,ho]
    have htotal : h=3*1+2*canonicalPairs h := by simpa [hm] using ht
    exact one_triple_body_orbits P hr hn hlarge htotal
  · have hm : canonicalTriples h=2 := by simp [canonicalTriples,ho]
    have htotal : h=3*2+2*canonicalPairs h := by simpa [hm] using ht
    exact two_triple_body_orbits P hr hn hlarge htotal

end Frames

end CorralFormalization.LatinCompletion.LatinPrefix
