import CorralFormalization.Results.GeneralTiles.LayoutTails

/-!
# Arbitrary palette-preserving row modifications

The input below is one modified row for each original row, its full gap
palette, and inclusion of the actual original tails of lengths 1, 2, n.
Because each relevant gap is unique, inclusion implies equality. No Latin
frame, local-cell condition or special form of row modification is used.
-/

namespace CorralFormalization.LatinCompletion.GeneralTiles

open LatinTransfer PhysicalCorral DiversitySymmetry TerraceLift

theorem familyTails_rotation {M : ℕ} [NeZero M]
    (F : Finset (Finset (ZMod M))) (c : ZMod M) (d : ℕ) :
    familyTails ((Motion.rotation c).onFamily F) d =
      (familyTails F d).image (fun x => c+x) := by
  classical
  simp only [familyTails,Motion.onFamily,Finset.image_biUnion,Finset.biUnion_image,
    gapTails_rotation]

theorem familyTails_reflection {M : ℕ} [NeZero M]
    (F : Finset (Finset (ZMod M))) (c : ZMod M) (d : ℕ) :
    familyTails ((Motion.reflection c).onFamily F) d =
      (familyTails F d).image (fun x => c-(d : ZMod M)-x) := by
  classical
  simp only [familyTails,Motion.onFamily,Finset.image_biUnion,Finset.biUnion_image,
    gapTails_reflection]

/-- An arbitrary collection of modified rows with the original palette,
retaining the edges singled out in Lemma 11. Inclusion of the tail sets
means preservation of those actual directed edges: their heads are tail+d.
The structure does not assume the desired tail equality or row decoder. -/
structure RowModification {M : ℕ} [NeZero M] (n : ℕ)
    (F : Finset (Finset (ZMod M))) where
  row : {R : Finset (ZMod M) // R∈F} → Finset (ZMod M)
  palette : ∀ R, finiteCyclicGapInventory M ((row R).image ZMod.val) =
    Multiset.ofList (fullGapList n)
  preserves : ∀ R d, d∈({1,2,n} : Finset ℕ) → gapTails R.val d ⊆ gapTails (row R) d

namespace RowModification

variable {M n : ℕ} [NeZero M] {F : Finset (Finset (ZMod M))}

def family (P : RowModification n F) : Finset (Finset (ZMod M)) :=
  F.attach.image P.row

theorem tails_eq (P : RowModification n F) (hn : 2≤n)
    (hpal : ∀ R∈F,finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n))
    (R : {R : Finset (ZMod M) // R∈F}) (d : ℕ) (hd : d∈({1,2,n} : Finset ℕ)) :
    gapTails (P.row R) d = gapTails R.val d := by
  have hdn : 0<d ∧ d≤n := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> omega
  obtain ⟨x,hx⟩ := gapTails_singleton_of_finiteCyclicGapInventory n R.val hn
    (hpal R.val R.property) d hdn.1 hdn.2
  obtain ⟨y,hy⟩ := gapTails_singleton_of_finiteCyclicGapInventory n (P.row R) hn
    (P.palette R) d hdn.1 hdn.2
  have hxy : x=y := by
    have hi := P.preserves R d hd
    rw [hx,hy] at hi
    exact Finset.mem_singleton.mp (hi (Finset.mem_singleton_self x))
  rw [hx,hy,hxy]

/-- Any such modification keeps all three global distinguished tail sets. -/
theorem family_tails_eq (P : RowModification n F) (hn : 2≤n)
    (hpal : ∀ R∈F,finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n))
    (d : ℕ) (hd : d∈({1,2,n} : Finset ℕ)) :
    familyTails P.family d = familyTails F d := by
  classical
  unfold RowModification.family
  rw [familyTails,Finset.image_biUnion]
  simp_rw [P.tails_eq hn hpal _ d hd]
  ext x
  simp [familyTails]

/-- The unique gap-n tail of each row is a label independent of every
allowed modification. Distinct original rows retain distinct labels. -/
theorem row_recovered_by_n_tail (P : RowModification n F) (hn : 2≤n)
    (hpal : ∀ R∈F,finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n))
    (hdis : ∀ R∈F,∀ S∈F,R≠S → Disjoint R S)
    (R S : {R : Finset (ZMod M) // R∈F}) :
    gapTails (P.row R) n = gapTails (P.row S) n ↔ R=S := by
  constructor
  · intro he
    rw [P.tails_eq hn hpal _ n (by simp),P.tails_eq hn hpal _ n (by simp)] at he
    by_contra hne
    have hne' : R.val≠S.val := fun h => hne (Subtype.ext h)
    obtain ⟨x,hx⟩ := gapTails_singleton_of_finiteCyclicGapInventory n R.val hn
      (hpal R.val R.property) n (by omega) le_rfl
    have hRx : x∈gapTails R.val n := by rw [hx]; simp
    have hSx : x∈gapTails S.val n := he ▸ hRx
    exact Finset.disjoint_left.mp (hdis _ R.property _ S.property hne')
      ((mem_gapTails _ _ _).mp hRx).choose_spec.1.1
      ((mem_gapTails _ _ _).mp hSx).choose_spec.1.1
  · rintro rfl
    rfl

theorem row_injective (P : RowModification n F) (hn : 2≤n)
    (hpal : ∀ R∈F,finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n))
    (hdis : ∀ R∈F,∀ S∈F,R≠S → Disjoint R S) : Function.Injective P.row := by
  intro R S he
  apply (P.row_recovered_by_n_tail hn hpal hdis R S).mp
  rw [he]

end RowModification

namespace CyclicTiling

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modified_gap_two_tails (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (P : RowModification n (L.family T)) :
    familyTails P.family 2=L.twoTailPattern n := by
  rw [P.family_tails_eq (by omega) (L.inventory T hn (by omega)) 2 (by simp),
    L.gap_two_tails T hn hsmall]

theorem modified_gap_n_tails (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (P : RowModification n (L.family T)) :
    familyTails P.family n=L.nTailPattern n := by
  rw [P.family_tails_eq (by omega) (L.inventory T hn (by omega)) n (by simp),
    L.gap_n_tails T hn hsmall]

theorem modified_gap_one_tails (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (rest : List ℕ) (hbody : T.body=[7,1]++rest)
    (P : RowModification n (L.family T)) :
    familyTails P.family 1=
      (Finset.univ : Finset (ZMod h)).image (fun q => zeroSite h n q+17) := by
  rw [P.family_tails_eq (by omega) (L.inventory T hn (by omega)) 1 (by simp),
    L.gap_one_tails T hn hsmall rest hbody]

/-- A geometric row modification supplies no extra information to the
layout decoder: its actual preserved gap-two tails determine both starts. -/
theorem modified_layout_reconstruction {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : CyclicTiling h ι) (K : CyclicTiling h κ) (T U : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n)
    (P : RowModification n (L.family T)) (Q : RowModification n (K.family U))
    (htails : familyTails P.family 2=familyTails Q.family 2) :
    L.twoStarts=K.twoStarts ∧ L.threeStarts=K.threeStarts := by
  apply L.layout_reconstruction K hsmall
  rw [← L.modified_gap_two_tails T hn hsmall P,
    ← K.modified_gap_two_tails U hn hsmall Q]
  exact htails

theorem modified_rows_distinguished (L : CyclicTiling h ι) (T : CompletedTerrace n)
    (hn : n=2*h-1) (hsmall : 65≤n) (P Q : RowModification n (L.family T))
    (R S : {R : Finset (ZMod (h*n)) // R∈L.family T}) :
    gapTails (P.row R) n=gapTails (Q.row S) n ↔ R=S := by
  have hpal := L.inventory T hn (by omega : 15≤n)
  have hdis : ∀ R∈L.family T,∀ S∈L.family T,R≠S → Disjoint R S := by
    intro R hR S hS hRS
    exact L.disjoint T hn (by omega : 15≤n) R S hR hS hRS
  rw [Q.tails_eq (by omega) hpal S n (by simp),
    ← P.tails_eq (by omega) hpal S n (by simp)]
  exact P.row_recovered_by_n_tail (by omega) hpal hdis R S

end CyclicTiling

end CorralFormalization.LatinCompletion.GeneralTiles
