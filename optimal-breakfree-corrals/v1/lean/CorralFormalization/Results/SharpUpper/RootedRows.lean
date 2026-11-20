import CorralFormalization.Results.SharpUpper.Histories
import CorralFormalization.Results.SharpUpper.Product
import CorralFormalization.Results.SharpUpper.Intervals
import CorralFormalization.DiversityCompletion.WordBridge

/-!
# Every physical row supplies `n` different rooted gap representations

The upper bound only needs an injection of rooted physical rows into uniform
starting-site / gap-permutation samples. The cyclic enumeration is supplied
by the proved bridge from the exact finite cyclic gap inventory.
-/

namespace CorralFormalization.Results.SharpUpper

open Finset PhysicalCorral DiversitySymmetry

variable {M n : ℕ} [NeZero M]

/-- All actual physical rows with the prescribed full inventory. -/
noncomputable def validRows (M n : ℕ) [NeZero M] : Finset (Finset (ZMod M)) := by
  classical
  exact univ.filter (fun S => finiteCyclicGapInventory M (S.image ZMod.val) =
    Multiset.ofList (fullGapList n))

/-- All valid physical rows disjoint from the already occupied sites. -/
noncomputable def disjointValidRows (F : Finset (ZMod M)) (n : ℕ) :
    Finset (Finset (ZMod M)) := by
  classical
  exact (validRows M n).filter (fun S => Disjoint S F)

/-- A concrete cyclic enumeration with all prescribed gaps exactly once. -/
structure GapEnumeration (n : ℕ) [NeZero n] (S : Finset (ZMod M)) where
  row : CyclicRow n S
  injective_gap : Function.Injective row.gap
  gap_range : ∀ i, 0 < row.gap i ∧ row.gap i ≤ n

noncomputable def validRowEnumeration [NeZero n] (hn : 2 ≤ n)
    (S : Finset (ZMod M)) (hS : S ∈ validRows M n) : GapEnumeration n S := by
  have hg : finiteCyclicGapInventory M (S.image ZMod.val) =
      Multiset.ofList (fullGapList n) := (mem_filter.mp hS).2
  apply Classical.choice
  obtain ⟨E, hinj, hvalues⟩ := cyclicRow_of_finiteCyclicGapInventory S hn hg
  exact ⟨⟨E, hinj, fun i => (fullGapList_mem n (E.gap i)).mp
    ((hvalues _).mpr ⟨i,rfl⟩)⟩⟩

section Encoding

variable [NeZero n] {S : Finset (ZMod M)}

/-- The `t`th gap label when the row is rooted at cyclic index `k`. -/
def enumerationLetter (E : GapEnumeration n S) (k : ZMod n) (t : Fin n) : Fin n :=
  ⟨E.row.gap (k + (t.val : ZMod n)) - 1,
    by obtain ⟨hpos, hle⟩ := E.gap_range (k + (t.val : ZMod n)); omega⟩

omit [NeZero M] in
lemma enumerationLetter_value (E : GapEnumeration n S) (k : ZMod n) (t : Fin n) :
    (enumerationLetter E k t).val + 1 = E.row.gap (k + (t.val : ZMod n)) := by
  dsimp [enumerationLetter]
  have h := (E.gap_range (k + (t.val : ZMod n))).1
  omega

lemma enumerationLetter_injective (E : GapEnumeration n S) (k : ZMod n) :
    Function.Injective (enumerationLetter E k) := by
  intro t u htu
  have hv := congrArg Fin.val htu
  have ht := enumerationLetter_value E k t
  have hu := enumerationLetter_value E k u
  have hgap : E.row.gap (k + (t.val : ZMod n)) = E.row.gap (k + (u.val : ZMod n)) := by omega
  have hi : (t.val : ZMod n) = (u.val : ZMod n) := add_left_cancel (E.injective_gap hgap)
  have hi' := congrArg ZMod.val hi
  apply Fin.ext
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt t.isLt, Nat.mod_eq_of_lt u.isLt] using hi'

/-- The exact exposed gap word at a root. -/
def enumerationWord (E : GapEnumeration n S) (k : ZMod n) : List (Fin n) :=
  List.ofFn (enumerationLetter E k)

lemma enumerationWord_mem (E : GapEnumeration n S) (k : ZMod n) :
    enumerationWord E k ∈ gapPermutations n := by
  apply List.mem_toFinset.mpr
  apply List.mem_permutations.mpr
  have hnd : (enumerationWord E k).Nodup := List.nodup_ofFn.mpr (enumerationLetter_injective E k)
  apply (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange n)).mpr
  intro a
  have hs : Function.Surjective (enumerationLetter E k) :=
    Finite.surjective_of_injective (enumerationLetter_injective E k)
  obtain ⟨t,ht⟩ := hs a
  simp only [List.mem_finRange, iff_true]
  exact List.mem_ofFn.mpr ⟨t,ht⟩

/-- Actual prefix sums of the encoded word recover the physical cyclic
sites, including the final return after `n` gaps. -/
lemma enumerationWord_historySite (E : GapEnumeration n S) (k : ZMod n)
    (t : ℕ) (ht : t ≤ n) :
    historySite (E.row.site k) ((enumerationWord E k).take t) =
      E.row.site (k + (t : ZMod n)) := by
  induction t with
  | zero => simp [historySite]
  | succ t ih =>
    have htn : t < n := by omega
    have htl : t < (enumerationWord E k).length := by simp [enumerationWord]; omega
    rw [List.take_succ_eq_append_getElem htl, historySite_append, ih (by omega)]
    have hletter : ((enumerationWord E k)[t]).val + 1 = E.row.gap (k + (t : ZMod n)) := by
      simpa [enumerationWord] using enumerationLetter_value E k ⟨t,htn⟩
    rw [hletter]
    have hstep := head_eq_tail_add (x := E.row.site (k + (t : ZMod n)))
      (y := E.row.site (k + (t : ZMod n) + 1)) (d := E.row.gap (k + (t : ZMod n))) rfl
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hstep.symm

/-- The physical row reconstructed from the first `n` sampled sites. -/
def sampleRow (n : ℕ) (p : GapHistory M n) : Finset (ZMod M) :=
  univ.image (fun t : Fin n => historySite p.1 (p.2.take t.val))

lemma enumerationWord_sampleRow (E : GapEnumeration n S) (k : ZMod n) :
    sampleRow n (E.row.site k, enumerationWord E k) = S := by
  ext x
  simp only [sampleRow, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨t,ht⟩
    rw [enumerationWord_historySite E k t.val (Nat.le_of_lt t.isLt)] at ht
    exact ht ▸ (E.row.range _).mpr ⟨k + (t.val : ZMod n),rfl⟩
  · intro hx
    obtain ⟨i,hi⟩ := (E.row.range x).mp hx
    let t : Fin n := ⟨(i-k).val, ZMod.val_lt _⟩
    refine ⟨t, ?_⟩
    rw [enumerationWord_historySite E k t.val (Nat.le_of_lt t.isLt)]
    have hki : k + (t.val : ZMod n) = i := by dsimp [t]; rw [ZMod.natCast_zmod_val]; ring
    rw [hki,hi]

lemma enumerationWord_avoiding (E : GapEnumeration n S) (k : ZMod n)
    (F : Finset (ZMod M)) (hSF : Disjoint S F) :
    (E.row.site k, enumerationWord E k) ∈ avoidingSamples (n := n) F := by
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_univ _,enumerationWord_mem E k⟩, ?_⟩
  intro t ht hF
  rw [enumerationWord_historySite E k t ht] at hF
  have hS : E.row.site (k + (t : ZMod n)) ∈ S :=
    (E.row.range _).mpr ⟨k + (t : ZMod n),rfl⟩
  exact disjoint_left.mp hSF hS hF

end Encoding

/-- Every valid physical row gives `n` distinct avoiding representations,
and representations from different rows are distinct. This proves exactly
the multiplicity needed for the global upper bound, without assuming a
uniform distribution on physical rows. -/
theorem rootedRows_card_le_samples (hn : 2 ≤ n) (F : Finset (ZMod M)) :
    (disjointValidRows F n).card * n ≤ (avoidingSamples (n := n) F).card := by
  classical
  let : NeZero n := ⟨by omega⟩
  let C := disjointValidRows F n
  let E : (S : C) → GapEnumeration n S.val := fun S =>
    validRowEnumeration hn S.val (mem_filter.mp S.property).1
  let encode : C × ZMod n → GapHistory M n := fun p =>
    ((E p.1).row.site p.2, enumerationWord (E p.1) p.2)
  have hinj : Function.Injective encode := by
    rintro ⟨S,k⟩ ⟨T,l⟩ heq
    have hrows := congrArg (sampleRow n) heq
    change sampleRow n ((E S).row.site k, enumerationWord (E S) k) =
      sampleRow n ((E T).row.site l, enumerationWord (E T) l) at hrows
    rw [enumerationWord_sampleRow, enumerationWord_sampleRow] at hrows
    have hST : S = T := Subtype.ext hrows
    subst T
    have hsites := congrArg Prod.fst heq
    have hkl : k = l := (E S).row.injective hsites
    exact Prod.ext rfl hkl
  have hmem : ∀ p, encode p ∈ avoidingSamples (n := n) F := by
    rintro ⟨S,k⟩
    exact enumerationWord_avoiding (E S) k F (mem_filter.mp S.property).2
  calc
    (disjointValidRows F n).card * n = (univ.image encode).card := by
      rw [card_image_of_injective _ hinj]
      simp [C, Fintype.card_prod, ZMod.card]
    _ ≤ _ := card_le_card (by
      intro p hp
      obtain ⟨q,_,rfl⟩ := mem_image.mp hp
      exact hmem q)

/-- The exact concrete row-count numerator supplied by the history bound. -/
theorem disjointValidRows_mul_card_le (hn : 2 ≤ n)
    (F : Finset (ZMod M)) {j : ℕ} (hjn : j ≤ n)
    (hd : DenseNextSites (n := n) F j) :
    (disjointValidRows F n).card * n ≤
      (M-F.card) * (n-j)^j * (n-j).factorial :=
  (rootedRows_card_le_samples hn F).trans (avoidingSamples_card_le F hjn hd)

end CorralFormalization.Results.SharpUpper
