import CorralFormalization.Results.SharpUpper.RootedRows
import CorralFormalization.ReverseGapWord

/-!
# Motion invariance of actual valid physical rows

The reflection proof reverses a positive gap word and checks the resulting
physical prefix sites. It does not assume covariance of a sorted inventory.
-/

namespace CorralFormalization.Results.SharpUpper

open Finset PhysicalCorral DiversitySymmetry

variable {M n : ℕ} [NeZero M]

/-- Prefix sites of an ordinary positive gap word, translated on the
physical clock. -/
def prefixRow (x : ZMod M) (g : List ℕ) : Finset (ZMod M) :=
  (properPrefixSites g).toFinset.image (fun p : ℕ => x + (p : ZMod M))

omit [NeZero M] in
lemma sampleRow_eq_prefixRow (x : ZMod M) (w : List (Fin n)) (hlen : w.length = n) :
    sampleRow n (x,w) = prefixRow x (w.map (fun a : Fin n => a.val+1)) := by
  ext y
  simp only [sampleRow, prefixRow, mem_image, mem_univ, true_and,
    List.mem_toFinset, mem_properPrefixSites_iff, List.length_map]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨((w.take t.val).map (fun a : Fin n => a.val+1)).sum, ?_, ht⟩
    exact ⟨t.val, by omega, by rw [List.map_take]⟩
  · rintro ⟨p,⟨t,ht,hp⟩,hy⟩
    refine ⟨⟨t,by omega⟩, ?_⟩
    unfold historySite
    rw [← List.map_take] at hp
    rw [hp]
    exact hy

lemma finRange_gapWord (n : ℕ) :
    (List.finRange n).map (fun a : Fin n => a.val+1) = fullGapList n := by
  apply List.ext_getElem
  · simp [fullGapList]
  · intro i hi hj
    simp [fullGapList]

lemma gapWord_perm_full {w : List (Fin n)} (hw : w ∈ gapPermutations n) :
    (w.map (fun a : Fin n => a.val+1)).Perm (fullGapList n) := by
  have hp : w.Perm (List.finRange n) := List.mem_permutations.mp (List.mem_toFinset.mp hw)
  simpa only [finRange_gapWord] using hp.map (fun a : Fin n => a.val+1)

/-- Positive full-inventory words give valid physical rows at every
starting site. The wrapping modulus is the same `M` as the actual clock. -/
theorem prefixRow_valid (hw : width n = M) (x : ZMod M) (g : List ℕ)
    (hperm : g.Perm (fullGapList n)) : prefixRow x g ∈ validRows M n := by
  classical
  have hsum : g.sum = M := hperm.sum_eq.trans ((fullGapList_sum n).trans hw)
  have hpos : ∀ a ∈ g, 0 < a := by
    intro a ha
    exact ((fullGapList_mem n a).mp (hperm.mem_iff.mp ha)).1
  have hb : ∀ p ∈ (properPrefixSites g).toFinset, p < M := by
    intro p hp
    rw [← hsum]
    exact properPrefixSites_lt_sum g hpos p (List.mem_toFinset.mp hp)
  have hbase : finiteCyclicGapInventory M (properPrefixSites g).toFinset = Multiset.ofList g := by
    rw [← hsum]
    cases g with
    | nil => have := NeZero.ne M; simp_all
    | cons a as => exact properPrefixSites_finite_gaps a as hpos
  have hdecode : (prefixRow x g).image ZMod.val =
      (properPrefixSites g).toFinset.image (fun p => (p+x.val)%M) := by
    rw [prefixRow, image_image]
    apply image_congr
    intro p hp
    change (x + (p : ZMod M)).val = (p+x.val)%M
    rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, Nat.add_comm]
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  rw [hdecode, finite_set_cyclic_gap_rotate M x.val _ (NeZero.pos M) hb, hbase]
  exact Multiset.coe_eq_coe.mpr hperm

omit [NeZero M] in
lemma prefixRow_rotation (c x : ZMod M) (g : List ℕ) :
    (Motion.rotation c).onRow (prefixRow x g) = prefixRow (c+x) g := by
  simp only [Motion.onRow, prefixRow, image_image, Function.comp_def, Motion.act, add_assoc]

/-- Reversing the actual positive gap word is the literal physical
reflection, including the start and the closing gap. -/
lemma prefixRow_reflection (b x : ZMod M) (g : List ℕ)
    (hpos : ∀ a ∈ g, 0 < a) (hsum : g.sum = M) :
    (Motion.reflection b).onRow (prefixRow x g) = prefixRow (b-x) g.reverse := by
  have hgsum : 0 < g.sum := by rw [hsum]; exact NeZero.pos M
  unfold prefixRow
  rw [properPrefixSites_reverse_reflect g hpos hgsum]
  simp only [Motion.onRow, image_image, Function.comp_def, Motion.act]
  apply image_congr
  intro p hp
  have hpM : p < M := by
    rw [← hsum]
    exact properPrefixSites_lt_sum g hpos p (List.mem_toFinset.mp hp)
  change b - (x + (p : ZMod M)) = b - x + (((g.sum-p)%g.sum : ℕ) : ZMod M)
  rw [hsum, ZMod.natCast_mod, Nat.cast_sub (by omega : p ≤ M)]
  simp only [ZMod.natCast_self, zero_sub]
  ring

/-- Every common physical rotation or reflection preserves the prescribed
full cyclic-gap inventory. -/
theorem validRows_motion_closed (hn : 2 ≤ n) (hw : width n = M)
    (S : Finset (ZMod M)) (hS : S ∈ validRows M n) (f : Motion M) :
    f.onRow S ∈ validRows M n := by
  let : NeZero n := ⟨by omega⟩
  let E := validRowEnumeration hn S hS
  let w := enumerationWord E 0
  let g := w.map (fun a : Fin n => a.val+1)
  have hperm : g.Perm (fullGapList n) := gapWord_perm_full (enumerationWord_mem E 0)
  have hlen : w.length = n := by simp [w, enumerationWord]
  have hrepr : S = prefixRow (E.row.site 0) g :=
    (enumerationWord_sampleRow E 0).symm.trans (sampleRow_eq_prefixRow _ w hlen)
  rw [hrepr]
  cases f with
  | rotation c =>
    rw [prefixRow_rotation]
    exact prefixRow_valid hw _ g hperm
  | reflection b =>
    have hpos : ∀ a ∈ g, 0 < a := by
      intro a ha
      exact ((fullGapList_mem n a).mp (hperm.mem_iff.mp ha)).1
    have hsum : g.sum = M := hperm.sum_eq.trans ((fullGapList_sum n).trans hw)
    rw [prefixRow_reflection _ _ _ hpos hsum]
    exact prefixRow_valid hw _ g.reverse ((List.reverse_perm g).trans hperm)

end CorralFormalization.Results.SharpUpper
