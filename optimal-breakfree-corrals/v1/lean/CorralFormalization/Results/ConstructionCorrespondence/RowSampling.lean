import CorralFormalization.Results.SharpUpper.RowMotion
import CorralFormalization.Results.SharpUpper.RowBranching

/-! Exact physical row sampling of the exact representation-multiplicity
claim in manuscript Section 7. No sampling or fibre supplier is assumed. -/

namespace CorralFormalization.Results.ConstructionCorrespondence.RowSampling

open Finset PhysicalCorral DiversitySymmetry Results.SharpUpper

variable {M n : ℕ} [NeZero M] [NeZero n]

theorem cyclicRow_sites_eq_of_start {S : Finset (ZMod M)}
    (E F : CyclicRow n S) (k : ZMod n) (hstart : E.site 0 = F.site k) :
    ∀ i : ZMod n, E.site i = F.site (k + i) := by
  have hnat : ∀ t : ℕ, E.site (t : ZMod n) = F.site (k + (t : ZMod n)) := by
    intro t
    induction t with
    | zero => simpa using hstart
    | succ t ih =>
      have he := E.consecutive (t : ZMod n)
      rw [ih] at he
      have hf := F.consecutive (k + (t : ZMod n))
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using adjacent_unique_head he hf
  intro i
  simpa only [ZMod.natCast_zmod_val] using hnat i.val

theorem sampleRow_cyclic (hn : 2 ≤ n) (hwidth : width n = M)
    (x : ZMod M) (w : List (Fin n)) (hw : w ∈ gapPermutations n) :
    ∃ E : CyclicRow n (sampleRow n (x, w)), E.site 0 = x ∧
      ∀ i : ZMod n, E.gap i = (w[i.val]'(by
        have hp := gapWord_perm_full hw
        have hl := hp.length_eq
        simp only [List.length_map, fullGapList, List.length_range] at hl
        have hi := ZMod.val_lt i
        omega)).val + 1 := by
  let g := w.map (fun a : Fin n => a.val + 1)
  have hperm : g.Perm (fullGapList n) := gapWord_perm_full hw
  have hglen : g.length = n := by simpa [fullGapList] using hperm.length_eq
  have hwlen : w.length = n := by simpa only [g, List.length_map] using hglen
  have hpos : ∀ a ∈ g, 0 < a := by
    intro a ha
    exact ((fullGapList_mem n a).mp (hperm.mem_iff.mp ha)).1
  have hsum : g.sum = M := hperm.sum_eq.trans ((fullGapList_sum n).trans hwidth)
  obtain ⟨E, hsites, hgap⟩ := cyclicRow_of_positive_word g hglen hpos hsum hn
  have hrow : (Motion.rotation x).onRow (wordSites M n g) = sampleRow n (x, w) := by
    rw [sampleRow_eq_prefixRow x w hwlen, wordSites_eq_physicalPrefixes g hglen]
    simp only [Motion.onRow, physicalSites, prefixRow, image_image, Function.comp_def, Motion.act, g]
  rw [← hrow]
  refine ⟨E.rotation x, ?_, ?_⟩
  · change x + E.site 0 = x
    rw [hsites]
    simp
  · intro i
    rw [CyclicRow.rotation_gap, hgap]
    simp only [g, List.getElem_map]

theorem sampleWord_eq_enumeration {S : Finset (ZMod M)} (hn : 2 ≤ n)
    (hwidth : width n = M) (E : GapEnumeration n S)
    (x : ZMod M) (w : List (Fin n)) (hw : w ∈ gapPermutations n)
    (hrow : sampleRow n (x, w) = S) (k : ZMod n) (hroot : E.row.site k = x) :
    w = enumerationWord E k := by
  subst S
  obtain ⟨F, hFstart, hFgap⟩ := sampleRow_cyclic hn hwidth x w hw
  have hstart : F.site 0 = E.row.site k := hFstart.trans hroot.symm
  have hsites := cyclicRow_sites_eq_of_start F E.row k hstart
  have hgap : ∀ i : ZMod n, F.gap i = E.row.gap (k + i) := by
    intro i
    simp only [CyclicRow.gap, hsites, add_assoc]
  have hlen : w.length = n := by
    have hp := (gapWord_perm_full hw).length_eq
    simpa [fullGapList] using hp
  apply List.ext_getElem
  · simp [hlen, enumerationWord]
  · intro t ht hu
    have htn : t < n := by omega
    have hi : (t : ZMod n).val = t := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt htn]
    have hF := hFgap (t : ZMod n)
    rw [hgap] at hF
    have hE := enumerationLetter_value E k ⟨t, htn⟩
    apply Fin.ext
    have : (w[t]).val + 1 = (enumerationLetter E k ⟨t, htn⟩).val + 1 := by
      simpa only [hi] using hF.symm.trans hE.symm
    simpa only [enumerationWord, List.getElem_ofFn] using Nat.add_right_cancel this

noncomputable def rowRepresentations (S : Finset (ZMod M)) : Finset (GapHistory M n) := by
  classical
  exact (gapSampleSpace M n).filter (fun p => sampleRow n p = S)

/-- Each actual valid physical row has exactly `n` sample representations,
one for each genuine starting point on it. -/
theorem rowRepresentations_card (hn : 2 ≤ n) (hwidth : width n = M)
    (S : Finset (ZMod M)) (hS : S ∈ validRows M n) :
    (rowRepresentations (n := n) S).card = n := by
  classical
  let E := validRowEnumeration hn S hS
  let encode : ZMod n → GapHistory M n := fun k => (E.row.site k, enumerationWord E k)
  have hinj : Function.Injective encode := by
    intro k l heq
    exact E.row.injective (congrArg Prod.fst heq)
  have heq : rowRepresentations (n := n) S = univ.image encode := by
    ext p
    rcases p with ⟨x, w⟩
    constructor
    · intro hp
      obtain ⟨hp, hrow⟩ := mem_filter.mp hp
      have hw : w ∈ gapPermutations n := (mem_product.mp hp).2
      have hx : x ∈ S := by
        rw [← hrow]
        apply mem_image.mpr
        refine ⟨⟨0, by omega⟩, mem_univ _, ?_⟩
        simp [historySite]
      obtain ⟨k, hk⟩ := (E.row.range x).mp hx
      have hword := sampleWord_eq_enumeration hn hwidth E x w hw hrow k hk
      refine mem_image.mpr ⟨k, mem_univ _, ?_⟩
      exact Prod.ext hk hword.symm
    · intro hp
      obtain ⟨k, _, heq⟩ := mem_image.mp hp
      rw [← heq]
      apply mem_filter.mpr
      exact ⟨mem_product.mpr ⟨mem_univ _, enumerationWord_mem E k⟩, enumerationWord_sampleRow E k⟩
  rw [heq, card_image_of_injective _ hinj]
  simp [ZMod.card]

omit [NeZero n] in
theorem sampleRow_valid (_hn : 2 ≤ n) (hwidth : width n = M)
    (p : GapHistory M n) (hp : p ∈ gapSampleSpace M n) :
    sampleRow n p ∈ validRows M n := by
  have hw : p.2 ∈ gapPermutations n := (mem_product.mp hp).2
  have hperm := gapWord_perm_full hw
  have hlen : p.2.length = n := by simpa [fullGapList] using hperm.length_eq
  rw [sampleRow_eq_prefixRow p.1 p.2 hlen]
  exact prefixRow_valid hwidth _ _ hperm

/-- The total number of samples is exactly `n` times the actual physical-row
count. The cardinality equality is proved through the real sampleRow map. -/
theorem validRows_card_mul (hn : 2 ≤ n) (hwidth : width n = M) :
    (validRows M n).card * n = M * n.factorial := by
  classical
  have hsplit : (validRows M n).biUnion (rowRepresentations (n := n)) = gapSampleSpace M n := by
    ext p
    constructor
    · intro hp
      obtain ⟨S, _, hp⟩ := mem_biUnion.mp hp
      exact (mem_filter.mp hp).1
    · intro hp
      exact mem_biUnion.mpr ⟨sampleRow n p, sampleRow_valid hn hwidth p hp,
        mem_filter.mpr ⟨hp, rfl⟩⟩
  have hdisjoint : ∀ S ∈ validRows M n, ∀ T ∈ validRows M n, S ≠ T →
      Disjoint (rowRepresentations (n := n) S) (rowRepresentations (n := n) T) := by
    intro S _ T _ hST
    apply disjoint_left.mpr
    intro p hpS hpT
    exact hST ((mem_filter.mp hpS).2.symm.trans (mem_filter.mp hpT).2)
  calc
    (validRows M n).card * n = ∑ _S ∈ validRows M n, n := by simp
    _ = ∑ S ∈ validRows M n, (rowRepresentations (n := n) S).card := by
      apply sum_congr rfl
      intro S hS
      exact (rowRepresentations_card hn hwidth S hS).symm
    _ = ((validRows M n).biUnion (rowRepresentations (n := n))).card :=
      (card_biUnion hdisjoint).symm
    _ = (gapSampleSpace M n).card := congrArg card hsplit
    _ = M * n.factorial := gapSampleSpace_card M n

/-- In particular the optimal physical clock has exactly `h * n!` rows.
The proof only requires the width identity and `M = h*n`, so it also
states explicitly which arithmetic makes the manuscript's count apply. -/
theorem validRows_card_of_clock (hn : 2 ≤ n) (hwidth : width n = M)
    (h : ℕ) (hclock : M = h * n) :
    (validRows M n).card = h * n.factorial := by
  have hmul := validRows_card_mul hn hwidth
  have hmul' : (validRows M n).card * n = (h * n) * n.factorial :=
    hmul.trans (congrArg (fun m : ℕ => m * n.factorial) hclock)
  have hnpos : 0 < n := by omega
  nlinarith [hmul']

/-- Equal fibres imply literal uniform sampling of actual physical rows.
This states the finite probability equality and does not choose a different
row distribution. -/
theorem rowRepresentations_probability (hn : 2 ≤ n) (hwidth : width n = M)
    (S : Finset (ZMod M)) (hS : S ∈ validRows M n) :
    ((rowRepresentations (n := n) S).card : ℝ) / ((gapSampleSpace M n).card : ℝ) =
      1 / ((validRows M n).card : ℝ) := by
  have hmul : ((validRows M n).card : ℝ) * (n : ℝ) =
      ((gapSampleSpace M n).card : ℝ) := by
    rw [gapSampleSpace_card]
    exact_mod_cast validRows_card_mul hn hwidth
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [rowRepresentations_card hn hwidth S hS, ← hmul]
  field_simp

end CorralFormalization.Results.ConstructionCorrespondence.RowSampling
