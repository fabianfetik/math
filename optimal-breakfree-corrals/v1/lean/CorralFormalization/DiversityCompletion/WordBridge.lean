import CorralFormalization.DiversityCompletion.CyclicGeometry

namespace CorralFormalization.DiversitySymmetry

open Finset
open CorralFormalization.PhysicalCorral

variable {M : ℕ} [NeZero M]

theorem gapLength_natCast_of_le (a b : ℕ) (ha : a < M) (hb : b < M) (hab : a ≤ b) :
    gapLength (a : ZMod M) (b : ZMod M) = b - a := by
  unfold gapLength
  have hva : (a : ZMod M).val = a := by simp [Nat.mod_eq_of_lt ha]
  have hvb : (b : ZMod M).val = b := by simp [Nat.mod_eq_of_lt hb]
  rw [ZMod.val_sub (by simpa only [hva, hvb] using hab), hva, hvb]

omit [NeZero M] in
theorem gapLength_natCast_of_gt (a b : ℕ) (ha : a < M) (_hb : b < M) (hba : b < a) :
    gapLength (a : ZMod M) (b : ZMod M) = M + b - a := by
  have heq : ((M + b - a : ℕ) : ZMod M) = (b : ZMod M) - (a : ZMod M) := by
    rw [Nat.cast_sub (by omega : a ≤ M + b), Nat.cast_add]
    simp
  unfold gapLength
  rw [← heq, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : M + b - a < M)]

/-- Ordinary adjacent representatives are physical neighbors exactly when
their open ordinary interval contains no represented point. -/
theorem insideArc_natCast_iff (a z b : ℕ) (ha : a < M) (hz : z < M)
    (hb : b < M) (hab : a < b) :
    insideArc (a : ZMod M) (z : ZMod M) (b : ZMod M) ↔ a < z ∧ z < b := by
  unfold insideArc
  rw [gapLength_natCast_of_le a b ha hb (Nat.le_of_lt hab)]
  by_cases haz : a ≤ z
  · rw [gapLength_natCast_of_le a z ha hz haz]
    omega
  · rw [gapLength_natCast_of_gt a z ha hz (Nat.lt_of_not_ge haz)]
    omega

/-- The wrap edge from the last positive representative to zero has no
interior point among representatives between zero and that last point. -/
theorem not_insideArc_wrap (a z : ℕ) (ha : a < M) (hz : z < M)
    (hapos : 0 < a) (hza : z ≤ a) :
    ¬ insideArc (a : ZMod M) (z : ZMod M) 0 := by
  by_cases hzeq : z = a
  · subst z
    simp [insideArc, gapLength]
  · have hlt : z < a := by omega
    have hgap0 := gapLength_natCast_of_gt a 0 ha (NeZero.pos M) hapos
    simp only [Nat.cast_zero, Nat.add_zero] at hgap0
    unfold insideArc
    rw [gapLength_natCast_of_gt a z ha hz hlt, hgap0]
    omega

/-- Actual sites of a positive gap word, indexed by all proper prefixes. -/
def wordSites (M n : ℕ) [NeZero n] (g : List ℕ) : Finset (ZMod M) :=
  univ.image fun i : ZMod n => (((g.take i.val).sum : ℕ) : ZMod M)

/-- A positive word making one winding gives an actual physical cyclic
row. The final edge is proved separately as the wrap and has the final
word entry as its positive natural length. -/
theorem cyclicRow_of_positive_word {n : ℕ} [NeZero n] (g : List ℕ)
    (hlen : g.length = n) (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum = M)
    (hn : 2 ≤ n) :
    ∃ E : CyclicRow n (wordSites M n g),
      (∀ i : ZMod n, E.site i = (((g.take i.val).sum : ℕ) : ZMod M)) ∧
      ∀ i : ZMod n, E.gap i = g[i.val]'(by have hi := ZMod.val_lt i; omega) := by
  let p : ℕ → ℕ := fun k => (g.take k).sum
  let v : ZMod n → ZMod M := fun i => (p i.val : ZMod M)
  have hbound : ∀ k, k < n → p k < M := by
    intro k hk
    rw [← hsum]
    exact properPrefixSites_lt_sum g hpos _
      ((mem_properPrefixSites_iff g _).mpr ⟨k, by omega, rfl⟩)
  have hstrict : ∀ a b, a < b → b ≤ n → p a < p b := by
    intro a b hab hb
    exact positive_take_sum_strict g hpos a b hab (by omega)
  have hmono : Monotone p := List.monotone_sum_take g
  have hvinj : Function.Injective v := by
    intro i j hij
    have hv := congrArg ZMod.val hij
    have hi := hbound i.val (ZMod.val_lt i)
    have hj := hbound j.val (ZMod.val_lt j)
    change (p i.val : ZMod M).val = (p j.val : ZMod M).val at hv
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
    apply ZMod.val_injective n
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h := hstrict i.val j.val hlt (Nat.le_of_lt (ZMod.val_lt j))
      omega
    · have h := hstrict j.val i.val hgt (Nat.le_of_lt (ZMod.val_lt i))
      omega
  have hmem : ∀ i, v i ∈ wordSites M n g := by
    intro i
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  have hstep : ∀ i : ZMod n,
      Adjacent (wordSites M n g) (v i) (v (i + 1)) ∧
        gapLength (v i) (v (i + 1)) = g[i.val]'(by have hi := ZMod.val_lt i; omega) := by
    intro i
    have hi : i.val < n := ZMod.val_lt i
    have hival : (i + 1).val = (i.val + 1) % n := by
      rw [ZMod.val_add, ZMod.val_one'' (by omega : n ≠ 1)]
    have hgi : 0 < g[i.val] := hpos _ (List.getElem_mem (by omega))
    have hsumstep : p (i.val + 1) = p i.val + g[i.val] := List.sum_take_succ g i.val (by omega)
    have hne : v i ≠ v (i + 1) := by
      intro hv
      have hindex := hvinj hv
      have hone : (1 : ZMod n) = 0 := by
        have h' : (i + 1) - i = i - i := congrArg (fun z => z - i) hindex.symm
        simpa using h'
      have hval := congrArg ZMod.val hone
      rw [ZMod.val_one'' (by omega : n ≠ 1), ZMod.val_zero] at hval
      omega
    by_cases hinterior : i.val + 1 < n
    · have hnext : (i + 1).val = i.val + 1 := by
        rw [hival, Nat.mod_eq_of_lt hinterior]
      have hpi := hbound i.val hi
      have hpnext := hbound (i.val + 1) hinterior
      have hlt : p i.val < p (i.val + 1) := by omega
      have hgap : gapLength (v i) (v (i + 1)) = g[i.val] := by
        change gapLength (p i.val : ZMod M) (p (i + 1).val : ZMod M) = _
        rw [hnext, gapLength_natCast_of_le _ _ hpi hpnext (Nat.le_of_lt hlt)]
        omega
      refine ⟨⟨hmem i, hmem (i + 1), hne, ?_⟩, hgap⟩
      intro z hz hzarc
      obtain ⟨k, _, rfl⟩ := mem_image.mp hz
      change insideArc (p i.val : ZMod M) (p k.val : ZMod M)
        (p (i + 1).val : ZMod M) at hzarc
      rw [hnext] at hzarc
      obtain ⟨hl, hr⟩ := (insideArc_natCast_iff _ _ _ hpi
        (hbound k.val (ZMod.val_lt k)) hpnext hlt).mp hzarc
      by_cases hki : k.val ≤ i.val
      · have h := hmono hki
        omega
      · have h := hmono (by omega : i.val + 1 ≤ k.val)
        omega
    · have hlast : i.val + 1 = n := by omega
      have hnext : (i + 1).val = 0 := by rw [hival, hlast, Nat.mod_self]
      have hpi := hbound i.val hi
      have hpi0 : 0 < p i.val := by
        have h := hstrict 0 i.val (by omega) (Nat.le_of_lt hi)
        simpa [p] using h
      have hpfull : p (i.val + 1) = M := by simp [p, hlast, ← hlen, hsum]
      have hgap : gapLength (v i) (v (i + 1)) = g[i.val] := by
        change gapLength (p i.val : ZMod M) (p (i + 1).val : ZMod M) = _
        rw [hnext]
        have hp0 : p 0 = 0 := rfl
        rw [hp0]
        rw [gapLength_natCast_of_gt _ _ hpi (NeZero.pos M) hpi0]
        omega
      refine ⟨⟨hmem i, hmem (i + 1), hne, ?_⟩, hgap⟩
      intro z hz hzarc
      obtain ⟨k, _, rfl⟩ := mem_image.mp hz
      change insideArc (p i.val : ZMod M) (p k.val : ZMod M)
        (p (i + 1).val : ZMod M) at hzarc
      rw [hnext] at hzarc
      have hp0 : p 0 = 0 := rfl
      simp only [hp0, Nat.cast_zero] at hzarc
      have hkle : k.val ≤ i.val := by have hk := ZMod.val_lt k; omega
      exact not_insideArc_wrap _ _ hpi (hbound k.val (ZMod.val_lt k)) hpi0 (hmono hkle) hzarc
  let E : CyclicRow n (wordSites M n g) := {
    site := v
    injective := hvinj
    range := by
      intro x
      simp only [wordSites, mem_image, mem_univ, true_and, v, p]
    consecutive := fun i => (hstep i).1
  }
  exact ⟨E, fun _ => rfl, fun i => (hstep i).2⟩

omit [NeZero M] in
theorem wordSites_eq_physicalPrefixes {n : ℕ} [NeZero n] (g : List ℕ) (hlen : g.length = n) :
    wordSites M n g = physicalSites M (properPrefixSites g).toFinset := by
  ext x
  simp only [wordSites, physicalSites, mem_image, mem_univ, true_and, List.mem_toFinset,
    mem_properPrefixSites_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(g.take i.val).sum, ⟨i.val, by have hi := ZMod.val_lt i; omega, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨(j : ZMod n), ?_⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : j < n)]

theorem rigidRow_positive_word {n : ℕ} [NeZero n] (g : List ℕ)
    (hlen : g.length = n) (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum = M)
    (hn : 3 ≤ n) (hnd : g.Nodup) :
    RigidRow (physicalSites M (properPrefixSites g).toFinset) := by
  obtain ⟨E, _, hgap⟩ := cyclicRow_of_positive_word g hlen hpos hsum (by omega)
  rw [← wordSites_eq_physicalPrefixes g hlen]
  apply E.rigidRow hn
  intro i j hij
  apply ZMod.val_injective n
  rw [hgap i, hgap j] at hij
  exact hnd.getElem_inj_iff.mp hij

/-- The existing sorted cyclic inventory supplies the actual physical
cyclic enumeration, including the wrap, its distinct gap function and
every prescribed gap length. No order-covariance assumption is an input. -/
theorem cyclicRow_of_finiteCyclicGapInventory {n : ℕ} [NeZero n]
    (R : Finset (ZMod M)) (hn : 2 ≤ n)
    (hgap : finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n)) :
    ∃ E : CyclicRow n R, Function.Injective E.gap ∧
      ∀ d, d ∈ fullGapList n ↔ ∃ i, E.gap i = d := by
  let S := R.image ZMod.val
  change finiteCyclicGapInventory M S = Multiset.ofList (fullGapList n) at hgap
  have hcard : S.card = n := by
    have h := congrArg Multiset.card hgap
    rw [finiteCyclicGapInventory_card] at h
    simpa only [fullGapList, Multiset.coe_card, List.length_map, List.length_range] using h
  have hne : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨c, cs, horder, hset⟩ := nonempty_finite_sites_have_ordered_list S hne
  have hndsites : (c :: cs).Nodup := horder.imp (by intro a b hab; omega)
  have horder' : (c :: cs).Pairwise (· ≤ ·) := horder.imp (by intro a b hab; omega)
  have hsort : S.sort (· ≤ ·) = c :: cs := by
    rw [← hset]
    exact (List.toFinset_sort (· ≤ ·) hndsites).mpr horder'
  have hbound : ∀ x ∈ c :: cs, x < M := by
    intro x hx
    have hxS : x ∈ S := by rw [← hset]; exact List.mem_toFinset.mpr hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hxS
    exact ZMod.val_lt y
  let g := cyclicGaps M c cs
  have hg : Multiset.ofList g = Multiset.ofList (fullGapList n) := by
    simpa only [finiteCyclicGapInventory, hsort] using hgap
  have hperm : g.Perm (fullGapList n) := Multiset.coe_eq_coe.mp hg
  have hlen : g.length = n := by simpa [fullGapList] using hperm.length_eq
  have hpos : ∀ x ∈ g, 0 < x := by
    intro x hx
    exact ((fullGapList_mem n x).mp (hperm.mem_iff.mp hx)).1
  have hsum : g.sum = M := cyclicGaps_sum M c cs horder' hbound
  have hnd : g.Nodup := hperm.nodup_iff.mpr (fullGapList_nodup n)
  obtain ⟨E, _, hEgap⟩ := cyclicRow_of_positive_word g hlen hpos hsum (by omega)
  have hinj : Function.Injective E.gap := by
    intro i j hij
    apply ZMod.val_injective n
    rw [hEgap i, hEgap j] at hij
    exact hnd.getElem_inj_iff.mp hij
  have hnat : (properPrefixSites g).toFinset.image (fun p => c + p) = S := by
    have h := congrArg List.toFinset (properPrefixSites_cyclic_inverse M c cs horder')
    have hmap : (properPrefixSites g).toFinset.image (fun p => c + p) =
        ((properPrefixSites g).map (fun p => c + p)).toFinset := by
      ext x
      simp
    rw [hmap]
    simpa only [hset] using h
  have hrow : (Motion.rotation (c : ZMod M)).onRow (wordSites M n g) = R := by
    calc
      (Motion.rotation (c : ZMod M)).onRow (wordSites M n g) =
          physicalSites M ((properPrefixSites g).toFinset.image (fun p => c + p)) := by
        rw [wordSites_eq_physicalPrefixes g hlen]
        simp only [Motion.onRow, physicalSites, Finset.image_image, Function.comp_def, Motion.act,
          Nat.cast_add]
      _ = physicalSites M S := congrArg (physicalSites M) hnat
      _ = R := physicalSites_encode R
  rw [← hrow]
  refine ⟨E.rotation (c : ZMod M), ?_, ?_⟩
  · intro i j hij
    apply hinj
    simpa only [CyclicRow.rotation_gap] using hij
  · intro d
    constructor
    · intro hd
      have hdg : d ∈ g := hperm.mem_iff.mpr hd
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hdg
      refine ⟨(j : ZMod n), ?_⟩
      rw [CyclicRow.rotation_gap, hEgap]
      have hvj : (j : ZMod n).val = j := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : j < n)]
      simpa only [hvj] using hget
    · rintro ⟨i, hi⟩
      rw [CyclicRow.rotation_gap, hEgap i] at hi
      have hdg : d ∈ g := hi ▸ List.getElem_mem (by have hiv := ZMod.val_lt i; omega)
      exact hperm.mem_iff.mp hdg

/-- The actual physical row is rigid whenever its existing sorted cyclic
gap inventory is the full pairwise-distinct inventory and `n≥3`.
The sorted-list, positive-word, wrap and ZMod representation bridges are
proved here; no cyclic-enumeration certificate is an input. -/
theorem rigidRow_of_finiteCyclicGapInventory (n : ℕ) (R : Finset (ZMod M))
    (hn : 3 ≤ n)
    (hgap : finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n)) : RigidRow R := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨E, hinj, _⟩ := cyclicRow_of_finiteCyclicGapInventory R (by omega : 2 ≤ n) hgap
  exact E.rigidRow hn hinj

/-- Every prescribed gap, including the unique maximal gap `n`, has
exactly one actual oriented tail. The `n≥2` condition is sufficient here;
the stronger `n≥3` is specifically needed for row rigidity. -/
theorem gapTails_singleton_of_finiteCyclicGapInventory (n : ℕ) (R : Finset (ZMod M))
    (hn : 2 ≤ n)
    (hgap : finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n))
    (d : ℕ) (hd0 : 0 < d) (hdn : d ≤ n) :
    ∃ x : ZMod M, gapTails R d = {x} := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨E, hinj, hvalues⟩ := cyclicRow_of_finiteCyclicGapInventory R hn hgap
  obtain ⟨i, hi⟩ := (hvalues d).mp ((fullGapList_mem n d).mpr ⟨hd0, hdn⟩)
  refine ⟨E.site i, ?_⟩
  simpa only [hi] using E.gapTails_singleton hinj i

namespace CyclicRow

variable {n : ℕ} [NeZero n] {R : Finset (ZMod M)}

omit [NeZero M] in
theorem hasGapNeighborPair (E : CyclicRow n R) (i : ZMod n) :
    HasGapNeighborPair R (E.gap i) {E.gap (i - 1), E.gap (i + 1)} := by
  refine ⟨E.site (i - 1), E.site i, E.site (i + 1), E.site (i + 1 + 1),
    ?_, E.consecutive i, E.consecutive (i + 1), rfl, ?_⟩
  · simpa only [sub_add_cancel] using E.consecutive (i - 1)
  · simp only [gap, sub_add_cancel]

/-- An injective gap inventory makes the neighbor pair a well-defined
invariant at every prescribed gap, hence at the unique maximum. -/
theorem hasGapNeighborPair_iff (E : CyclicRow n R) (hg : Function.Injective E.gap)
    (i : ZMod n) (pair : Finset ℕ) :
    HasGapNeighborPair R (E.gap i) pair ↔ pair = {E.gap (i - 1), E.gap (i + 1)} := by
  constructor
  · rintro ⟨w, x, y, z, hwx, hxy, hyz, hd, hp⟩
    obtain ⟨j, hjx, hjy⟩ := (E.adjacent_iff x y).mp hxy
    have hji : j = i := hg (by simpa only [gap, hjx, hjy] using hd)
    subst j
    subst x
    subst y
    have hprev : Adjacent R (E.site (i - 1)) (E.site i) := by
      simpa only [sub_add_cancel] using E.consecutive (i - 1)
    have hw : w = E.site (i - 1) := adjacent_unique_tail hwx hprev
    have hz : z = E.site (i + 1 + 1) := adjacent_unique_head hyz (E.consecutive (i + 1))
    subst w
    subst z
    simpa only [gap, sub_add_cancel] using hp.symm
  · rintro rfl
    exact E.hasGapNeighborPair i

theorem gapTails_eq_image (E : CyclicRow n R) (d : ℕ) :
    gapTails R d = (univ.filter (fun i : ZMod n => E.gap i = d)).image E.site := by
  classical
  ext x
  simp only [mem_gapTails, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨y, hxy, hd⟩
    obtain ⟨i, hx, hy⟩ := (E.adjacent_iff x y).mp hxy
    exact ⟨i, by simpa only [gap, hx, hy] using hd, hx⟩
  · rintro ⟨i, hd, rfl⟩
    exact ⟨E.site (i + 1), E.consecutive i, hd⟩

end CyclicRow

/-- Exact transfer of actual physical gap tails from the positive word.
Only the proper prefixes at positions with value `d` enter the answer. -/
theorem gapTails_wordSites {n : ℕ} [NeZero n] (g : List ℕ)
    (hlen : g.length = n) (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum = M)
    (hn : 2 ≤ n) (d : ℕ) :
    gapTails (wordSites M n g) d =
      (univ.filter (fun i : ZMod n =>
        g[i.val]'(by have hi := ZMod.val_lt i; omega) = d)).image
          (fun i => (((g.take i.val).sum : ℕ) : ZMod M)) := by
  obtain ⟨E, hsite, hgap⟩ := cyclicRow_of_positive_word g hlen hpos hsum hn
  have hsitefun : E.site = fun i => (((g.take i.val).sum : ℕ) : ZMod M) := funext hsite
  simpa only [hsitefun, hgap] using E.gapTails_eq_image d

/-- The same exact formula with an arbitrary physical starting point.
This supplies parameter-independent tails whenever the distinguished-gap
positions and the corresponding proper-prefix sums stay fixed. -/
theorem gapTails_translated_positive_word {n : ℕ} [NeZero n] (g : List ℕ)
    (hlen : g.length = n) (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum = M)
    (hn : 2 ≤ n) (c : ZMod M) (d : ℕ) :
    gapTails ((Motion.rotation c).onRow (physicalSites M (properPrefixSites g).toFinset)) d =
      (univ.filter (fun i : ZMod n =>
        g[i.val]'(by have hi := ZMod.val_lt i; omega) = d)).image
          (fun i => c + (((g.take i.val).sum : ℕ) : ZMod M)) := by
  rw [gapTails_rotation, ← wordSites_eq_physicalPrefixes g hlen,
    gapTails_wordSites g hlen hpos hsum hn d, Finset.image_image]
  rfl

/-- Complete inventories supply one unambiguous unordered neighbor pair
at their unique maximal gap, as an actual physical-row property. Its
invariance under every Motion is `hasGapNeighborPair_motion_iff`. -/
theorem unique_max_gap_neighbor_pair (n : ℕ) (R : Finset (ZMod M)) (hn : 2 ≤ n)
    (hgap : finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n)) :
    ∃! pair : Finset ℕ, HasGapNeighborPair R n pair := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨E, hinj, hvalues⟩ := cyclicRow_of_finiteCyclicGapInventory R hn hgap
  obtain ⟨i, hi⟩ := (hvalues n).mp ((fullGapList_mem n n).mpr ⟨by omega, le_rfl⟩)
  refine ⟨{E.gap (i - 1), E.gap (i + 1)}, ?_, ?_⟩
  · simpa only [hi] using E.hasGapNeighborPair i
  · intro pair hp
    apply (E.hasGapNeighborPair_iff hinj i pair).mp
    simpa only [hi] using hp

end CorralFormalization.DiversitySymmetry
