import Mathlib
import CorralFormalization.ConstructionSupport.PhysicalRows

namespace CorralFormalization.DiversitySymmetry

open Finset
open CorralFormalization.PhysicalCorral

variable {M : ℕ} [NeZero M]

/-- Positive clockwise distance on the actual physical clock. -/
def gapLength (x y : ZMod M) : ℕ := (y - x).val

/-- Strictly inside the clockwise arc from `x` to `y`. -/
def insideArc (x z y : ZMod M) : Prop :=
  0 < gapLength x z ∧ gapLength x z < gapLength x y

/-- Actual consecutive physical sites, including the edge across zero.
There is no preferred cut of the circle in this definition. -/
def Adjacent (R : Finset (ZMod M)) (x y : ZMod M) : Prop :=
  x ∈ R ∧ y ∈ R ∧ x ≠ y ∧ ∀ z ∈ R, ¬ insideArc x z y

omit [NeZero M] in
theorem gapLength_pos {x y : ZMod M} (hxy : x ≠ y) : 0 < gapLength x y := by
  unfold gapLength
  exact Nat.pos_of_ne_zero (fun h => hxy (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h)).symm)

omit [NeZero M] in
@[simp] theorem gapLength_rotation (c x y : ZMod M) :
    gapLength (c + x) (c + y) = gapLength x y := by
  unfold gapLength
  congr 1
  ring

omit [NeZero M] in
@[simp] theorem gapLength_reflection (c x y : ZMod M) :
    gapLength (c - y) (c - x) = gapLength x y := by
  unfold gapLength
  congr 1
  ring

omit [NeZero M] in
theorem insideArc_rotation (c x z y : ZMod M) :
    insideArc (c + x) (c + z) (c + y) ↔ insideArc x z y := by
  simp [insideArc]

theorem insideArc_reflection (c x z y : ZMod M) :
    insideArc (c - y) (c - z) (c - x) ↔ insideArc x z y := by
  have hforward : ∀ a b d : ZMod M, insideArc a b d →
      insideArc (c - d) (c - b) (c - a) := by
    intro a b d h
    obtain ⟨hpos, hlt⟩ := h
    have hsub : d - b = (d - a) - (b - a) := by ring
    have hv : gapLength (c - d) (c - b) = gapLength a d - gapLength a b := by
      unfold gapLength
      have heq : (c - b) - (c - d) = (d - a) - (b - a) := by ring
      rw [heq, ZMod.val_sub (Nat.le_of_lt hlt)]
    rw [insideArc, hv, gapLength_reflection]
    omega
  constructor
  · intro h
    have h' := hforward (c - y) (c - z) (c - x) h
    simpa using h'
  · exact hforward x z y

omit [NeZero M] in
theorem adjacent_rotation {R : Finset (ZMod M)} {x y : ZMod M}
    (h : Adjacent R x y) (c : ZMod M) :
    Adjacent ((Motion.rotation c).onRow R) (c + x) (c + y) := by
  obtain ⟨hx, hy, hxy, hempty⟩ := h
  refine ⟨mem_image.mpr ⟨x, hx, rfl⟩, mem_image.mpr ⟨y, hy, rfl⟩,
    (add_right_injective c).ne hxy, ?_⟩
  intro z hz hzarc
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
  exact hempty w hw ((insideArc_rotation c x w y).mp hzarc)

theorem adjacent_reflection {R : Finset (ZMod M)} {x y : ZMod M}
    (h : Adjacent R x y) (c : ZMod M) :
    Adjacent ((Motion.reflection c).onRow R) (c - y) (c - x) := by
  obtain ⟨hx, hy, hxy, hempty⟩ := h
  refine ⟨mem_image.mpr ⟨y, hy, rfl⟩, mem_image.mpr ⟨x, hx, rfl⟩, ?_, ?_⟩
  · intro h
    exact hxy (sub_right_injective h).symm
  intro z hz hzarc
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
  exact hempty w hw ((insideArc_reflection c x w y).mp hzarc)

/-- The geometric successor is unique; this uses actual distances and
the empty arc, rather than an assumed permutation of gap positions. -/
theorem adjacent_unique_head {R : Finset (ZMod M)} {x y z : ZMod M}
    (hy : Adjacent R x y) (hz : Adjacent R x z) : y = z := by
  have hdy := gapLength_pos hy.2.2.1
  have hdz := gapLength_pos hz.2.2.1
  have hle : gapLength x y ≤ gapLength x z := by
    by_contra h
    exact hy.2.2.2 z hz.2.1 ⟨hdz, Nat.lt_of_not_ge h⟩
  have hge : gapLength x z ≤ gapLength x y := by
    by_contra h
    exact hz.2.2.2 y hy.2.1 ⟨hdy, Nat.lt_of_not_ge h⟩
  have heq : y - x = z - x := ZMod.val_injective M (Nat.le_antisymm hle hge)
  exact sub_left_injective heq

theorem adjacent_unique_tail {R : Finset (ZMod M)} {x y z : ZMod M}
    (hx : Adjacent R x z) (hy : Adjacent R y z) : x = y := by
  have h := adjacent_unique_head (adjacent_reflection hx 0) (adjacent_reflection hy 0)
  simpa using congrArg Neg.neg h

/-- The concrete unordered pair of gaps on either side of a distinguished
gap of length `d`. A unique maximum is a particular distinguished gap;
the covariance is valid for every `d`. -/
def HasGapNeighborPair (R : Finset (ZMod M)) (d : ℕ) (pair : Finset ℕ) : Prop :=
  ∃ w x y z : ZMod M,
    Adjacent R w x ∧ Adjacent R x y ∧ Adjacent R y z ∧
      gapLength x y = d ∧ {gapLength w x, gapLength y z} = pair

omit [NeZero M] in
theorem hasGapNeighborPair_rotation_forward (R : Finset (ZMod M))
    (c : ZMod M) (d : ℕ) (pair : Finset ℕ)
    (h : HasGapNeighborPair R d pair) :
    HasGapNeighborPair ((Motion.rotation c).onRow R) d pair := by
  obtain ⟨w, x, y, z, hwx, hxy, hyz, hd, hp⟩ := h
  refine ⟨c + w, c + x, c + y, c + z, adjacent_rotation hwx c,
    adjacent_rotation hxy c, adjacent_rotation hyz c, ?_, ?_⟩
  · simpa using hd
  · simpa using hp

theorem hasGapNeighborPair_reflection_forward (R : Finset (ZMod M))
    (c : ZMod M) (d : ℕ) (pair : Finset ℕ)
    (h : HasGapNeighborPair R d pair) :
    HasGapNeighborPair ((Motion.reflection c).onRow R) d pair := by
  obtain ⟨w, x, y, z, hwx, hxy, hyz, hd, hp⟩ := h
  refine ⟨c - z, c - y, c - x, c - w, adjacent_reflection hyz c,
    adjacent_reflection hxy c, adjacent_reflection hwx c, ?_, ?_⟩
  · simpa using hd
  · simpa only [gapLength_reflection, pair_comm] using hp

/-- The marker hypothesis in `marked_seed_reduction` is now paid for this
specific, geometric gap-neighbor marker, for every physical motion. -/
theorem hasGapNeighborPair_motion_iff (f : Motion M) (R : Finset (ZMod M))
    (d : ℕ) (pair : Finset ℕ) :
    HasGapNeighborPair (f.onRow R) d pair ↔ HasGapNeighborPair R d pair := by
  cases f with
  | rotation c =>
    constructor
    · intro h
      have h' := hasGapNeighborPair_rotation_forward _ (-c) d pair h
      simpa [← Motion.onRow_compose, Motion.compose] using h'
    · exact hasGapNeighborPair_rotation_forward R c d pair
  | reflection c =>
    constructor
    · intro h
      have h' := hasGapNeighborPair_reflection_forward _ c d pair h
      simpa only [Motion.reflection_onRow_involutive c R] using h'
    · exact hasGapNeighborPair_reflection_forward R c d pair

/-- All actual tails of directed consecutive gaps of the prescribed length.
Uniqueness of a maximum is not needed for the transformation law. -/
noncomputable def gapTails (R : Finset (ZMod M)) (d : ℕ) : Finset (ZMod M) := by
  classical
  exact R.filter fun x => ∃ y, Adjacent R x y ∧ gapLength x y = d

@[simp] theorem mem_gapTails (R : Finset (ZMod M)) (d : ℕ) (x : ZMod M) :
    x ∈ gapTails R d ↔ ∃ y, Adjacent R x y ∧ gapLength x y = d := by
  classical
  simp only [gapTails, mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.choose_spec.1.1, h⟩

/-- The head of an actual gap of natural length `d` is `tail+d` modulo
the physical clock; this pays the reflection's additional `-d` term. -/
theorem head_eq_tail_add {x y : ZMod M} {d : ℕ} (h : gapLength x y = d) :
    y = x + (d : ZMod M) := by
  have hcast : (d : ZMod M) = y - x := by
    rw [← h]
    exact ZMod.natCast_zmod_val _
  rw [hcast]
  ring

theorem gapTails_rotation_image_subset (R : Finset (ZMod M)) (c : ZMod M) (d : ℕ) :
    (gapTails R d).image (fun x => c + x) ⊆ gapTails ((Motion.rotation c).onRow R) d := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
  obtain ⟨b, hab, hd⟩ := (mem_gapTails R d a).mp ha
  exact (mem_gapTails _ _ _).mpr ⟨c + b, adjacent_rotation hab c, by simpa using hd⟩

theorem gapTails_reflection_image_subset (R : Finset (ZMod M)) (c : ZMod M) (d : ℕ) :
    (gapTails R d).image (fun x => c - (d : ZMod M) - x) ⊆
      gapTails ((Motion.reflection c).onRow R) d := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
  obtain ⟨b, hab, hd⟩ := (mem_gapTails R d a).mp ha
  have hb := head_eq_tail_add hd
  have htail : c - b = c - (d : ZMod M) - a := by rw [hb]; ring
  rw [← htail]
  exact (mem_gapTails _ _ _).mpr ⟨c - a, adjacent_reflection hab c, by simpa using hd⟩

/-- Literal transformation law for oriented gap tails under translation. -/
theorem gapTails_rotation (R : Finset (ZMod M)) (c : ZMod M) (d : ℕ) :
    gapTails ((Motion.rotation c).onRow R) d =
      (gapTails R d).image (fun x => c + x) := by
  classical
  apply subset_antisymm _ (gapTails_rotation_image_subset R c d)
  have hback := gapTails_rotation_image_subset ((Motion.rotation c).onRow R) (-c) d
  have hrow : (Motion.rotation (-c)).onRow ((Motion.rotation c).onRow R) = R := by
    rw [← Motion.onRow_compose]
    simp [Motion.compose]
  rw [hrow] at hback
  intro x hx
  have hxback := hback (mem_image.mpr ⟨x, hx, rfl⟩)
  exact mem_image.mpr ⟨-c + x, hxback, by ring⟩

/-- Literal transformation law for oriented gap tails under reflection.
The correct new tail is `c-d-x`, not `c-x`. -/
theorem gapTails_reflection (R : Finset (ZMod M)) (c : ZMod M) (d : ℕ) :
    gapTails ((Motion.reflection c).onRow R) d =
      (gapTails R d).image (fun x => c - (d : ZMod M) - x) := by
  classical
  apply subset_antisymm _ (gapTails_reflection_image_subset R c d)
  have hback := gapTails_reflection_image_subset ((Motion.reflection c).onRow R) c d
  rw [Motion.reflection_onRow_involutive c R] at hback
  intro x hx
  have hxback := hback (mem_image.mpr ⟨x, hx, rfl⟩)
  exact mem_image.mpr ⟨c - (d : ZMod M) - x, hxback, by ring⟩

/-- Noncircular geometric certificate: an actual cyclic enumeration of all
row points, and actual consecutive-site edges. Distinctness of the gap
function is a separate local inventory hypothesis, not row rigidity. -/
structure CyclicRow (n : ℕ) [NeZero n] (R : Finset (ZMod M)) where
  site : ZMod n → ZMod M
  injective : Function.Injective site
  range : ∀ x, x ∈ R ↔ ∃ i, site i = x
  consecutive : ∀ i, Adjacent R (site i) (site (i + 1))

namespace CyclicRow

variable {n : ℕ} [NeZero n] {R : Finset (ZMod M)}

def gap (E : CyclicRow n R) (i : ZMod n) : ℕ := gapLength (E.site i) (E.site (i + 1))

theorem adjacent_iff (E : CyclicRow n R) (x y : ZMod M) :
    Adjacent R x y ↔ ∃ i, E.site i = x ∧ E.site (i + 1) = y := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (E.range x).mp h.1
    refine ⟨i, hi, ?_⟩
    apply adjacent_unique_head (E.consecutive i)
    simpa only [hi] using h
  · rintro ⟨i, rfl, rfl⟩
    exact E.consecutive i

theorem gapTails_singleton (E : CyclicRow n R) (hg : Function.Injective E.gap)
    (i : ZMod n) : gapTails R (E.gap i) = {E.site i} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hxy, hgap⟩ := (mem_gapTails _ _ _).mp hx
    obtain ⟨j, hjx, hjy⟩ := (E.adjacent_iff x y).mp hxy
    have hji : j = i := hg (by simpa only [gap, hjx, hjy] using hgap)
    exact mem_singleton.mpr (by simpa only [hji] using hjx.symm)
  · intro hx
    obtain rfl := mem_singleton.mp hx
    exact (mem_gapTails _ _ _).mpr ⟨E.site (i + 1), E.consecutive i, rfl⟩

/-- Translation of a concrete cyclic enumeration preserves its physical
consecutiveness and its gap function. -/
def rotation (E : CyclicRow n R) (c : ZMod M) :
    CyclicRow n ((Motion.rotation c).onRow R) where
  site i := c + E.site i
  injective := (add_right_injective c).comp E.injective
  range := by
    intro x
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      obtain ⟨i, rfl⟩ := (E.range y).mp hy
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact mem_image.mpr ⟨E.site i, (E.range _).mpr ⟨i, rfl⟩, rfl⟩
  consecutive i := adjacent_rotation (E.consecutive i) c

@[simp] theorem rotation_gap (E : CyclicRow n R) (c : ZMod M) (i : ZMod n) :
    (E.rotation c).gap i = E.gap i := by
  exact gapLength_rotation c _ _

theorem rigidRow (E : CyclicRow n R) (hn : 3 ≤ n)
    (hg : Function.Injective E.gap) : RigidRow R := by
  intro f hf
  have hneq : (2 : ZMod n) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hval : (2 : ZMod n).val = 2 := by
      change ((2 : ℕ) : ZMod n).val = 2
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 2 < n)]
    rw [hval, ZMod.val_zero] at hv
    omega
  cases f with
  | rotation c =>
    have hpoint : ∀ i : ZMod n, c + E.site i = E.site i := by
      intro i
      have ha := adjacent_rotation (E.consecutive i) c
      rw [hf] at ha
      obtain ⟨j, hj⟩ := (E.range _).mp ha.1
      have hhead : E.site (j + 1) = c + E.site (i + 1) := by
        apply adjacent_unique_head (E.consecutive j)
        simpa only [hj] using ha
      have hgap : E.gap j = E.gap i := by
        simp only [gap, hj, hhead, gapLength_rotation]
      have hji := hg hgap
      simpa only [hji] using hj.symm
    have hc : c = 0 := by
      have h := hpoint 0
      exact add_right_cancel (show c + E.site 0 = 0 + E.site 0 by simpa using h)
    subst c
    rfl
  | reflection c =>
    have hswap : ∀ i : ZMod n,
        c - E.site (i + 1) = E.site i ∧ c - E.site i = E.site (i + 1) := by
      intro i
      have ha := adjacent_reflection (E.consecutive i) c
      rw [hf] at ha
      obtain ⟨j, hj⟩ := (E.range _).mp ha.1
      have hhead : E.site (j + 1) = c - E.site i := by
        apply adjacent_unique_head (E.consecutive j)
        simpa only [hj] using ha
      have hgap : E.gap j = E.gap i := by
        simp only [gap, hj, hhead, gapLength_reflection]
      have hji := hg hgap
      constructor
      · simpa only [hji] using hj.symm
      · simpa only [hji] using hhead.symm
    have h0 := (hswap 0).1
    simp only [zero_add] at h0
    have h := h0.symm.trans (hswap 1).2
    have heq : E.site 0 = E.site 2 := by simpa only [one_add_one_eq_two] using h
    exact False.elim (hneq (E.injective heq).symm)

end CyclicRow

end CorralFormalization.DiversitySymmetry
