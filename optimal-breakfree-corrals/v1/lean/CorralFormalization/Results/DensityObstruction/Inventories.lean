import CorralFormalization.Results.DensityObstruction.CyclicClasses

namespace CorralFormalization.Results.DensityObstruction

open scoped BigOperators

def vertices {h : ℕ} [NeZero (3*h)] (T : Finset (ZMod (3*h))) : Finset (ZMod (3*h)) :=
  (residueClass h 0 ∪ residueClass h 1) ∪ T

def colors {h : ℕ} [NeZero (3*h)] (T : Finset (ZMod (3*h))) : Finset (ZMod (3*h)) :=
  (vertices T).erase 0

theorem zero_mem_vertices {h : ℕ} [NeZero (3*h)] (T : Finset (ZMod (3*h))) :
    0 ∈ vertices T := by simp [vertices, mem_residueClass]

theorem zero_not_mem_colors {h : ℕ} [NeZero (3*h)] (T : Finset (ZMod (3*h))) :
    0 ∉ colors T := by simp [colors]

theorem colors_card_add_one {h : ℕ} [NeZero (3*h)] (T : Finset (ZMod (3*h))) :
    (colors T).card + 1 = (vertices T).card := by
  exact Finset.card_erase_add_one (zero_mem_vertices T)

theorem twoClass_disjoint_base {h : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (hT : T ⊆ residueClass h 2) :
    Disjoint (residueClass h 0 ∪ residueClass h 1) T := by
  apply Finset.disjoint_union_left.mpr
  constructor
  · exact (residueClass_disjoint 0 2 (by decide)).mono_right hT
  · exact (residueClass_disjoint 1 2 (by decide)).mono_right hT

theorem vertices_card {h a : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (hT : T ⊆ residueClass h 2) (hcard : T.card = a) :
    (vertices T).card = 2*h+a := by
  rw [vertices, Finset.card_union_of_disjoint (twoClass_disjoint_base T hT),
    Finset.card_union_of_disjoint (residueClass_disjoint 0 1 (by decide)),
    residueClass_card, residueClass_card, hcard]
  omega

theorem vertices_filter_two {h : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (hT : T ⊆ residueClass h 2) :
    (vertices T).filter (fun z => residue h z = 2) = T := by
  ext z
  constructor
  · intro hz
    obtain ⟨hz, htwo⟩ := Finset.mem_filter.mp hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · have hzero := (mem_residueClass 0 z).mp hz
        have : (0 : ZMod 3) = 2 := hzero.symm.trans htwo
        exact False.elim ((by decide : (0 : ZMod 3) ≠ 2) this)
      · have hone := (mem_residueClass 1 z).mp hz
        have : (1 : ZMod 3) = 2 := hone.symm.trans htwo
        exact False.elim ((by decide : (1 : ZMod 3) ≠ 2) this)
    · exact hz
  · intro hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hz,
      (mem_residueClass 2 z).mp (hT hz)⟩

theorem vertices_filter_one {h : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (_hT : T ⊆ residueClass h 2) :
    (vertices T).filter (fun z => residue h z = 1) = residueClass h 1 := by
  ext z
  constructor
  · intro hz
    exact (mem_residueClass 1 z).mpr (Finset.mem_filter.mp hz).2
  · intro hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hz),
      (mem_residueClass 1 z).mp hz⟩

theorem colors_filter_nonzero {h : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (r : ZMod 3) (hr : r ≠ 0) :
    (colors T).filter (fun z => residue h z = r) =
      (vertices T).filter (fun z => residue h z = r) := by
  ext z
  simp only [colors, Finset.mem_filter, Finset.mem_erase]
  constructor
  · exact fun hz => ⟨hz.1.2, hz.2⟩
  · intro hz
    refine ⟨⟨?_, hz.1⟩, hz.2⟩
    intro he
    subst z
    exact hr (by simpa using hz.2.symm)

theorem colors_filter_one {h : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (hT : T ⊆ residueClass h 2) :
    (colors T).filter (fun z => residue h z = 1) = residueClass h 1 := by
  rw [colors_filter_nonzero T 1 (by decide), vertices_filter_one T hT]

theorem colors_filter_two {h : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (hT : T ⊆ residueClass h 2) :
    (colors T).filter (fun z => residue h z = 2) = T := by
  rw [colors_filter_nonzero T 2 (by decide), vertices_filter_two T hT]

theorem sum_residueClass {h : ℕ} [NeZero (3*h)] (r : ZMod 3) :
    (∑ z ∈ residueClass h r, residue h z) = h • r := by
  calc
    _ = ∑ _z ∈ residueClass h r, r := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (mem_residueClass r z).mp hz
    _ = h • r := by simp [residueClass_card]

theorem colors_sum_residue {h a : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (hT : T ⊆ residueClass h 2) (hcard : T.card = a) :
    residue h (∑ d ∈ colors T, d) = (h : ZMod 3) + 2*a := by
  rw [map_sum]
  have hs : (∑ d ∈ colors T, residue h d) = ∑ z ∈ vertices T, residue h z := by
    have h := Finset.sum_erase_add (vertices T) (fun z => residue h z) (zero_mem_vertices T)
    simpa [colors] using h
  rw [hs, vertices, Finset.sum_union (twoClass_disjoint_base T hT),
    Finset.sum_union (residueClass_disjoint 0 1 (by decide)),
    sum_residueClass, sum_residueClass]
  have hts : (∑ z ∈ T, residue h z) = a • (2 : ZMod 3) := by
    calc
      _ = ∑ _z ∈ T, (2 : ZMod 3) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (mem_residueClass 2 z).mp (hT hz)
      _ = _ := by simp [hcard]
  rw [hts]
  simp [nsmul_eq_mul, mul_comm]

/-- The full sum in the original cyclic group, not only its mod-three image. -/
theorem colors_sum {h : ℕ} [NeZero (3*h)]
    (T : Finset (ZMod (3*h))) (hT : T ⊆ residueClass h 2) :
    (∑ d ∈ colors T, d) = (h : ZMod (3*h)) + ∑ z ∈ T, z := by
  have hs : (∑ d ∈ colors T, d) = ∑ z ∈ vertices T, z := by
    have h := Finset.sum_erase_add (vertices T) (fun z => z) (zero_mem_vertices T)
    simpa [colors] using h
  rw [hs, vertices, Finset.sum_union (twoClass_disjoint_base T hT),
    Finset.sum_union (residueClass_disjoint 0 1 (by decide)), sum_classes_zero_one]

end CorralFormalization.Results.DensityObstruction
