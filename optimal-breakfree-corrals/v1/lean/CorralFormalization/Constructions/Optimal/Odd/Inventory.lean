import CorralFormalization.Constructions.Optimal.Odd.Word

namespace CorralFormalization

/-- An arithmetic progression of step four over a finite range has no
repeated value. -/
theorem oddConstructionMap4_nodup (n c : ℕ) :
    ((List.range n).map (fun j => 4 * j + c)).Nodup := by
  apply List.Nodup.map
  · intro i j hij
    dsimp at hij
    omega
  · exact List.nodup_range

/-- Two step-four progressions with different residues are disjoint. -/
theorem oddConstructionMap4_disjoint (n m c d : ℕ) (hcd : c % 4 ≠ d % 4) :
    ∀ x ∈ (List.range n).map (fun j => 4 * j + c),
      ∀ y ∈ (List.range m).map (fun j => 4 * j + d), x ≠ y := by
  intro x hx y hy hxy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
  have hmod : c % 4 = d % 4 := by omega
  exact hcd hmod

/-- The four canonical residue streams contain no repetitions, including
across different streams. -/
theorem oddConstructionCanonicalInventory_nodup (A : ℕ) :
    (oddConstructionGapCanonicalInventory A).Nodup := by
  let c0 := oddConstructionInventoryCanonicalClass0 A
  let c2 := oddConstructionInventoryCanonicalClass2 A
  let c1 := oddConstructionInventoryCanonicalClass1 A
  let c3 := oddConstructionInventoryCanonicalClass3 A
  have h0 : c0.Nodup := oddConstructionMap4_nodup (A + 1) 4
  have h2 : c2.Nodup := oddConstructionMap4_nodup (A + 1) 2
  have h1 : c1.Nodup := oddConstructionMap4_nodup (A + 2) 1
  have h3 : c3.Nodup := oddConstructionMap4_nodup (A - 1) 7
  have h02 := oddConstructionMap4_disjoint (A + 1) (A + 1) 4 2 (by decide)
  have h01 := oddConstructionMap4_disjoint (A + 1) (A + 2) 4 1 (by decide)
  have h03 := oddConstructionMap4_disjoint (A + 1) (A - 1) 4 7 (by decide)
  have h21 := oddConstructionMap4_disjoint (A + 1) (A + 2) 2 1 (by decide)
  have h23 := oddConstructionMap4_disjoint (A + 1) (A - 1) 2 7 (by decide)
  have h13 := oddConstructionMap4_disjoint (A + 2) (A - 1) 1 7 (by decide)
  have h0rest : ∀ x ∈ c0, ∀ y ∈ c2 ++ c1 ++ c3, x ≠ y := by
    intro x hx y hy
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · rcases hy with hy | hy
      · exact h02 x hx y hy
      · exact h01 x hx y hy
    · exact h03 x hx y hy
  have h2rest : ∀ x ∈ c2, ∀ y ∈ c1 ++ c3, x ≠ y := by
    intro x hx y hy
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · exact h21 x hx y hy
    · exact h23 x hx y hy
  change (c0 ++ c2 ++ c1 ++ c3).Nodup
  have hright : (c0 ++ (c2 ++ (c1 ++ c3))).Nodup :=
    List.nodup_append.mpr ⟨h0, List.nodup_append.mpr
      ⟨h2, List.nodup_append.mpr ⟨h1, h3, h13⟩, h2rest⟩, by
        intro x hx y hy
        exact h0rest x hx y (by simpa [List.append_assoc] using hy)⟩
  simpa only [List.append_assoc] using hright

/-- The explicit interval inventory `[4A+5]` with `3` and `4A+3` removed. -/
def oddConstructionAllowedGapInventory (A : ℕ) : List ℕ :=
  (List.range (4 * A + 6)).filter
    (fun x => decide (0 < x ∧ x ≠ 3 ∧ x ≠ 4 * A + 3))

theorem oddConstructionAllowedGapInventory_nodup (A : ℕ) :
    (oddConstructionAllowedGapInventory A).Nodup := by
  exact List.Nodup.filter _ List.nodup_range

/-- The four bounded residue streams contain precisely the allowed gap
values of the paper, with the endpoint and both exclusions explicit. -/
theorem oddConstructionCanonicalInventory_mem (A x : ℕ) (hA : 2 ≤ A) :
    x ∈ oddConstructionGapCanonicalInventory A ↔
      0 < x ∧ x ≤ 4 * A + 5 ∧ x ≠ 3 ∧ x ≠ 4 * A + 3 := by
  simp only [oddConstructionGapCanonicalInventory, oddConstructionInventoryCanonicalClass0,
    oddConstructionInventoryCanonicalClass2, oddConstructionInventoryCanonicalClass1,
    oddConstructionInventoryCanonicalClass3, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · rintro ⟨hxpos, hxhi, hx3, hxK⟩
    have hmod : x % 4 = 0 ∨ x % 4 = 2 ∨ x % 4 = 1 ∨ x % 4 = 3 := by omega
    rcases hmod with h0 | h2 | h1 | h3
    · left; left; left
      refine ⟨(x - 4) / 4, ?_, ?_⟩ <;> omega
    · left; left; right
      refine ⟨(x - 2) / 4, ?_, ?_⟩ <;> omega
    · left; right
      refine ⟨(x - 1) / 4, ?_, ?_⟩ <;> omega
    · right
      refine ⟨(x - 7) / 4, ?_, ?_⟩ <;> omega

theorem oddConstructionAllowedGapInventory_mem (A x : ℕ) :
    x ∈ oddConstructionAllowedGapInventory A ↔
      0 < x ∧ x ≤ 4 * A + 5 ∧ x ≠ 3 ∧ x ≠ 4 * A + 3 := by
  simp [oddConstructionAllowedGapInventory, List.mem_filter, List.mem_range]
  omega

/-- The canonical streams enumerate the ordinary interval inventory once
each, with exactly the two printed exclusions. -/
theorem oddConstructionCanonicalInventory_perm_allowed (A : ℕ) (hA : 2 ≤ A) :
    (oddConstructionGapCanonicalInventory A).Perm (oddConstructionAllowedGapInventory A) := by
  apply (List.perm_ext_iff_of_nodup (oddConstructionCanonicalInventory_nodup A)
    (oddConstructionAllowedGapInventory_nodup A)).2
  intro x
  rw [oddConstructionCanonicalInventory_mem A x hA, oddConstructionAllowedGapInventory_mem A x]

/-- The actual printed word has exactly the paper's interval gap inventory,
including multiplicity one for every allowed value. -/
theorem oddConstructionGapWord_perm_allowed (A : ℕ) (hA : 2 ≤ A) :
    (oddConstructionGapWord A).Perm (oddConstructionAllowedGapInventory A) :=
  (oddConstructionGapWord_perm_inventory A hA).trans
    ((oddConstructionGapInventory_perm_canonical A hA).trans
      (oddConstructionCanonicalInventory_perm_allowed A hA))

/-- The complete set of gap lengths `[4A+5]`, in increasing order. -/
def oddConstructionFullGapInventory (A : ℕ) : List ℕ :=
  (List.range (4 * A + 6)).filter (fun x => decide (0 < x))

theorem oddConstructionFullGapInventory_eq_range (A : ℕ) :
    oddConstructionFullGapInventory A = (List.range (4 * A + 5)).map (fun j => j + 1) := by
  unfold oddConstructionFullGapInventory
  have hlen : 4 * A + 6 = (4 * A + 5) + 1 := by omega
  rw [hlen, List.range_succ_eq_map]
  simp [List.filter_map, Function.comp_def, Nat.succ_eq_add_one]

theorem oddConstructionFullGapInventory_nodup (A : ℕ) :
    (oddConstructionFullGapInventory A).Nodup :=
  List.Nodup.filter _ List.nodup_range

/-- Adding the two missing gaps gives every required gap exactly once. -/
theorem oddConstructionAllowed_plus_missing_perm_full (A : ℕ) (hA : 2 ≤ A) :
    (oddConstructionAllowedGapInventory A ++ [3, 4 * A + 3]).Perm
      (oddConstructionFullGapInventory A) := by
  have hmissing : ([3, 4 * A + 3] : List ℕ).Nodup := by simp; omega
  have hdisjoint : ∀ x ∈ oddConstructionAllowedGapInventory A,
      ∀ y ∈ ([3, 4 * A + 3] : List ℕ), x ≠ y := by
    intro x hx y hy heq
    have hallowed := (oddConstructionAllowedGapInventory_mem A x).1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy <;> omega
  have hnodup : (oddConstructionAllowedGapInventory A ++ [3, 4 * A + 3]).Nodup :=
    List.nodup_append.mpr ⟨oddConstructionAllowedGapInventory_nodup A, hmissing, hdisjoint⟩
  apply (List.perm_ext_iff_of_nodup hnodup (oddConstructionFullGapInventory_nodup A)).2
  intro x
  simp only [List.mem_append, oddConstructionAllowedGapInventory_mem,
    List.mem_cons, List.not_mem_nil, or_false, oddConstructionFullGapInventory,
    List.mem_filter, List.mem_range, decide_eq_true_eq]
  omega

theorem oddConstructionWord_plus_missing_inventory (A : ℕ) (hA : 2 ≤ A) :
    Multiset.ofList (oddConstructionGapWord A) + Multiset.ofList [3, 4 * A + 3] =
      Multiset.ofList (oddConstructionFullGapInventory A) := by
  rw [Multiset.coe_add]
  apply Multiset.coe_eq_coe.mpr
  exact ((oddConstructionGapWord_perm_allowed A hA).append_right [3, 4 * A + 3]).trans
    (oddConstructionAllowed_plus_missing_perm_full A hA)

end CorralFormalization
