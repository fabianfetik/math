import CorralFormalization.GapPermutation
import CorralFormalization.Arithmetic

namespace CorralFormalization

theorem fullGapList_succ (n : ℕ) :
    fullGapList (n + 1) = fullGapList n ++ [n + 1] := by
  simp [fullGapList, List.range_succ]

theorem fullGapList_sum (n : ℕ) : (fullGapList n).sum = width n := by
  induction n with
  | zero => simp [fullGapList, width]
  | succ n ih => simp [fullGapList_succ, ih, width_succ]

/-- A permutation in the original predicate, as its actual ordered positive
gap word. The one-based values are preserved. -/
def permutationWord {n : ℕ} (ρ : Equiv.Perm (Fin n)) : List ℕ :=
  List.ofFn (fun j => (ρ j).val + 1)

theorem permutationWord_length {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    (permutationWord ρ).length = n := by simp [permutationWord]

theorem permutationWord_range {n : ℕ} (ρ : Equiv.Perm (Fin n))
    (x : ℕ) (hx : x ∈ permutationWord ρ) : 0 < x ∧ x ≤ n := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  have hlt := (ρ j).isLt
  omega

theorem permutationWord_nodup {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    (permutationWord ρ).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  change (ρ i).val + 1 = (ρ j).val + 1 at hij
  apply ρ.injective
  apply Fin.ext
  omega

theorem permutationWord_perm_full {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    (permutationWord ρ).Perm (fullGapList n) := by
  apply (List.perm_ext_iff_of_nodup (permutationWord_nodup ρ) (fullGapList_nodup n)).2
  intro x
  rw [fullGapList_mem]
  constructor
  · exact permutationWord_range ρ x
  · rintro ⟨hx, hxn⟩
    apply List.mem_ofFn.mpr
    refine ⟨ρ.symm ⟨x - 1, by omega⟩, ?_⟩
    simp
    omega

theorem permutationWord_sum {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    (permutationWord ρ).sum = width n := by
  rw [(permutationWord_perm_full ρ).sum_eq, fullGapList_sum]

/-- Encoding the actual word back as a permutation recovers the supplied
permutation, rather than a reordered witness with the same inventory. -/
theorem permutationWord_gapListPerm {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    gapListPerm (permutationWord ρ) (permutationWord_length ρ)
      (permutationWord_range ρ) (permutationWord_nodup ρ) = ρ := by
  ext j
  have hv := gapListPerm_value (permutationWord ρ) (permutationWord_length ρ)
    (permutationWord_range ρ) (permutationWord_nodup ρ) j
  rw [List.getD_eq_getElem _ 0 (by rw [permutationWord_length]; exact j.isLt)] at hv
  simp only [permutationWord, List.getElem_ofFn] at hv
  change (gapListPerm (permutationWord ρ) (permutationWord_length ρ)
    (permutationWord_range ρ) (permutationWord_nodup ρ) j).val + 1 = (ρ j).val + 1 at hv
  omega

theorem permutationWord_partialSum {n : ℕ} (ρ : Equiv.Perm (Fin n)) (j : Fin n) :
    partialSum ρ j = ((permutationWord ρ).take (j.val + 1)).sum := by
  have hp := gapListPerm_partialSum (permutationWord ρ) (permutationWord_length ρ)
    (permutationWord_range ρ) (permutationWord_nodup ρ) j
  rw [permutationWord_gapListPerm ρ] at hp
  exact hp

end CorralFormalization
