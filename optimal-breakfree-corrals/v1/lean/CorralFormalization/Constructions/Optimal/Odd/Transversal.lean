import CorralFormalization.Constructions.Optimal.Odd.Word
import CorralFormalization.BucketGeometry

namespace CorralFormalization

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. The gap word
itself is shared by the two constructions. -/

/-- Proper prefixes of the actual printed word, reduced modulo its length. -/
def actualOddPrefixResidue (A : ℕ) (j : Fin (4 * A + 3)) : Fin (4 * A + 3) :=
  ⟨oddConstructionPrefix A j.val % (4 * A + 3), Nat.mod_lt _ (by omega)⟩

/-- The concrete prefix residues are a bijection for every paper parameter. -/
theorem actualOddPrefixResidue_bijective (A : ℕ) (hA : 2 ≤ A) :
    Function.Bijective (actualOddPrefixResidue A) := by
  have heq : actualOddPrefixResidue A = oddCorePrefixResidue A hA := by
    funext j
    apply Fin.ext
    exact oddConstructionPrefixResidueValue_actual_all A hA j
  rw [heq]
  exact oddCorePrefixResidue_bijective A hA

/-- Every proper prefix is strictly before the end of the one-winding word. -/
theorem actualOddPrefix_lt_width (A : ℕ) (hA : 2 ≤ A)
    (j : Fin (4 * A + 3)) :
    oddConstructionPrefix A j.val < (2 * A + 3) * (4 * A + 3) := by
  have hj : j.val < (oddConstructionGapWord A).length := by
    rw [oddConstructionGapWord_length A hA]
    exact j.isLt
  have hne : (oddConstructionGapWord A).drop j.val ≠ [] := by
    intro hnil
    have := (List.drop_eq_nil_iff.mp hnil)
    omega
  have hpos : 0 < ((oddConstructionGapWord A).drop j.val).sum := by
    apply List.sum_pos
    · intro x hx
      exact oddConstructionGapWord_positive A hA (List.mem_of_mem_drop hx)
    · exact hne
  have hsum := congrArg List.sum (List.take_append_drop j.val (oddConstructionGapWord A))
  rw [List.sum_append, oddConstructionGapWord_sum A hA] at hsum
  change ((oddConstructionGapWord A).take j.val).sum < _
  omega

/-- The translated, physical prefix set Q from manuscript §4.3. -/
def actualOddQ (A : ℕ) : Finset ℕ :=
  Finset.univ.image fun j : Fin (4 * A + 3) =>
    (oddConstructionPrefix A j.val + (2 * A - 3)) % ((2 * A + 3) * (4 * A + 3))

/-- Equation (6), using the actual word's proper prefixes as its points. -/
def actualOddLiteralRow (A s : ℕ) : Finset ℕ :=
  Finset.univ.image fun j : Fin (4 * A + 3) =>
    (oddConstructionPrefix A j.val + (2 * A - 3) + (4 * A + 3) * s) %
      ((2 * A + 3) * (4 * A + 3))

theorem actualOddLiteralRow_eq_translatedSites (A s : ℕ) :
    actualOddLiteralRow A s =
      translatedSites (2 * A + 3) (4 * A + 3) s (actualOddQ A) := by
  simp [actualOddLiteralRow, translatedSites, actualOddQ, Finset.image_image,
    Function.comp_def, Nat.mod_add_mod]

def actualOddShiftedResidue (A : ℕ) (j : Fin (4 * A + 3)) : Fin (4 * A + 3) :=
  ⟨((oddConstructionPrefix A j.val + (2 * A - 3)) %
    ((2 * A + 3) * (4 * A + 3))) % (4 * A + 3), Nat.mod_lt _ (by omega)⟩

/-- Translation and reduction on the physical clock give the table's actual
shifted remainder, not merely an independently encoded residue list. -/
theorem actualOddShiftedResidue_eq_table (A : ℕ) (hA : 2 ≤ A)
    (j : Fin (4 * A + 3)) :
    actualOddShiftedResidue A j = oddCoreTranslatedPrefixResidue A hA j := by
  apply Fin.ext
  change ((oddConstructionPrefix A j.val + (2 * A - 3)) %
    ((2 * A + 3) * (4 * A + 3))) % (4 * A + 3) = _
  rw [Nat.mod_mul_left_mod]
  simp only [oddCoreTranslatedPrefixResidue, Fin.val_add, oddCorePrefixResidue]
  rw [← oddConstructionPrefixResidueValue_actual_all A hA j]
  simp [Nat.add_mod]

theorem actualOddShiftedResidue_bijective (A : ℕ) (hA : 2 ≤ A) :
    Function.Bijective (actualOddShiftedResidue A) := by
  have heq : actualOddShiftedResidue A = oddCoreTranslatedPrefixResidue A hA := by
    funext j
    exact actualOddShiftedResidue_eq_table A hA j
  rw [heq]
  exact oddCoreTranslatedPrefixResidue_bijective A hA

/-- The literal translated prefix set Q meets every remainder class once. -/
theorem actualOddQ_transversal (A : ℕ) (hA : 2 ≤ A) :
    ∀ r, r < 4 * A + 3 → ∃! q, q ∈ actualOddQ A ∧ q % (4 * A + 3) = r := by
  intro r hr
  obtain ⟨j, hj⟩ := (actualOddShiftedResidue_bijective A hA).surjective ⟨r, hr⟩
  let q := (oddConstructionPrefix A j.val + (2 * A - 3)) % ((2 * A + 3) * (4 * A + 3))
  have hq : q ∈ actualOddQ A := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hqr : q % (4 * A + 3) = r := congrArg Fin.val hj
  refine ⟨q, ⟨hq, hqr⟩, ?_⟩
  intro p ⟨hp, hpr⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
  have heq : actualOddShiftedResidue A i = actualOddShiftedResidue A j := by
    apply Fin.ext
    change ((oddConstructionPrefix A i.val + (2 * A - 3)) %
      ((2 * A + 3) * (4 * A + 3))) % (4 * A + 3) = q % (4 * A + 3)
    rw [hi, hpr, hqr]
  have hij := (actualOddShiftedResidue_bijective A hA).injective heq
  subst i
  exact hi.symm

theorem actualOddQ_lt_width (A q : ℕ) (hq : q ∈ actualOddQ A) :
    q < (2 * A + 3) * (4 * A + 3) := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
  exact Nat.mod_lt _ (by positivity)

/-- The paper's actual Q has the equation (9) endpoints provided the two
relevant concrete buckets are nonempty. Proving the printed populations and
therefore discharging these hypotheses remains a separate obligation. -/
theorem actualOddCoreRows_endpoints_of_nonempty_buckets
    (A : ℕ) (s : Fin (2 * A + 3))
    (hfirst : (localBucket (4 * A + 3)
      (((2 * A + 3) - s.val) % (2 * A + 3)) (actualOddQ A)).Nonempty)
    (hlast : (localBucket (4 * A + 3)
      ((2 * A + 3) - 1 - s.val) (actualOddQ A)).Nonempty) :
    ∃ hsites : (translatedSites (2 * A + 3) (4 * A + 3) s.val (actualOddQ A)).Nonempty,
      (translatedSites (2 * A + 3) (4 * A + 3) s.val (actualOddQ A)).min' hsites =
        (localBucket (4 * A + 3)
          (((2 * A + 3) - s.val) % (2 * A + 3)) (actualOddQ A)).min' hfirst ∧
      (2 * A + 3) * (4 * A + 3) -
          (translatedSites (2 * A + 3) (4 * A + 3) s.val (actualOddQ A)).max' hsites =
        (4 * A + 3) - (localBucket (4 * A + 3)
          ((2 * A + 3) - 1 - s.val) (actualOddQ A)).max' hlast := by
  exact explicit_bucket_endpoint_geometry _ _ _ _ (by omega) (by omega) s.isLt
    (actualOddQ_lt_width A) hfirst hlast

/-- These are the paper's actual first-factor rows, and every site has
exactly one owner. This does not establish their bucket endpoints. -/
theorem actualOddCoreRows_partition (A : ℕ) (hA : 2 ≤ A)
    (x : ℕ) (hx : x < (2 * A + 3) * (4 * A + 3)) :
    ∃! s : Fin (2 * A + 3),
      x ∈ translatedSites (2 * A + 3) (4 * A + 3) s.val (actualOddQ A) := by
  apply transversal_block_translates_partition _ _ _ (by omega) (by omega)
  · exact actualOddQ_lt_width A
  · exact actualOddQ_transversal A hA
  · exact hx

/-- The point sets exactly as printed in (6) partition their physical clock. -/
theorem actualOddLiteralRows_partition (A : ℕ) (hA : 2 ≤ A)
    (x : ℕ) (hx : x < (2 * A + 3) * (4 * A + 3)) :
    ∃! s : Fin (2 * A + 3), x ∈ actualOddLiteralRow A s.val := by
  simpa only [actualOddLiteralRow_eq_translatedSites] using
    actualOddCoreRows_partition A hA x hx

end CorralFormalization
