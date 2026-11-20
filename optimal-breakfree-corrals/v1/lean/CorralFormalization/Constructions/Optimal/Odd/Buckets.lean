import CorralFormalization.Constructions.Optimal.Odd.Quotients

set_option maxHeartbeats 0

namespace CorralFormalization

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. -/

/-- Quantifier-free regrouping of the quotient/remainder pairs in (10).
Each disjunct corresponds to one printed prefix family or exceptional point. -/
def oddConstructionBucketSpec (A b r : ℕ) : Prop :=
  (b = 0 ∧ r = 2 * A - 3) ∨
  (b = 1 ∧ r = 2 * A - 1) ∨
  (b = 0 ∧ r = 2 * A - 4) ∨
  (2 ≤ b ∧ b ≤ A + 2 ∧ r = 2 * A + 2 * b - 6) ∨
  (3 ≤ b ∧ b ≤ A ∧ r = 2 * A + 1 - 2 * b) ∨
  (b = A ∧ r = 4 * A + 2) ∨
  (b = A + 1 ∧ r = 4 * A) ∨
  (A + 3 ≤ b ∧ b ≤ 2 * A + 2 ∧ r = 6 * A + 5 - 2 * b) ∨
  (b = A + 3 ∧ r = 4 * A + 1) ∨
  (A + 5 ≤ b ∧ b ≤ 2 * A + 2 ∧ r = 2 * b - 2 * A - 10)

/-- Quotient and remainder of a canonical block representation. -/
theorem oddConstructionBlock_coordinates (K b r : ℕ) (hK : 0 < K) (hr : r < K) :
    (b * K + r) / K = b ∧ (b * K + r) % K = r := by
  apply (Nat.div_mod_unique hK).2
  constructor
  · ring
  · exact hr

/-- Every actual shifted proper prefix has one of the pairs described by
the paper's regrouped table, with a valid quotient and local remainder. -/
theorem oddConstructionShiftedPoint_has_bucket_spec (A : ℕ) (hA : 2 ≤ A)
    (j : Fin (4 * A + 3)) :
    ∃ b r, b < 2 * A + 3 ∧ r < 4 * A + 3 ∧
      oddConstructionShiftedPoint A j.val = b * (4 * A + 3) + r ∧
      oddConstructionBucketSpec A b r := by
  rcases j with ⟨j, hj⟩
  simp only
  by_cases hj0 : j = 0
  · subst j
    refine ⟨0, 2 * A - 3, by omega, by omega, ?_, ?_⟩
    · simpa using oddConstructionShifted_zero A hA
    · unfold oddConstructionBucketSpec
      omega
  · by_cases hj1 : j = 1
    · subst j
      refine ⟨1, 2 * A - 1, by omega, by omega, ?_, ?_⟩
      · exact oddConstructionShifted_one A hA
      · unfold oddConstructionBucketSpec
        omega
    · by_cases hjfirst : j ≤ 2 * A + 2
      · by_cases heven : j % 2 = 0
        · let t := (j - 2) / 2
          have hjform : j = 2 + 2 * t := by dsimp [t]; omega
          have ht : t ≤ A := by dsimp [t]; omega
          refine ⟨t + 2, 2 * A + 2 * t - 2, by omega, by omega, ?_, ?_⟩
          · rw [hjform]
            exact oddConstructionShifted_L A t hA ht
          · unfold oddConstructionBucketSpec
            omega
        · let t := (j - 3) / 2
          have hjform : j = 3 + 2 * t := by dsimp [t]; omega
          have ht : t < A := by dsimp [t]; omega
          by_cases hearly : t + 3 ≤ A
          · refine ⟨t + 3, 2 * A - 2 * t - 5, by omega, by omega, ?_, ?_⟩
            · rw [hjform]
              exact oddConstructionShifted_H_early A t hA hearly
            · unfold oddConstructionBucketSpec
              omega
          · refine ⟨t + 2, 4 * A + 3 + 2 * A - 2 * t - 5,
              by omega, by omega, ?_, ?_⟩
            · rw [hjform]
              exact oddConstructionShifted_H_late A t hA ht (by omega)
            · unfold oddConstructionBucketSpec
              omega
      · by_cases hjsecond : j ≤ 4 * A + 1
        · by_cases heven : (j - (2 * A + 3)) % 2 = 0
          · let t := (j - (2 * A + 3)) / 2
            have hjform : j = 2 * A + 3 + 2 * t := by dsimp [t]; omega
            have ht : t < A := by dsimp [t]; omega
            refine ⟨A + 3 + t, 4 * A + 3 - 4 - 2 * t,
                by omega, by omega, ?_, ?_⟩
            · rw [hjform]
              exact oddConstructionShifted_E A t hA ht
            · unfold oddConstructionBucketSpec
              omega
          · let t := (j - (2 * A + 4)) / 2
            have hjform : j = 2 * A + 4 + 2 * t := by dsimp [t]; omega
            have ht : t < A - 1 := by dsimp [t]; omega
            by_cases ht0 : t = 0
            · have hjform0 : j = 2 * A + 4 := by omega
              refine ⟨A + 3, 4 * A + 3 - 2, by omega, by omega, ?_, ?_⟩
              · rw [hjform0]
                simpa using oddConstructionShifted_F_zero A hA
              · unfold oddConstructionBucketSpec
                omega
            · refine ⟨A + 4 + t, 2 * t - 2, by omega, by omega, ?_, ?_⟩
              · rw [hjform]
                exact oddConstructionShifted_F_pos A t hA ht (by omega)
              · unfold oddConstructionBucketSpec
                omega
        · have hjlast : j = 4 * A + 2 := by omega
          subst j
          refine ⟨0, 2 * A - 4, by omega, by omega, ?_, ?_⟩
          · simpa using oddConstructionShifted_final A hA
          · unfold oddConstructionBucketSpec
            omega

/-- Every pair in the regrouped table is realized by an actual proper
prefix of the printed word. -/
theorem oddConstructionBucketSpec_realized (A b r : ℕ) (hA : 2 ≤ A)
    (hspec : oddConstructionBucketSpec A b r) :
    ∃ j : Fin (4 * A + 3),
      oddConstructionShiftedPoint A j.val = b * (4 * A + 3) + r := by
  unfold oddConstructionBucketSpec at hspec
  rcases hspec with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨hb, hr⟩ := h
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only
    rw [hb, hr]
    simpa using oddConstructionShifted_zero A hA
  · obtain ⟨hb, hr⟩ := h
    refine ⟨⟨1, by omega⟩, ?_⟩
    simp only
    rw [hb, hr]
    exact oddConstructionShifted_one A hA
  · obtain ⟨hb, hr⟩ := h
    refine ⟨⟨4 * A + 2, by omega⟩, ?_⟩
    simp only
    rw [hb, hr]
    simpa using oddConstructionShifted_final A hA
  · obtain ⟨hb0, hb1, hr⟩ := h
    let t := b - 2
    have ht : t ≤ A := by dsimp [t]; omega
    have htb : t + 2 = b := by dsimp [t]; omega
    have htr : 2 * A + 2 * t - 2 = r := by dsimp [t]; omega
    refine ⟨⟨2 + 2 * t, by omega⟩, ?_⟩
    simp only
    simpa [htb, htr] using oddConstructionShifted_L A t hA ht
  · obtain ⟨hb0, hb1, hr⟩ := h
    let t := b - 3
    have ht : t + 3 ≤ A := by dsimp [t]; omega
    have htb : t + 3 = b := by dsimp [t]; omega
    have htr : 2 * A - 2 * t - 5 = r := by dsimp [t]; omega
    refine ⟨⟨3 + 2 * t, by omega⟩, ?_⟩
    simp only
    simpa [htb, htr] using oddConstructionShifted_H_early A t hA ht
  · obtain ⟨hb, hr⟩ := h
    let t := A - 2
    have ht : t < A := by dsimp [t]; omega
    have hlate : A ≤ t + 2 := by dsimp [t]; omega
    have htb : t + 2 = b := by dsimp [t]; omega
    have htr : 4 * A + 3 + 2 * A - 2 * t - 5 = r := by dsimp [t]; omega
    refine ⟨⟨3 + 2 * t, by omega⟩, ?_⟩
    simp only
    simpa [htb, htr] using oddConstructionShifted_H_late A t hA ht hlate
  · obtain ⟨hb, hr⟩ := h
    let t := A - 1
    have ht : t < A := by dsimp [t]; omega
    have hlate : A ≤ t + 2 := by dsimp [t]; omega
    have htb : t + 2 = b := by dsimp [t]; omega
    have htr : 4 * A + 3 + 2 * A - 2 * t - 5 = r := by dsimp [t]; omega
    refine ⟨⟨3 + 2 * t, by omega⟩, ?_⟩
    simp only
    simpa [htb, htr] using oddConstructionShifted_H_late A t hA ht hlate
  · obtain ⟨hb0, hb1, hr⟩ := h
    let t := b - (A + 3)
    have ht : t < A := by dsimp [t]; omega
    have htb : A + 3 + t = b := by dsimp [t]; omega
    have htr : 4 * A + 3 - 4 - 2 * t = r := by dsimp [t]; omega
    refine ⟨⟨2 * A + 3 + 2 * t, by omega⟩, ?_⟩
    simp only
    have hp := oddConstructionShifted_E A t hA ht
    rw [htb, htr] at hp
    exact hp
  · obtain ⟨hb, hr⟩ := h
    refine ⟨⟨2 * A + 4, by omega⟩, ?_⟩
    simp only
    rw [hb, hr]
    simpa using oddConstructionShifted_F_zero A hA
  · obtain ⟨hb0, hb1, hr⟩ := h
    let t := b - (A + 4)
    have ht : t < A - 1 := by dsimp [t]; omega
    have htpos : 1 ≤ t := by dsimp [t]; omega
    have htb : A + 4 + t = b := by dsimp [t]; omega
    have htr : 2 * t - 2 = r := by dsimp [t]; omega
    refine ⟨⟨2 * A + 4 + 2 * t, by omega⟩, ?_⟩
    simp only
    simpa [htb, htr] using oddConstructionShifted_F_pos A t hA ht htpos

theorem oddConstructionBucketSpec_remainder_lt (A b r : ℕ) (hA : 2 ≤ A)
    (hspec : oddConstructionBucketSpec A b r) : r < 4 * A + 3 := by
  unfold oddConstructionBucketSpec at hspec
  rcases hspec with h | h | h | h | h | h | h | h | h | h <;> omega

/-- Exact membership in the paper's actual local bucket, expressed by the
quantifier-free regrouping of its actual shifted prefix pairs. -/
theorem actualOddBucket_mem_iff_spec (A b r : ℕ) (hA : 2 ≤ A) :
    r ∈ localBucket (4 * A + 3) b (actualOddQ A) ↔ oddConstructionBucketSpec A b r := by
  constructor
  · intro hmem
    obtain ⟨hr, hq⟩ := Finset.mem_filter.mp hmem
    have hrlt : r < 4 * A + 3 := Finset.mem_range.mp hr
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hq
    have hjpoint : oddConstructionShiftedPoint A j.val = b * (4 * A + 3) + r := hj
    obtain ⟨b', r', _, hr'lt, hpoint, hspec⟩ :=
      oddConstructionShiftedPoint_has_bucket_spec A hA j
    have heq : b * (4 * A + 3) + r = b' * (4 * A + 3) + r' :=
      hjpoint.symm.trans hpoint
    have hcoords := oddConstructionBlock_coordinates (4 * A + 3) b r (by omega) hrlt
    have hcoords' := oddConstructionBlock_coordinates (4 * A + 3) b' r' (by omega) hr'lt
    have hb : b = b' := by
      have hdiv := congrArg (fun x : ℕ => x / (4 * A + 3)) heq
      simpa [hcoords.1, hcoords'.1] using hdiv
    have hr : r = r' := by
      have hmod := congrArg (fun x : ℕ => x % (4 * A + 3)) heq
      simpa [hcoords.2, hcoords'.2] using hmod
    simpa [hb, hr] using hspec
  · intro hspec
    have hrlt := oddConstructionBucketSpec_remainder_lt A b r hA hspec
    obtain ⟨j, hj⟩ := oddConstructionBucketSpec_realized A b r hA hspec
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hrlt, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, hj⟩

/-- The bucket lists printed in §4.3, including the separate `A=2` list. -/
def oddConstructionPrintedBucket (A b : ℕ) : Finset ℕ :=
  if A = 2 then
    if b = 0 then {0, 1}
    else if b = 1 then {3}
    else if b = 2 then {2, 10}
    else if b = 3 then {4, 8}
    else if b = 4 then {6}
    else if b = 5 then {7, 9}
    else {5}
  else if b = 0 then {2 * A - 4, 2 * A - 3}
  else if b = 1 then {2 * A - 1}
  else if b = 2 then {2 * A - 2}
  else if b < A then {2 * A + 1 - 2 * b, 2 * A + 2 * b - 6}
  else if b = A then {1, 4 * A + 3 - 9, 4 * A + 3 - 1}
  else if b = A + 1 then {4 * A + 3 - 7, 4 * A + 3 - 3}
  else if b = A + 2 then {4 * A + 3 - 5}
  else if b = A + 3 then {4 * A + 3 - 4, 4 * A + 3 - 2}
  else if b = A + 4 then {4 * A + 3 - 6}
  else {2 * b - 2 * A - 10, 6 * A + 5 - 2 * b}

/-- The quantifier-free pair description is exactly the printed table. -/
theorem oddConstructionPrintedBucket_mem_iff_spec (A b r : ℕ)
    (hA : 2 ≤ A) (hb : b < 2 * A + 3) :
    r ∈ oddConstructionPrintedBucket A b ↔ oddConstructionBucketSpec A b r := by
  unfold oddConstructionPrintedBucket oddConstructionBucketSpec
  split_ifs <;> simp_all <;> omega

/-- The buckets calculated from the actual word prefixes are exactly the
lists printed in §4.3 for every `A≥2`, including the `A=2` case. -/
theorem actualOddBucket_eq_printed (A b : ℕ)
    (hA : 2 ≤ A) (hb : b < 2 * A + 3) :
    localBucket (4 * A + 3) b (actualOddQ A) = oddConstructionPrintedBucket A b := by
  ext r
  exact (actualOddBucket_mem_iff_spec A b r hA).trans
    (oddConstructionPrintedBucket_mem_iff_spec A b r hA hb).symm

/-- Every printed table entry is a nonempty finite set. -/
theorem oddConstructionPrintedBucket_nonempty (A b : ℕ) :
    (oddConstructionPrintedBucket A b).Nonempty := by
  unfold oddConstructionPrintedBucket
  split_ifs <;> simp

/-- In particular, every bucket of the actual shifted word is nonempty. -/
theorem actualOddBucket_nonempty (A b : ℕ) (hA : 2 ≤ A)
    (hb : b < 2 * A + 3) :
    (localBucket (4 * A + 3) b (actualOddQ A)).Nonempty := by
  rw [actualOddBucket_eq_printed A b hA hb]
  exact oddConstructionPrintedBucket_nonempty A b

end CorralFormalization
