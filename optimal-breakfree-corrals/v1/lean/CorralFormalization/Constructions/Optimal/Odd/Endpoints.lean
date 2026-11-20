import CorralFormalization.Constructions.Optimal.Odd.Buckets
import CorralFormalization.Constructions.Optimal.Odd.Assignment

set_option maxHeartbeats 0

namespace CorralFormalization

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. -/

open OddSeamAssignment

/-- On the owners using a tail match, the stated tail deficit fits inside a
local bucket width. -/
theorem oddConstructionTailEndpoint_le_width (A s : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (htail : explicitUsesTail A s) :
    explicitTailEndpoint A s ≤ 4 * A + 3 := by
  unfold explicitTailEndpoint
  unfold explicitUsesTail at htail
  split_ifs <;> omega

/-- The candidate last local remainder occurs in the actual bucket. -/
theorem oddConstructionTailBucket_max_mem (A s : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (htail : explicitUsesTail A s) :
    oddConstructionBucketSpec A (2 * A + 3 - 1 - s)
      ((4 * A + 3) - explicitTailEndpoint A s) := by
  unfold explicitTailEndpoint
  unfold explicitUsesTail at htail
  split_ifs with h0 h1 h2 h3 h4 h5
  · unfold oddConstructionBucketSpec
    right; right; right; right; right; right; right; left
    omega
  · unfold oddConstructionBucketSpec
    right; right; right; right; right; right; right; right; left
    omega
  · unfold oddConstructionBucketSpec
    right; right; right; right; right; right; left
    omega
  · unfold oddConstructionBucketSpec
    right; right; right; right; right; left
    omega
  · unfold oddConstructionBucketSpec
    right; left
    omega
  · unfold oddConstructionBucketSpec
    left
    omega
  · omega

/-- Nothing in that actual bucket exceeds the candidate last remainder. -/
theorem oddConstructionTailBucket_max_upper (A s r : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (htail : explicitUsesTail A s)
    (hmem : oddConstructionBucketSpec A (2 * A + 3 - 1 - s) r) :
    r ≤ (4 * A + 3) - explicitTailEndpoint A s := by
  unfold explicitTailEndpoint
  unfold explicitUsesTail at htail
  unfold oddConstructionBucketSpec at hmem
  split_ifs <;> rcases hmem with h | h | h | h | h | h | h | h | h | h <;> omega

/-- The first block index has the ordinary representative `h-s` on every
owner for which the paper uses a head match. -/
theorem oddConstructionHeadBucket_index (A s : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (hhead : ¬ explicitUsesTail A s) :
    (2 * A + 3 - s) % (2 * A + 3) = 2 * A + 3 - s := by
  apply Nat.mod_eq_of_lt
  unfold explicitUsesTail at hhead
  omega

/-- The candidate first local remainder occurs in the actual bucket. -/
theorem oddConstructionHeadBucket_min_mem (A s : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (hhead : ¬ explicitUsesTail A s) :
    oddConstructionBucketSpec A (2 * A + 3 - s) (explicitHeadEndpoint A s) := by
  unfold explicitHeadEndpoint
  unfold explicitUsesTail at hhead
  split_ifs with h0 h1
  · unfold oddConstructionBucketSpec
    right; right; right; right; right; right; right; left
    omega
  · unfold oddConstructionBucketSpec
    right; right; right; right; left
    omega
  · omega

/-- Nothing in that actual bucket is below the candidate first remainder. -/
theorem oddConstructionHeadBucket_min_lower (A s r : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (hhead : ¬ explicitUsesTail A s)
    (hmem : oddConstructionBucketSpec A (2 * A + 3 - s) r) :
    explicitHeadEndpoint A s ≤ r := by
  unfold explicitHeadEndpoint
  unfold explicitUsesTail at hhead
  unfold oddConstructionBucketSpec at hmem
  split_ifs <;> rcases hmem with h | h | h | h | h | h | h | h | h | h <;> omega

/-- The last source bucket's actual maximum is the one in the paper's
endpoint table, for every owner which uses a tail match. -/
theorem oddConstructionTailBucket_actual_max (A s : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (htail : explicitUsesTail A s) :
    (localBucket (4 * A + 3) (2 * A + 3 - 1 - s) (actualOddQ A)).max'
        (actualOddBucket_nonempty A (2 * A + 3 - 1 - s) hA (by omega)) =
      (4 * A + 3) - explicitTailEndpoint A s := by
  apply le_antisymm
  · apply Finset.max'_le
    intro r hr
    exact oddConstructionTailBucket_max_upper A s r hA hs htail
      ((actualOddBucket_mem_iff_spec A _ r hA).1 hr)
  · apply Finset.le_max'
    exact (actualOddBucket_mem_iff_spec A _ _ hA).2
      (oddConstructionTailBucket_max_mem A s hA hs htail)

theorem oddConstructionHeadBucket_lt (A s : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (hhead : ¬ explicitUsesTail A s) :
    2 * A + 3 - s < 2 * A + 3 := by
  have hindex := oddConstructionHeadBucket_index A s hA hs hhead
  have hmod := Nat.mod_lt (2 * A + 3 - s) (by omega : 0 < 2 * A + 3)
  omega

/-- The first source bucket's actual minimum is the one in the paper's
endpoint table, for every owner which uses a head match. -/
theorem oddConstructionHeadBucket_actual_min (A s : ℕ) (hA : 2 ≤ A)
    (hs : s < 2 * A + 3) (hhead : ¬ explicitUsesTail A s) :
    (localBucket (4 * A + 3) (2 * A + 3 - s) (actualOddQ A)).min'
        (actualOddBucket_nonempty A (2 * A + 3 - s) hA
          (oddConstructionHeadBucket_lt A s hA hs hhead)) = explicitHeadEndpoint A s := by
  apply le_antisymm
  · apply Finset.min'_le
    exact (actualOddBucket_mem_iff_spec A _ _ hA).2
      (oddConstructionHeadBucket_min_mem A s hA hs hhead)
  · apply Finset.le_min'
    intro r hr
    exact oddConstructionHeadBucket_min_lower A s r hA hs hhead
      ((actualOddBucket_mem_iff_spec A _ r hA).1 hr)

/-- The first-factor row using the same physical representation as (6). -/
def oddConstructionCoreSites (A : ℕ) (s : Fin (2 * A + 3)) : Finset ℕ :=
  translatedSites (2 * A + 3) (4 * A + 3) s.val (actualOddQ A)

theorem oddConstructionCoreSites_nonempty (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (2 * A + 3)) : (oddConstructionCoreSites A s).Nonempty := by
  have hf := actualOddBucket_nonempty A ((2 * A + 3 - s.val) % (2 * A + 3)) hA
    (Nat.mod_lt _ (by omega))
  have hl := actualOddBucket_nonempty A (2 * A + 3 - 1 - s.val) hA (by omega)
  obtain ⟨hne, _, _⟩ := actualOddCoreRows_endpoints_of_nonempty_buckets A s hf hl
  exact hne

/-- The actual first point of a paper core row equals the appropriate
head value in the printed endpoint table. -/
theorem oddConstructionCoreSites_head_table (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (2 * A + 3)) (hhead : ¬ explicitUsesTail A s.val) :
    (oddConstructionCoreSites A s).min' (oddConstructionCoreSites_nonempty A hA s) =
      explicitHeadEndpoint A s.val := by
  have hf := actualOddBucket_nonempty A ((2 * A + 3 - s.val) % (2 * A + 3)) hA
    (Nat.mod_lt _ (by omega))
  have hl := actualOddBucket_nonempty A (2 * A + 3 - 1 - s.val) hA (by omega)
  obtain ⟨_, hfirst, _⟩ := actualOddCoreRows_endpoints_of_nonempty_buckets A s hf hl
  have hbucket : (localBucket (4 * A + 3)
      ((2 * A + 3 - s.val) % (2 * A + 3)) (actualOddQ A)).min' hf =
      explicitHeadEndpoint A s.val := by
    simpa only [oddConstructionHeadBucket_index A s.val hA s.isLt hhead] using
      oddConstructionHeadBucket_actual_min A s.val hA s.isLt hhead
  exact hfirst.trans hbucket

/-- The actual last-point deficit of a paper core row equals the appropriate
tail value in the printed endpoint table. -/
theorem oddConstructionCoreSites_tail_table (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (2 * A + 3)) (htail : explicitUsesTail A s.val) :
    (2 * A + 3) * (4 * A + 3) -
      (oddConstructionCoreSites A s).max' (oddConstructionCoreSites_nonempty A hA s) =
        explicitTailEndpoint A s.val := by
  have hf := actualOddBucket_nonempty A ((2 * A + 3 - s.val) % (2 * A + 3)) hA
    (Nat.mod_lt _ (by omega))
  have hl := actualOddBucket_nonempty A (2 * A + 3 - 1 - s.val) hA (by omega)
  obtain ⟨_, _, hlast⟩ := actualOddCoreRows_endpoints_of_nonempty_buckets A s hf hl
  have hmax := oddConstructionTailBucket_actual_max A s.val hA s.isLt htail
  have hwidth := oddConstructionTailEndpoint_le_width A s.val hA s.isLt htail
  rw [hmax] at hlast
  have hlast' : (2 * A + 3) * (4 * A + 3) -
      (oddConstructionCoreSites A s).max' (oddConstructionCoreSites_nonempty A hA s) =
      (4 * A + 3) - ((4 * A + 3) - explicitTailEndpoint A s.val) := by
    simpa only [oddConstructionCoreSites] using hlast
  omega

/-- The actual core row and the actual assigned two-point row satisfy the
paper's head-or-tail match, with the bucket hypotheses fully discharged. -/
theorem oddConstructionConcreteEndpointMatch (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (2 * A + 3)) :
    if explicitUsesTail A s.val then
      (2 * A + 3) * (4 * A + 3) -
        (oddConstructionCoreSites A s).max' (oddConstructionCoreSites_nonempty A hA s) =
          dTail A (explicitOwnerIndex A hA s)
    else
      (oddConstructionCoreSites A s).min' (oddConstructionCoreSites_nonempty A hA s) =
          dHead A (explicitOwnerIndex A hA s) := by
  by_cases ht : explicitUsesTail A s.val
  · simp only [if_pos ht]
    calc
      _ = explicitTailEndpoint A s.val := oddConstructionCoreSites_tail_table A hA s ht
      _ = dTail A (explicitOwnerIndex A hA s) := by
        simpa [ht] using explicitOwnerEndpointMatch A hA s
  · simp only [if_neg ht]
    calc
      _ = explicitHeadEndpoint A s.val := oddConstructionCoreSites_head_table A hA s ht
      _ = dHead A (explicitOwnerIndex A hA s) := by
        simpa [ht] using explicitOwnerEndpointMatch A hA s

end CorralFormalization
