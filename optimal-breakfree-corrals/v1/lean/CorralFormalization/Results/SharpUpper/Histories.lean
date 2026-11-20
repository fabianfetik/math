import Mathlib.Data.List.Permutation
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Surviving gap histories and their concrete falling-factorial count

The alphabet is literally `Fin n`, with letter `a` representing gap `a+1`.
Starting sites are uniform on `ZMod M`, and complete words are all permutations
of that alphabet. The only geometric input is the displayed density condition
on the `n` possible next sites. No conditional independence is assumed.
-/

namespace CorralFormalization.Results.SharpUpper

open Finset

/-- A starting site and an exposed sequence of distinct gap labels. -/
abbrev GapHistory (M n : ℕ) := ZMod M × List (Fin n)

/-- The location reached after exposing a word of gap labels. -/
def historySite {M n : ℕ} (x : ZMod M) (w : List (Fin n)) : ZMod M :=
  x + ((w.map (fun a => a.val + 1)).sum : ℕ)

/-- Exact unused labels allowed at the next step. The geometry is imposed
only for the first `j` exposures. -/
noncomputable def nextLabels {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) (j t : ℕ) (p : GapHistory M n) : Finset (Fin n) := by
  classical
  exact univ.filter (fun a => a ∉ p.2 ∧
    (t < j → historySite p.1 (p.2 ++ [a]) ∉ F))

/-- All surviving exact histories, with no independence convention. -/
noncomputable def survivingHistories {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) (j : ℕ) : ℕ → Finset (GapHistory M n)
  | 0 => (univ \ F).image (fun x => (x, []))
  | t + 1 => (survivingHistories F j t).biUnion (fun p =>
      (nextLabels F j t p).image (fun a => (p.1, p.2 ++ [a])))

/-- The full local density property used by the paper's G1 argument. -/
def DenseNextSites {M n : ℕ} [NeZero M] (F : Finset (ZMod M)) (j : ℕ) : Prop :=
  ∀ x : ZMod M, j ≤ (univ.filter (fun a : Fin n => x + (a.val + 1 : ℕ) ∈ F)).card

lemma historySite_append {M n : ℕ} (x : ZMod M) (w : List (Fin n)) (a : Fin n) :
    historySite x (w ++ [a]) = historySite x w + (a.val + 1 : ℕ) := by
  simp [historySite, List.map_append, List.sum_append, Nat.cast_add, add_assoc]

lemma survivingHistories_shape {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) (j t : ℕ) (p : GapHistory M n)
    (hp : p ∈ survivingHistories F j t) : p.2.length = t ∧ p.2.Nodup := by
  classical
  induction t generalizing p with
  | zero =>
    obtain ⟨x, _, rfl⟩ := mem_image.mp hp
    simp
  | succ t ih =>
    obtain ⟨q, hq, hp⟩ := mem_biUnion.mp hp
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
    obtain ⟨hlen, hnodup⟩ := ih q hq
    have hnot : a ∉ q.2 := (mem_filter.mp ha).2.1
    refine ⟨by simp [hlen], ?_⟩
    simpa only [List.concat_eq_append] using (List.Nodup.concat hnot hnodup)

lemma nextLabels_card_le_dense {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) {j t : ℕ} (hd : DenseNextSites (n := n) F j)
    (ht : t < j) (p : GapHistory M n) : (nextLabels F j t p).card ≤ n - j := by
  classical
  let bad : Finset (Fin n) := univ.filter (fun a =>
    historySite p.1 p.2 + (a.val + 1 : ℕ) ∈ F)
  have hbad : j ≤ bad.card := hd (historySite p.1 p.2)
  have hsub : nextLabels F j t p ⊆ univ \ bad := by
    intro a ha
    obtain ⟨_, hnot, havoid⟩ := mem_filter.mp ha
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    intro hb
    exact havoid ht (by simpa [bad, historySite_append] using (mem_filter.mp hb).2)
  have hbadn : bad.card ≤ n := by
    simpa using (card_le_univ bad)
  calc
    (nextLabels F j t p).card ≤ (univ \ bad).card := card_le_card hsub
    _ = n - bad.card := by rw [card_sdiff_of_subset (subset_univ _)]; simp
    _ ≤ n - j := Nat.sub_le_sub_left hbad n

lemma nextLabels_card_le_unused {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) (j t : ℕ) (p : GapHistory M n)
    (hshape : p.2.length = t ∧ p.2.Nodup) :
    (nextLabels F j t p).card ≤ n - t := by
  classical
  have hsub : nextLabels F j t p ⊆ univ \ p.2.toFinset := by
    intro a ha
    exact mem_sdiff.mpr ⟨mem_univ _, by simpa using (mem_filter.mp ha).2.1⟩
  calc
    (nextLabels F j t p).card ≤ (univ \ p.2.toFinset).card := card_le_card hsub
    _ = n - t := by
      rw [card_sdiff_of_subset (subset_univ _)]
      simp [List.toFinset_card_of_nodup hshape.2, hshape.1]

lemma survivingHistories_step_card {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) (j t b : ℕ)
    (hb : ∀ p ∈ survivingHistories (n := n) F j t,
      (nextLabels F j t p).card ≤ b) :
    (survivingHistories (n := n) F j (t+1)).card ≤
      (survivingHistories (n := n) F j t).card * b := by
  classical
  calc
    _ ≤ ∑ p ∈ survivingHistories F j t,
        ((nextLabels F j t p).image (fun a => (p.1, p.2 ++ [a]))).card := card_biUnion_le
    _ ≤ ∑ p ∈ survivingHistories F j t, b := by
      apply sum_le_sum
      intro p hp
      exact card_image_le.trans (hb p hp)
    _ = _ := by simp

lemma survivingHistories_initial_card {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) (j : ℕ) :
    (survivingHistories (n := n) F j 0).card = M - F.card := by
  classical
  rw [survivingHistories, card_image_of_injective _ (by
    intro x y hxy
    exact congrArg Prod.fst hxy)]
  rw [card_sdiff_of_subset (subset_univ _)]
  simp [ZMod.card]

/-- The first `t≤j` exposures each have at most `n-j` possible surviving
new labels. This is the concrete history count behind G1. -/
theorem survivingHistories_prefix_card {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) {j : ℕ} (hd : DenseNextSites (n := n) F j)
    (t : ℕ) (ht : t ≤ j) :
    (survivingHistories (n := n) F j t).card ≤ (M-F.card) * (n-j)^t := by
  induction t with
  | zero => simp [survivingHistories_initial_card]
  | succ t ih =>
    calc
      _ ≤ (survivingHistories (n := n) F j t).card * (n-j) :=
        survivingHistories_step_card F j t (n-j) (fun p _ =>
          nextLabels_card_le_dense F hd (by omega) p)
      _ ≤ ((M-F.card) * (n-j)^t) * (n-j) := Nat.mul_le_mul_right _ (ih (by omega))
      _ = _ := by rw [pow_succ, Nat.mul_assoc]

/-- After the first `j` exposures, the unused labels give the exact
falling-factorial continuation bound. -/
theorem survivingHistories_continuation_card {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) {j : ℕ} (_hjn : j ≤ n) (k : ℕ) :
    (survivingHistories (n := n) F j (j+k)).card ≤
      (survivingHistories (n := n) F j j).card * (n-j).descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ ≤ (survivingHistories (n := n) F j (j+k)).card * (n-(j+k)) := by
        simpa [Nat.add_assoc] using survivingHistories_step_card F j (j+k) (n-(j+k))
          (fun p hp => nextLabels_card_le_unused F j (j+k) p
            (survivingHistories_shape F j (j+k) p hp))
      _ ≤ ((survivingHistories (n := n) F j j).card * (n-j).descFactorial k) *
          (n-(j+k)) := Nat.mul_le_mul_right _ ih
      _ = _ := by
        rw [Nat.descFactorial_succ, show n-(j+k) = n-j-k by omega]
        ring

/-- The complete relaxed permutation count has exactly the numerator and
the factorial continuation used in the sharp correction factor. -/
theorem survivingHistories_full_card {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) {j : ℕ} (hjn : j ≤ n)
    (hd : DenseNextSites (n := n) F j) :
    (survivingHistories (n := n) F j n).card ≤
      (M-F.card) * (n-j)^j * (n-j).factorial := by
  have hc := survivingHistories_continuation_card F hjn (n-j)
  rw [Nat.add_sub_of_le hjn, Nat.descFactorial_self] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (survivingHistories_prefix_card F hd j le_rfl))

/-- All gap permutations, with no quotient by cyclic starting positions. -/
noncomputable def gapPermutations (n : ℕ) : Finset (List (Fin n)) :=
  (List.finRange n).permutations.toFinset

theorem gapPermutations_card (n : ℕ) : (gapPermutations n).card = n.factorial := by
  rw [gapPermutations, List.toFinset_card_of_nodup
    (List.nodup_permutations _ (List.nodup_finRange n)), List.length_permutations]
  simp

/-- The uniform starting-site / uniform gap-permutation sample space. -/
noncomputable def gapSampleSpace (M n : ℕ) [NeZero M] : Finset (GapHistory M n) :=
  univ.product (gapPermutations n)

theorem gapSampleSpace_card (M n : ℕ) [NeZero M] :
    (gapSampleSpace M n).card = M * n.factorial := by
  simp [gapSampleSpace, gapPermutations_card, ZMod.card]

/-- Samples whose starting site and every exposed arrival avoid `F`.
At the triangular clock the final arrival is the starting site again. -/
noncomputable def avoidingSamples {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) : Finset (GapHistory M n) := by
  classical
  exact (gapSampleSpace M n).filter (fun p =>
    ∀ t ≤ n, historySite p.1 (p.2.take t) ∉ F)

lemma take_mem_survivingHistories {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) {j : ℕ} (x : ZMod M) (w : List (Fin n))
    (hnd : w.Nodup) (havoid : ∀ t ≤ w.length, historySite x (w.take t) ∉ F)
    (t : ℕ) (ht : t ≤ w.length) :
    (x, w.take t) ∈ survivingHistories F j t := by
  classical
  induction t with
  | zero =>
    apply mem_image.mpr
    refine ⟨x, mem_sdiff.mpr ⟨mem_univ _, ?_⟩, by simp⟩
    simpa [historySite] using havoid 0 (by omega)
  | succ t ih =>
    have htl : t < w.length := by omega
    have htnd : (w.take t ++ [w[t]]).Nodup := by
      rw [← List.take_succ_eq_append_getElem htl]
      exact hnd.take
    have hnot : w[t] ∉ w.take t := by
      exact ((List.nodup_concat (w.take t) w[t]).mp
        (by simpa only [List.concat_eq_append] using htnd)).1
    apply mem_biUnion.mpr
    refine ⟨(x,w.take t), ih (by omega), ?_⟩
    apply mem_image.mpr
    refine ⟨w[t], mem_filter.mpr ⟨mem_univ _, hnot, ?_⟩, ?_⟩
    · intro _
      simpa only [← List.take_succ_eq_append_getElem htl] using havoid (t+1) ht
    · simp only [List.take_succ_eq_append_getElem htl]

/-- Every completely avoiding genuine gap permutation is one of the
relaxed histories counted above. -/
lemma avoidingSamples_subset_surviving {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) (j : ℕ) :
    avoidingSamples (n := n) F ⊆ survivingHistories F j n := by
  classical
  intro p hp
  obtain ⟨hpS,havoid⟩ := mem_filter.mp hp
  obtain ⟨_,hpw⟩ := mem_product.mp hpS
  have hperm : p.2.Perm (List.finRange n) :=
    List.mem_permutations.mp (List.mem_toFinset.mp hpw)
  have hlen : p.2.length = n := by simpa using hperm.length_eq
  have hnd : p.2.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange n)
  have hh := take_mem_survivingHistories (j := j) F p.1 p.2 hnd
    (fun t ht => havoid t (by omega)) n (by omega)
  simpa [List.take_of_length_le (by omega : p.2.length ≤ n)] using hh

/-- A concrete, finite-count version of G1 on the exact uniform
starting-site / gap-permutation sample space. -/
theorem avoidingSamples_card_le {M n : ℕ} [NeZero M]
    (F : Finset (ZMod M)) {j : ℕ} (hjn : j ≤ n)
    (hd : DenseNextSites (n := n) F j) :
    (avoidingSamples (n := n) F).card ≤
      (M-F.card) * (n-j)^j * (n-j).factorial :=
  (card_le_card (avoidingSamples_subset_surviving F j)).trans
    (survivingHistories_full_card F hjn hd)

end CorralFormalization.Results.SharpUpper
