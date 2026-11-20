import CorralFormalization.Results.OrderedPartitionCounting
import CorralFormalization.Results.PrimeHeight.ModelBridges
import CorralFormalization.Results.SharpUpper.RowBranching
import CorralFormalization.Results.SharpUpper.Orbits

/-!
# Sharp upper bound: from actual physical rows to unlabelled families

Every history is a prefix of a real optimal partition. The finite row
branching bound and the `h!` ordered-prefix multiplicity are joined here;
no independence assumption and no abstract replacement of the physical
corral census is used.
-/

open Finset CorralFormalization.PhysicalCorral CorralLatinTailMarker
open CorralFormalization.PhysicalCensus
open CorralFormalization.Results.PrimeHeight
open CorralFormalization.Results.OrderedPartitionCounting
open CorralFormalization.Results.SharpUpper

namespace CorralFormalization.Results.PhysicalPartitionUpper

variable {h n : ℕ} [NeZero (h*n)]

theorem valid_family_card (hn : 2 ≤ n) (hw : width n = h*n)
    (F : PhysicalFamily h n) (hF : F ∈ validOptimalFamilies h n) : F.card = h :=
  ((mem_validOptimalFamilies_iff_local hn hw F).mp hF).1

theorem valid_family_disjoint (hn : 2 ≤ n) (hw : width n = h*n)
    (F : PhysicalFamily h n) (hF : F ∈ validOptimalFamilies h n) :
    ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B :=
  ((mem_validOptimalFamilies_iff_local hn hw F).mp hF).2.1

theorem valid_family_rows (hn : 2 ≤ n) (hw : width n = h*n)
    (F : PhysicalFamily h n) (hF : F ∈ validOptimalFamilies h n) :
    F ⊆ validRows (h*n) n := by
  intro R hR
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, ((mem_validOptimalFamilies_iff_local hn hw F).mp hF).2.2 R hR⟩

theorem valid_family_cover (F : PhysicalFamily h n) (hF : F ∈ validOptimalFamilies h n) :
    F.biUnion id = (Finset.univ : Finset (ZMod (h*n))) := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨R,⟨hR,hx⟩,_⟩ := validOptimalFamilies_partition F hF x
  exact Finset.mem_biUnion.mpr ⟨R,hR,hx⟩

/-- Actual available physical rows after the already selected rows. -/
noncomputable def allowedPhysicalRows (p : List (Finset (ZMod (h*n)))) :
    Finset (Finset (ZMod (h*n))) :=
  disjointValidRows (p.toFinset.biUnion id) n

theorem ordering_next_allowed (hn : 2 ≤ n) (hw : width n = h*n)
    (xs : List (Finset (ZMod (h*n))))
    (hxs : xs ∈ orderingsOfFamilies (validOptimalFamilies h n))
    (j : ℕ) (hj : j < xs.length) : xs[j] ∈ allowedPhysicalRows (xs.take j) := by
  classical
  obtain ⟨F,hF,hxsF⟩ := Finset.mem_biUnion.mp hxs
  have hFrow := valid_family_rows hn hw F hF
  have hFdis := valid_family_disjoint hn hw F hF
  have hrecover := familyOrderings_recover F xs hxsF
  have hnd := familyOrderings_nodup F xs hxsF
  have hxF : xs[j] ∈ F := by rw [← hrecover]; exact List.mem_toFinset.mpr (List.getElem_mem hj)
  have hnot : xs[j] ∉ xs.take j := by
    have hh : (xs.take j ++ [xs[j]]).Nodup := by
      rw [← List.take_succ_eq_append_getElem hj]
      exact hnd.take
    exact ((List.nodup_concat _ _).mp (by simpa only [List.concat_eq_append] using hh)).1
  change xs[j] ∈ disjointValidRows ((xs.take j).toFinset.biUnion id) n
  apply Finset.mem_filter.mpr
  refine ⟨hFrow hxF, ?_⟩
  apply Finset.disjoint_left.mpr
  intro x hx hprior
  obtain ⟨A,hA,hxA⟩ := Finset.mem_biUnion.mp hprior
  have hAF : A ∈ F := by
    rw [← hrecover]
    exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hA))
  have hne : xs[j] ≠ A := by
    intro heq
    apply hnot
    rw [heq]
    exact List.mem_toFinset.mp hA
  exact (Finset.disjoint_left.mp (hFdis xs[j] hxF A hAF hne)) hx hxA

theorem prefix_allowed_card_le (hn : 2 ≤ n) (hw : width n = h*n) (hhn : h ≤ n)
    (j : ℕ) (hj : j < h) (p : List (Finset (ZMod (h*n))))
    (hp : p ∈ familyPrefixes (validOptimalFamilies h n) j) :
    ((allowedPhysicalRows p).card : ℝ) ≤
      ((h-j : ℕ) : ℝ) * (n.factorial : ℝ) * avoidanceFactor n j := by
  classical
  obtain ⟨xs,hxs,hpx⟩ := Finset.mem_image.mp hp
  have hlen : xs.length = h := ordering_length (validOptimalFamilies h n) h
    (valid_family_card hn hw) xs hxs
  obtain ⟨F,hF,hxsF⟩ := Finset.mem_biUnion.mp hxs
  have hrecover := familyOrderings_recover F xs hxsF
  have hnd := familyOrderings_nodup F xs hxsF
  subst p
  let J := (xs.take j).toFinset
  have hJsub : J ⊆ F := by
    intro A hA
    rw [← hrecover]
    exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hA))
  have hJ : J ⊆ validRows (h*n) n := hJsub.trans (valid_family_rows hn hw F hF)
  have hdis : ∀ A ∈ J, ∀ B ∈ J, A ≠ B → Disjoint A B := by
    intro A hA B hB hne
    exact valid_family_disjoint hn hw F hF A (hJsub hA) B (hJsub hB) hne
  have hJcard : J.card = j := by
    rw [show J.card = (xs.take j).length from List.toFinset_card_of_nodup hnd.take,
      List.length_take, hlen, Nat.min_eq_left (by omega : j ≤ h)]
  have hbound := physical_row_branching_bound (h:=h) hn J hJ hdis (by omega : J.card ≤ n)
  rw [hJcard] at hbound
  exact hbound

/-- All actual unlabelled optimal partitions obey the full product of the
one-row branching factors, with the exact `h!` multiplicity on the left. -/
theorem valid_families_count_le_branching_product
    (hh : 1 ≤ h) (hn : 2 ≤ n) (hw : width n = h*n) (hhn : h ≤ n) :
    ((validOptimalFamilies h n).card : ℝ) * (h.factorial : ℝ) ≤
      ∏ j ∈ Finset.range (h-1),
        (((h-j : ℕ) : ℝ) * (n.factorial : ℝ) * avoidanceFactor n j) := by
  classical
  apply partition_count_from_branching (Finset.univ : Finset (ZMod (h*n)))
    (validOptimalFamilies h n) h hh (valid_family_card hn hw) valid_family_cover
    (valid_family_disjoint hn hw) allowedPhysicalRows (ordering_next_allowed hn hw)
  · intro j
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (avoidanceFactor_nonneg n j)
  · exact prefix_allowed_card_le hn hw hhn

theorem branching_product_eq (h n : ℕ) (hh : 2 ≤ h) :
    (∏ j ∈ Finset.range (h-1),
      (((h-j : ℕ) : ℝ) * (n.factorial : ℝ) * avoidanceFactor n j)) =
      (h.factorial : ℝ) * (n.factorial : ℝ)^(h-1) *
        (∏ j ∈ Finset.range (h-2), avoidanceFactor n (j+1)) := by
  have hfact : (∏ j ∈ Finset.range (h-1), ((h-j : ℕ) : ℝ)) = (h.factorial : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range]
    have hn := Nat.factorial_mul_descFactorial (n:=h) (k:=h-1) (by omega)
    have hsub : h - (h-1) = 1 := by omega
    rw [hsub] at hn
    simp only [Nat.factorial_one, one_mul] at hn
    exact_mod_cast hn
  have havoid : (∏ j ∈ Finset.range (h-1), avoidanceFactor n j) =
      ∏ j ∈ Finset.range (h-2), avoidanceFactor n (j+1) := by
    have he : h-1 = (h-2)+1 := by omega
    rw [he, Finset.prod_range_succ']
    simp [avoidanceFactor]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hfact, Finset.prod_const,
    Finset.card_range, havoid]

/-- `P_h`: the number of unlabelled, anchored physical optimal-corral
partitions. This is a direct name for the existing finite physical census. -/
noncomputable def P_h (h : ℕ) (hh : 2 ≤ h) : ℕ := by
  have : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  exact (validOptimalFamilies h (2*h-1)).card

/-- The first sharp inequality in Theorem 8, for every height `h≥2` and
the actual physical census. -/
theorem physical_partition_sharp_upper (h : ℕ) (hh : 2 ≤ h) :
    (P_h h hh : ℝ) ≤
      (((2*h-1).factorial : ℕ) : ℝ)^(h-1) * correctionProduct h := by
  have : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hw : width (2*h-1) = h*(2*h-1) := LatinTransfer.optimal_width (by omega) rfl
  have hb := valid_families_count_le_branching_product (h:=h) (n:=2*h-1)
    (by omega) (by omega) hw (by omega)
  rw [branching_product_eq h (2*h-1) hh] at hb
  change ((validOptimalFamilies h (2*h-1)).card : ℝ) * (h.factorial : ℝ) ≤
    (h.factorial : ℝ) * (((2*h-1).factorial : ℕ) : ℝ)^(h-1) *
      correctionProduct h at hb
  have hpos : 0 < (h.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos h
  change ((validOptimalFamilies h (2*h-1)).card : ℝ) ≤ _
  apply le_of_mul_le_mul_left _ hpos
  nlinarith [hb]

/-- All three inequalities of the paper's global Theorem 8, with the exact
physical partition and asymmetric-orbit censuses and no additional theorem
inputs. The factor `2h(2h-1)` counts the actual dihedral orbit. -/
theorem sharp_global_census_bounds (h : ℕ) (hh : 2 ≤ h) :
    (P_h h hh : ℝ) ≤
        (((2*h-1).factorial : ℕ) : ℝ)^(h-1) * correctionProduct h ∧
    (A_h h hh : ℝ) ≤
        ((((2*h-1).factorial : ℕ) : ℝ)^(h-1) * correctionProduct h) /
          ((2*(h*(2*h-1)) : ℕ) : ℝ) ∧
    correctionProduct h ≤
      Real.exp (-(((h - 2 : ℕ) : ℝ) * ((h - 1 : ℕ) : ℝ) * (h : ℝ) /
        (6 * ((2 * h - 1 : ℕ) : ℝ)))) := by
  have : NeZero (h*(2*h-1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hw : width (2*h-1) = h*(2*h-1) := LatinTransfer.optimal_width (by omega) rfl
  have hp := physical_partition_sharp_upper h hh
  have horbit := asymmetric_orbit_count_le_div (h:=h) (n:=2*h-1) (by omega) hw
  have hden : 0 ≤ ((2*(h*(2*h-1)) : ℕ) : ℝ) := by positivity
  refine ⟨hp, ?_, correctionProduct_le_exp h hh⟩
  change ((allAsymmetricCorralOrbits h (2*h-1)).card : ℝ) ≤ _
  exact horbit.trans (div_le_div_of_nonneg_right hp hden)

end CorralFormalization.Results.PhysicalPartitionUpper
