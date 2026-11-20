import CorralFormalization.Results.PrimeHeight.PrimeSubgroup

/-!
# Every optimal corral of odd prime height is asymmetric

The main theorem quantifies over every unlabelled physical family with the
paper's actual local gap inventory and disjointness. It has no construction,
marker, prescribed cyclic enumeration, or assumed freeness as a parameter.
-/

namespace CorralFormalization.Results.PrimeHeight

open PhysicalCorral DiversitySymmetry

variable {M : ℕ} [NeZero M]

/-- Every actual row having the full inventory `[n]` meets its translate
by the maximal gap `n`. The enumerated consecutive pair is obtained from the
sorted physical sites by the existing, proved representation bridge. -/
theorem row_meets_gap_translate {n : ℕ} (R : Finset (ZMod M)) (hn : 2 ≤ n)
    (hgap : finiteCyclicGapInventory M (R.image ZMod.val) =
      Multiset.ofList (fullGapList n)) :
    ¬ Disjoint R ((Motion.rotation (n : ZMod M)).onRow R) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨E, _, hvalues⟩ := cyclicRow_of_finiteCyclicGapInventory R hn hgap
  obtain ⟨i, hi⟩ := (hvalues n).mp ((fullGapList_mem n n).mpr ⟨by omega, le_rfl⟩)
  have hd : (n : ZMod M) = E.site (i + 1) - E.site i := by
    exact (congrArg (fun a : ℕ => (a : ZMod M)) hi).symm.trans
      (ZMod.natCast_zmod_val _)
  have he : (Motion.rotation (n : ZMod M)).act (E.site i) = E.site (i + 1) := by
    change (n : ZMod M) + E.site i = _
    rw [hd, sub_add_cancel]
  intro hdis
  exact Finset.disjoint_left.mp hdis (E.consecutive i).2.1
    (Finset.mem_image.mpr ⟨E.site i, (E.consecutive i).1, he⟩)

omit [NeZero M] in
/-- A family of disjoint rigid rows cannot be stabilized by a nonzero
translation if each row meets its translate. -/
theorem no_gap_rotation_symmetry (F : Finset (Finset (ZMod M)))
    (hne : F.Nonempty)
    (hrigid : ∀ R ∈ F, RigidRow R)
    (hdisjoint : ∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S)
    (c : ZMod M) (hc : c ≠ 0)
    (hoverlap : ∀ R ∈ F, ¬ Disjoint R ((Motion.rotation c).onRow R)) :
    Motion.rotation c ∉ familyStabilizer F := by
  intro hf
  obtain ⟨R, hR⟩ := hne
  have hS : (Motion.rotation c).onRow R ∈ F := by
    have hf' : (Motion.rotation c).onFamily F = F := hf
    have hm : (Motion.rotation c).onRow R ∈ (Motion.rotation c).onFamily F :=
      Finset.mem_image.mpr ⟨R, hR, rfl⟩
    simpa only [hf'] using hm
  have hsame : (Motion.rotation c).onRow R = R := by
    by_contra hdiff
    exact hoverlap R hR (hdisjoint R hR _ hS (fun heq => hdiff heq.symm))
  exact hc (Motion.rotation.inj (hrigid R hR _ hsame))

/-- The abstract prime-height mechanism with all physical motions and
unlabelled row permutations. Its local assumptions are subsequently supplied
from the actual complete cyclic-gap inventory. -/
theorem prime_height_asymmetric_of_rigid_rows_and_gap_overlap (h n : ℕ)
    (hp : Nat.Prime h) (hodd : Odd h) (hn : 0 < n)
    (F : Finset (Finset (ZMod (h*n)))) (hcard : F.card = h)
    (hrigid : ∀ R ∈ F, RigidRow R)
    (hdisjoint : ∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S)
    (hoverlap : ∀ R ∈ F,
      ¬ Disjoint R ((Motion.rotation (n : ZMod (h*n))).onRow R)) :
    PhysicallyAsymmetric F := by
  letI : NeZero (h*n) := ⟨Nat.mul_ne_zero hp.ne_zero (by omega)⟩
  have hdiv : Nat.card (familyStabilizer F) ∣ h := by
    simpa only [hcard] using stabilizer_card_dvd_rows F hrigid
  have hcases := (Nat.dvd_prime hp).mp hdiv
  have htriv : Nat.card (familyStabilizer F) = 1 := by
    rcases hcases with h1 | hh
    · exact h1
    · have hsym := odd_order_subgroup_contains_gap_rotation h n hp.pos hn hodd
        (familyStabilizer F) hh
      have hne : F.Nonempty := Finset.card_pos.mp (hcard.symm ▸ hp.pos)
      have hlt : n < h*n := by nlinarith [hp.two_le]
      have hnonzero : (n : ZMod (h*n)) ≠ 0 := by
        intro hz
        have hv := congrArg ZMod.val hz
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_zero] at hv
        omega
      exact False.elim (no_gap_rotation_symmetry F hne hrigid hdisjoint
        (n : ZMod (h*n)) hnonzero hoverlap hsym)
  have hbot := (familyStabilizer F).eq_bot_of_card_le (Nat.le_of_eq htriv)
  intro f hf
  have hm : f ∈ familyStabilizer F := hf
  rw [hbot] at hm
  exact hm

/-- All unlabelled physical families of `h` disjoint rows with inventory
`[n]` on the full `h*n` clock are asymmetric when `h` is an odd prime.
No existence supplier and no selected-family quantifier occurs. -/
theorem odd_prime_physical_partition_asymmetric (h n : ℕ)
    (hp : Nat.Prime h) (hodd : Odd h) (hn : 3 ≤ n)
    (F : Finset (Finset (ZMod (h*n)))) (hcard : F.card = h)
    (hdisjoint : ∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S)
    (hgap : ∀ R ∈ F, finiteCyclicGapInventory (h*n) (R.image ZMod.val) =
      Multiset.ofList (fullGapList n)) : PhysicallyAsymmetric F := by
  letI : NeZero (h*n) := ⟨Nat.mul_ne_zero hp.ne_zero (by omega)⟩
  refine prime_height_asymmetric_of_rigid_rows_and_gap_overlap h n hp hodd (by omega)
    F hcard ?_ hdisjoint ?_
  · intro R hR
    exact rigidRow_of_finiteCyclicGapInventory n R hn (hgap R hR)
  · intro R hR
    exact row_meets_gap_translate R (by omega) (hgap R hR)

/-- Theorem 7, exactly on the manuscript's optimal physical clock. -/
theorem every_optimal_corral_of_odd_prime_height_is_asymmetric (h : ℕ)
    (hp : Nat.Prime h) (hodd : Odd h)
    (F : Finset (Finset (ZMod (h*(2*h-1))))) (hcard : F.card = h)
    (hdisjoint : ∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S)
    (hgap : ∀ R ∈ F, finiteCyclicGapInventory (h*(2*h-1)) (R.image ZMod.val) =
      Multiset.ofList (fullGapList (2*h-1))) : PhysicallyAsymmetric F :=
  odd_prime_physical_partition_asymmetric h (2*h-1) hp hodd (by have := hp.two_le; omega)
    F hcard hdisjoint hgap

end CorralFormalization.Results.PrimeHeight
