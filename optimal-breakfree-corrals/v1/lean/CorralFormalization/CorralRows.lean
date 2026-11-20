import CorralFormalization.PermutationWord
import CorralFormalization.CorralFromRows

namespace CorralFormalization

/-- A corral as actual nonempty disjoint point sets on its triangular clock.
Full occupancy is not required. -/
structure CorralRows (h n : ℕ) where
  sites : Fin h → Finset ℕ
  nonempty : ∀ i, (sites i).Nonempty
  bounded : ∀ i x, x ∈ sites i → x < width n
  disjoint : ∀ i j, i ≠ j → Disjoint (sites i) (sites j)
  gaps : ∀ i, finiteCyclicGapInventory (width n) (sites i) =
    Multiset.ofList (fullGapList n)

theorem CorralRows.original {h n : ℕ} (R : CorralRows h n) (hh : 0 < h) :
    OriginalCorral h n :=
  originalCorral_of_disjoint_gap_rows h n hh R.sites R.nonempty R.bounded R.disjoint R.gaps

/-- Replacing the final full-winding arrival by the initial zero gives
exactly the proper-prefix point set. This also handles the singleton word. -/
theorem word_arrivals_eq_shifted_prefixes (W c : ℕ) (g : List ℕ)
    (hne : 0 < g.length) (hsum : g.sum = W) :
    (Finset.range g.length).image (fun j => (c + (g.take (j + 1)).sum) % W) =
      (properPrefixSites g).toFinset.image (fun p => (p + c) % W) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset,
    mem_properPrefixSites_iff]
  constructor
  · rintro ⟨j, hj, hx⟩
    by_cases hproper : j + 1 < g.length
    · refine ⟨(g.take (j + 1)).sum, ⟨j + 1, hproper, rfl⟩, ?_⟩
      simpa [Nat.add_comm] using hx
    · have hlast : j + 1 = g.length := by omega
      refine ⟨0, ⟨0, hne, by simp⟩, ?_⟩
      simpa [hlast, hsum] using hx
  · rintro ⟨p, ⟨j, hj, hp⟩, hx⟩
    by_cases hj0 : j = 0
    · subst j
      have hp0 : p = 0 := by simpa using hp.symm
      refine ⟨g.length - 1, by omega, ?_⟩
      have hl : g.length - 1 + 1 = g.length := by omega
      simpa [hl, hsum, hp0] using hx
    · refine ⟨j - 1, by omega, ?_⟩
      have hjform : j - 1 + 1 = j := by omega
      simpa [hjform, hp, Nat.add_comm] using hx

/-- The actual arrivals of one original permutation and integer shift. -/
def originalRowSites {n : ℕ} (ρ : Equiv.Perm (Fin n)) (τ : ℤ) : Finset ℕ :=
  Finset.univ.image (fun j : Fin n =>
    ((τ : ZMod (width n)) + (partialSum ρ j : ZMod (width n))).val)

theorem originalRowSites_eq_shifted_prefixes {n : ℕ} (hn : 0 < n)
    (ρ : Equiv.Perm (Fin n)) (τ : ℤ) :
    originalRowSites ρ τ = (properPrefixSites (permutationWord ρ)).toFinset.image
      (fun p => (p + (τ : ZMod (width n)).val) % width n) := by
  letI : NeZero (width n) := ⟨by have := width_pos n hn; omega⟩
  have hval (j : Fin n) :
      ((τ : ZMod (width n)) + (partialSum ρ j : ZMod (width n))).val =
        ((τ : ZMod (width n)).val + ((permutationWord ρ).take (j.val + 1)).sum) % width n := by
    rw [ZMod.val_add, ZMod.val_natCast, permutationWord_partialSum]
    exact Nat.add_mod_mod _ _ _
  rw [← word_arrivals_eq_shifted_prefixes (width n) (τ : ZMod (width n)).val
    (permutationWord ρ) (by rw [permutationWord_length]; exact hn) (permutationWord_sum ρ)]
  ext x
  simp only [originalRowSites, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_range, permutationWord_length]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.val, j.isLt, (hval j).symm.trans hj⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨⟨j, hj⟩, (hval ⟨j, hj⟩).trans hx⟩

theorem originalRowSites_nonempty {n : ℕ} (hn : 0 < n)
    (ρ : Equiv.Perm (Fin n)) (τ : ℤ) : (originalRowSites ρ τ).Nonempty := by
  exact ⟨_, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

theorem originalRowSites_bounded {n : ℕ} (hn : 0 < n)
    (ρ : Equiv.Perm (Fin n)) (τ : ℤ) (x : ℕ) (hx : x ∈ originalRowSites ρ τ) :
    x < width n := by
  letI : NeZero (width n) := ⟨by have := width_pos n hn; omega⟩
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact ZMod.val_lt _

theorem originalRowSites_gaps {n : ℕ} (hn : 0 < n)
    (ρ : Equiv.Perm (Fin n)) (τ : ℤ) :
    finiteCyclicGapInventory (width n) (originalRowSites ρ τ) =
      Multiset.ofList (fullGapList n) := by
  have hpos : ∀ x ∈ permutationWord ρ, 0 < x := by
    intro x hx
    exact (permutationWord_range ρ x hx).1
  have hbound : ∀ p ∈ (properPrefixSites (permutationWord ρ)).toFinset, p < width n := by
    intro p hp
    simpa [permutationWord_sum] using
      properPrefixSites_lt_sum (permutationWord ρ) hpos p (List.mem_toFinset.mp hp)
  rw [originalRowSites_eq_shifted_prefixes hn ρ τ,
    finite_set_cyclic_gap_rotate _ _ _ (width_pos n hn) hbound]
  have hlen := permutationWord_length ρ
  have hsum := permutationWord_sum ρ
  have hperm := permutationWord_perm_full ρ
  cases hw : permutationWord ρ with
  | nil => simp [hw] at hlen; omega
  | cons a as =>
    have hpos' : ∀ x ∈ a :: as, 0 < x := by simpa [hw] using hpos
    have hsum' : (a :: as).sum = width n := by simpa [hw] using hsum
    rw [← hsum', properPrefixSites_finite_gaps a as hpos']
    exact Multiset.coe_eq_coe.mpr (by simpa [hw] using hperm)

/-- Every original witness yields its actual disjoint row point sets with
the exact full cyclic-gap inventory. -/
theorem originalCorral_nonempty_rows {h n : ℕ} (hn : 0 < n)
    (hc : OriginalCorral h n) : Nonempty (CorralRows h n) := by
  letI : NeZero (width n) := ⟨by have := width_pos n hn; omega⟩
  obtain ⟨ρ, τ, hinj⟩ := hc
  refine ⟨{ sites := fun i => originalRowSites (ρ i) (τ i)
            nonempty := fun i => originalRowSites_nonempty hn (ρ i) (τ i)
            bounded := fun i => originalRowSites_bounded hn (ρ i) (τ i)
            disjoint := ?_
            gaps := fun i => originalRowSites_gaps hn (ρ i) (τ i) }⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hxi
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hxj
  have heq : originalResidue ρ τ (i, a) = originalResidue ρ τ (j, b) := by
    apply ZMod.val_injective
    exact ha.trans hb.symm
  have hp := hinj heq
  exact hij (congrArg Prod.fst hp)

theorem originalCorral_iff_nonempty_rows (h n : ℕ) (hh : 0 < h) (hn : 0 < n) :
    OriginalCorral h n ↔ Nonempty (CorralRows h n) := by
  constructor
  · exact originalCorral_nonempty_rows hn
  · rintro ⟨R⟩
    exact R.original hh

end CorralFormalization
