import CorralFormalization.Results.PrimeHeight.Asymmetry
import CorralFormalization.DiversityCompletion.OptimalCorralCensus

/-!
# Exact connections to the maintained original and physical models

These bridges preserve the actual sites of every witness. In particular,
`OriginalCorral` is not treated as an individual physical object: it is an
existence proposition, so the witness-level theorem quantifies over every
permutation/shift array having the required injective residue map.
-/

namespace CorralFormalization.Results.PrimeHeight

open PhysicalCorral DiversitySymmetry LatinCompletion CorralLatinTailMarker PhysicalCensus

theorem physicalFamily_rows_disjoint {h n : ℕ} [NeZero (width n)] (R : CorralRows h n) :
    ∀ S ∈ physicalFamily R, ∀ T ∈ physicalFamily R, S ≠ T → Disjoint S T := by
  intro S hS T hT hST
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
  apply corralRows_physical_disjoint R i j
  intro hij
  exact hST (congrArg (fun q => physicalSites (width n) (R.sites q)) hij)

theorem physicalFamily_rows_gaps {h n : ℕ} [NeZero (width n)] (R : CorralRows h n) :
    ∀ S ∈ physicalFamily R,
      finiteCyclicGapInventory (width n) (S.image ZMod.val) =
        Multiset.ofList (fullGapList n) := by
  intro S hS
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
  rw [physicalSites_decode _ (R.bounded i)]
  exact R.gaps i

/-- The local physical conditions are equivalent to the maintained row model,
including equality of the actual unlabelled families. -/
theorem physical_family_exact_iff {h n : ℕ} [NeZero (width n)] (hn : 2 ≤ n)
    (F : Finset (Finset (ZMod (width n)))) :
    (F.card = h ∧
      (∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T) ∧
      (∀ S ∈ F, finiteCyclicGapInventory (width n) (S.image ZMod.val) =
        Multiset.ofList (fullGapList n))) ↔
      ∃ R : CorralRows h n, physicalFamily R = F := by
  constructor
  · rintro ⟨hcard, hdis, hgap⟩
    apply physical_family_to_corralRows F hcard _ hdis hgap
    intro S hS
    letI : NeZero n := ⟨by omega⟩
    obtain ⟨E, _, _⟩ := cyclicRow_of_finiteCyclicGapInventory S hn (hgap S hS)
    exact ⟨E.site 0, (E.consecutive 0).1⟩
  · rintro ⟨R, rfl⟩
    exact ⟨physicalFamily_card R, physicalFamily_rows_disjoint R, physicalFamily_rows_gaps R⟩

/-- The original existence predicate and local unlabelled physical model are
equivalent. Full occupancy is not added here; at optimal width it follows
from the already proved partition theorem. -/
theorem originalCorral_iff_exists_physicalFamily {h n : ℕ} (hh : 0 < h) (hn : 2 ≤ n) :
    OriginalCorral h n ↔
      ∃ F : Finset (Finset (ZMod (width n))), F.card = h ∧
        (∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T) ∧
        (∀ S ∈ F, finiteCyclicGapInventory (width n) (S.image ZMod.val) =
          Multiset.ofList (fullGapList n)) := by
  letI : NeZero (width n) := ⟨by have := width_pos n (by omega : 0 < n); omega⟩
  constructor
  · intro hc
    obtain ⟨R⟩ := originalCorral_nonempty_rows (by omega : 0 < n) hc
    exact ⟨physicalFamily R, physicalFamily_card R, physicalFamily_rows_disjoint R,
      physicalFamily_rows_gaps R⟩
  · rintro ⟨F, hlocal⟩
    obtain ⟨R, _⟩ := (physical_family_exact_iff hn F).mp hlocal
    exact R.original hh

/-- Theorem 7 for every `CorralRows` object, on its own physical clock. -/
theorem odd_prime_corralRows_physical_asymmetric {h n : ℕ}
    (hp : Nat.Prime h) (hodd : Odd h) (hn : 3 ≤ n)
    (hwidth : width n = h*n) (R : CorralRows h n) :
    PhysicallyAsymmetric (physicalFamily R) := by
  letI : NeZero (width n) := ⟨by rw [hwidth]; exact Nat.mul_ne_zero hp.ne_zero (by omega)⟩
  have H := odd_prime_physical_partition_asymmetric h n hp hodd hn
  rw [← hwidth] at H
  exact H (physicalFamily R) (physicalFamily_card R)
    (physicalFamily_rows_disjoint R) (physicalFamily_rows_gaps R)

/-- The same universal theorem in the physical representation used by the
maintained full census and its physical orbit definitions. -/
theorem odd_prime_corralRows_realized_asymmetric {h n : ℕ} [NeZero (h*n)]
    (hp : Nat.Prime h) (hodd : Odd h) (hn : 3 ≤ n)
    (hwidth : width n = h*n) (R : CorralRows h n) :
    PhysicallyAsymmetric (realizedFamily R) := by
  have H := odd_prime_corralRows_physical_asymmetric hp hodd hn hwidth R
  unfold physicalFamily at H
  rw [hwidth] at H
  exact H

/-- Membership in the existing census is precisely the local physical
partition contract, rather than membership in a selected constructed family. -/
theorem mem_validOptimalFamilies_iff_local {h n : ℕ} [NeZero (h*n)]
    (hn : 2 ≤ n) (hwidth : width n = h*n) (F : PhysicalFamily h n) :
    F ∈ validOptimalFamilies h n ↔
      F.card = h ∧
      (∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T) ∧
      (∀ S ∈ F, finiteCyclicGapInventory (h*n) (S.image ZMod.val) =
        Multiset.ofList (fullGapList n)) := by
  classical
  letI : NeZero (width n) := ⟨by rw [hwidth]; exact NeZero.ne _⟩
  have H := fun F => physical_family_exact_iff (h := h) hn F
  unfold physicalFamily at H
  rw [hwidth] at H
  simp only [validOptimalFamilies, Finset.mem_filter, Finset.mem_univ, true_and,
    hwidth, true_and]
  exact (H F).symm

theorem every_odd_prime_validOptimalFamily_asymmetric {h n : ℕ} [NeZero (h*n)]
    (hp : Nat.Prime h) (hodd : Odd h)
    (F : PhysicalFamily h n) (hF : F ∈ validOptimalFamilies h n) :
    PhysicallyAsymmetric F := by
  classical
  obtain ⟨hwidth, R, hR⟩ := (Finset.mem_filter.mp hF).2
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by
    intro hn0
    exact NeZero.ne (h*n) (by simp [hn0]))
  have he := width_mul_two n
  rw [hwidth] at he
  have heq : n+1 = 2*h := Nat.eq_of_mul_eq_mul_left hnpos (by nlinarith [he])
  have hn : 3 ≤ n := by have := hp.two_le; omega
  rw [← hR]
  exact odd_prime_corralRows_realized_asymmetric hp hodd hn hwidth R

/-- The literal physical family of one original permutation/shift witness. -/
def originalWitnessPhysicalFamily {h n : ℕ}
    (ρ : Fin h → Equiv.Perm (Fin n)) (τ : Fin h → ℤ) :
    Finset (Finset (ZMod (width n))) :=
  Finset.univ.image (fun i => Finset.univ.image (fun j => originalResidue ρ τ (i,j)))

/-- The original witness is translated without choosing a different witness. -/
def rowsOfOriginalWitness {h n : ℕ} (hn : 0 < n)
    (ρ : Fin h → Equiv.Perm (Fin n)) (τ : Fin h → ℤ)
    (hinj : Function.Injective (originalResidue ρ τ)) : CorralRows h n where
  sites i := originalRowSites (ρ i) (τ i)
  nonempty i := originalRowSites_nonempty hn (ρ i) (τ i)
  bounded i := originalRowSites_bounded hn (ρ i) (τ i)
  gaps i := originalRowSites_gaps hn (ρ i) (τ i)
  disjoint := by
    letI : NeZero (width n) := ⟨by have := width_pos n hn; omega⟩
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hxi
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hxj
    have heq : originalResidue ρ τ (i,a) = originalResidue ρ τ (j,b) :=
      ZMod.val_injective _ (ha.trans hb.symm)
    exact hij (congrArg Prod.fst (hinj heq))

theorem rowsOfOriginalWitness_physicalFamily {h n : ℕ} (hn : 0 < n)
    (ρ : Fin h → Equiv.Perm (Fin n)) (τ : Fin h → ℤ)
    (hinj : Function.Injective (originalResidue ρ τ)) :
    physicalFamily (rowsOfOriginalWitness hn ρ τ hinj) = originalWitnessPhysicalFamily ρ τ := by
  letI : NeZero (width n) := ⟨by have := width_pos n hn; omega⟩
  unfold physicalFamily originalWitnessPhysicalFamily
  congr 1
  funext i
  simp only [rowsOfOriginalWitness, physicalSites, originalRowSites, Finset.image_image,
    Function.comp_def, ZMod.natCast_zmod_val]
  rfl

/-- Theorem 7 for every original permutation/shift witness, with no replacement
by a specially chosen witness and no existential weakening of the conclusion. -/
theorem every_odd_prime_originalWitness_asymmetric {h n : ℕ}
    (hp : Nat.Prime h) (hodd : Odd h) (hn : 3 ≤ n) (hwidth : width n = h*n)
    (ρ : Fin h → Equiv.Perm (Fin n)) (τ : Fin h → ℤ)
    (hinj : Function.Injective (originalResidue ρ τ)) :
    PhysicallyAsymmetric (originalWitnessPhysicalFamily ρ τ) := by
  rw [← rowsOfOriginalWitness_physicalFamily (by omega : 0 < n) ρ τ hinj]
  exact odd_prime_corralRows_physical_asymmetric hp hodd hn hwidth _

/-- No clock-equality or gap-length side condition remains in the optimal
row-model specialization of Theorem 7. -/
theorem every_odd_prime_optimal_corralRows_asymmetric (h : ℕ)
    (hp : Nat.Prime h) (hodd : Odd h) (R : CorralRows h (2*h-1)) :
    PhysicallyAsymmetric (physicalFamily R) :=
  odd_prime_corralRows_physical_asymmetric hp hodd (by have := hp.two_le; omega)
    (LatinTransfer.optimal_width hp.pos rfl) R

/-- The original-witness specialization has precisely the optimal parameter,
primality, oddness, and the original distinct-residue contract as hypotheses. -/
theorem every_odd_prime_optimal_originalWitness_asymmetric (h : ℕ)
    (hp : Nat.Prime h) (hodd : Odd h)
    (ρ : Fin h → Equiv.Perm (Fin (2*h-1))) (τ : Fin h → ℤ)
    (hinj : Function.Injective (originalResidue ρ τ)) :
    PhysicallyAsymmetric (originalWitnessPhysicalFamily ρ τ) :=
  every_odd_prime_originalWitness_asymmetric hp hodd (by have := hp.two_le; omega)
    (LatinTransfer.optimal_width hp.pos rfl) ρ τ hinj

end CorralFormalization.Results.PrimeHeight
