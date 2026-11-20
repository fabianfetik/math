import CorralFormalization.Constructions.Optimal.Odd.OneSwap.Owner
import CorralFormalization.Constructions.Optimal.Odd.OneSwap.Inverse
import CorralFormalization.CorralFromRows
import CorralFormalization.Bases

namespace CorralFormalization.OneSwapOdd

def W (A : ℕ) : ℕ := U A + 2 * h A

/-- The completed rows, with `z=2A`, the unshifted
two-point factor, and the permutation with exactly one image exchange. -/
def R (A : ℕ) (s : Fin (h A)) : Finset ℕ :=
  joinedRow (U A) (C A) (D A) (owner A) s

theorem R_formula (A : ℕ) (s : Fin (h A)) :
    R A s = C A s ∪ (D A (owner A s)).image (fun y => U A + y) := rfl

theorem W_eq_optimal (A : ℕ) : W A = h A * (2 * h A - 1) := by
  have hn : 2 * h A - 1 = 4 * A + 5 := by unfold h; omega
  rw [hn]
  unfold W U h K
  ring

theorem width_eq (A : ℕ) : width (4 * A + 5) = W A := by
  unfold width W U h K
  have hp : (4 * A + 5) * (4 * A + 5 + 1) =
      ((2 * A + 3) * (4 * A + 3) + 2 * (2 * A + 3)) * 2 := by ring
  rw [hp]
  simp

theorem R_nonempty (A : ℕ) (s : Fin (h A)) : (R A s).Nonempty := by
  obtain ⟨x, hx⟩ := C_nonempty A s
  exact ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩

theorem R_bound (A : ℕ) (s : Fin (h A)) (x : ℕ) (hx : x ∈ R A s) : x < W A := by
  exact joined_row_site_lt (C A) (D A) (owner A) (C_bound A) (D_bound A) s x hx

/-- Below the seam, formula (13) returns the owner of the same completed
physical row (12). -/
theorem R_core_inverse (A : ℕ) (hA : 1 ≤ A) (x : ℕ) (hx : x < U A)
    (p : ℕ) (hp : p ∈ oddConstructionRawPrefixSet A)
    (hpr : (p + 2 * A) % K A = x % K A) :
    ∃ hs : coreOwnerValue A x p < h A,
      x ∈ R A ⟨coreOwnerValue A x p, hs⟩ := by
  obtain ⟨hs, hmem⟩ := C_inverse A hA x hx p hp hpr
  exact ⟨hs, Finset.mem_union.mpr (Or.inl hmem)⟩

/-- At and above the seam, the displayed parity formula followed by the
inverse of the actual one-swap permutation returns the completed row. -/
theorem R_tail_inverse (A x : ℕ) (hxlow : U A ≤ x) (hxhigh : x < W A) :
    ∃ ht : twoPointOwnerValue A (x - U A) < h A,
      x ∈ R A ((owner A).symm ⟨twoPointOwnerValue A (x - U A), ht⟩) := by
  have hy : x - U A < 2 * h A := by unfold W at hxhigh; omega
  obtain ⟨ht, hmem⟩ := D_inverse A (x - U A) hy
  refine ⟨ht, Finset.mem_union.mpr (Or.inr ?_)⟩
  apply Finset.mem_image.mpr
  refine ⟨x - U A, ?_, by omega⟩
  simpa only [Equiv.apply_symm_apply] using hmem

/-- The literal one-swap construction partitions exactly the physical clock,
and every actual row has every required positive cyclic gap once, including
both seams and the final wrap.  There are no additional mathematical inputs
beyond the printed range `A≥1`. -/
theorem R_partition_and_exact_gaps (A : ℕ) (hA : 1 ≤ A) :
    (∀ x, x < W A ↔ ∃! s : Fin (h A), x ∈ R A s) ∧
      ∀ s : Fin (h A), finiteCyclicGapInventory (W A) (R A s) =
        Multiset.ofList (fullGapList (4 * A + 5)) := by
  obtain ⟨hpartition, hgap⟩ := joined_factors_contract (C A) (D A) (owner A)
    (C_nonempty A) (D_nonempty A) (C_bound A) (D_bound A)
    (C_partition A hA) (D_partition A) (owner_endpoint_match A hA)
  refine ⟨hpartition, ?_⟩
  intro s
  calc
    _ = finiteCyclicGapInventory (U A) (C A s) +
        finiteCyclicGapInventory (2 * h A) (D A (owner A s)) := hgap s
    _ = Multiset.ofList (oddConstructionGapWord A) + Multiset.ofList [3, K A] := by
      rw [C_gaps A hA, D_gaps]
    _ = Multiset.ofList (oddConstructionFullGapInventory A) := word_plus_missing_inventory A hA
    _ = Multiset.ofList (fullGapList (4 * A + 5)) := by
      rw [oddConstructionFullGapInventory_eq_range]
      rfl

/-- Actual original-contract witnesses whose arrivals lie in the same
literal rows (12). This retains the row construction in the theorem type,
instead of returning an unlocated existential corral witness. -/
theorem literal_original_witness (A : ℕ) (hA : 1 ≤ A) :
    ∃ (ρ : Fin (h A) → Equiv.Perm (Fin (4 * A + 5))) (τ : Fin (h A) → ℤ),
      Function.Injective (originalResidue ρ τ) ∧
        ∀ (s : Fin (h A)) (j : Fin (4 * A + 5)),
          (originalResidue ρ τ (s, j)).val ∈ R A s := by
  classical
  have hwitness : ∀ s : Fin (h A),
      ∃ (ρ : Equiv.Perm (Fin (4 * A + 5))) (τ : ℤ),
        (∀ j : Fin (4 * A + 5),
          ((τ : ZMod (width (4 * A + 5))) + (partialSum ρ j : ZMod (width (4 * A + 5)))).val ∈
            R A s) ∧
        Function.Injective (fun j : Fin (4 * A + 5) =>
          (τ : ZMod (width (4 * A + 5))) + (partialSum ρ j : ZMod (width (4 * A + 5)))) := by
    intro s
    apply gapRow_original_witness _ _ (R_nonempty A s)
    · intro x hx
      rw [width_eq]
      exact R_bound A s x hx
    · rw [width_eq]
      exact (R_partition_and_exact_gaps A hA).2 s
  choose ρ τ hmem hinj using hwitness
  refine ⟨ρ, τ, ?_, ?_⟩
  · intro a b hab
    rcases a with ⟨s, j⟩
    rcases b with ⟨t, k⟩
    have hx : (originalResidue ρ τ (s, j)).val ∈ R A s := hmem s j
    have hy : (originalResidue ρ τ (s, j)).val ∈ R A t := by
      rw [hab]
      exact hmem t k
    obtain ⟨u, _, huniq⟩ := ((R_partition_and_exact_gaps A hA).1 _).1
      (R_bound A s _ hx)
    have hst : s = t := (huniq s hx).trans (huniq t hy).symm
    subst t
    have hjk : j = k := hinj s hab
    exact Prod.ext rfl hjk
  · intro s j
    exact hmem s j

/-- For every `A≥1`, the printed one-swap construction gives an original
corral of height `2A+3` and optimal order `4A+5`. -/
theorem exists_corral (A : ℕ) (hA : 1 ≤ A) :
    OriginalCorral (2 * A + 3) (4 * A + 5) := by
  obtain ⟨ρ, τ, hinj, _⟩ := literal_original_witness A hA
  exact ⟨ρ, τ, hinj⟩

/-- The new uniform construction includes height five (`A=1`); only the
printed singleton and height-three cases are needed separately. -/
theorem all_odd_heights (height : ℕ) (hpos : 0 < height)
    (hodd : height % 2 = 1) : OriginalCorral height (2 * height - 1) := by
  by_cases h1 : height = 1
  · subst height
    exact optimal_base_height_one
  · by_cases h3 : height = 3
    · subst height
      exact optimal_base_height_three
    · let A := (height - 3) / 2
      have hA : 1 ≤ A := by dsimp [A]; omega
      have hheight : height = 2 * A + 3 := by dsimp [A]; omega
      have horder : 2 * height - 1 = 4 * A + 5 := by omega
      rw [horder, hheight]
      exact exists_corral A hA

end CorralFormalization.OneSwapOdd
