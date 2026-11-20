import CorralFormalization.ConstructionSupport.PhysicalRows

/-! A fixed two-row seed may be adjoined to the independently chosen
letters without losing the unlabelled support decoder. Only local support
disjointness and the actual nonemptiness/containment of seed rows enter. -/

namespace CorralFormalization.PhysicalCorral

variable {X J A : Type*} [DecidableEq X] [Fintype J]

structure FixedSeedSupport (X J A : Type*) [DecidableEq X] extends SupportAlphabet X J A where
  fixedSupport : Finset X
  fixedRows : Finset (Finset X)
  fixed_disjoint : ∀ j, Disjoint fixedSupport (support j)
  fixed_nonempty : ∀ S ∈ fixedRows, S.Nonempty
  fixed_subset : ∀ S ∈ fixedRows, S ⊆ fixedSupport

namespace FixedSeedSupport

variable (D : FixedSeedSupport X J A)

def assembleFixed (t : J → A) : Finset (Finset X) :=
  D.fixedRows ∪ D.toSupportAlphabet.assemble t

omit [Fintype J] in
theorem fixed_filter_empty (j : J) :
    D.fixedRows.filter (fun S => S ⊆ D.support j) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro S hS hsub
  obtain ⟨x, hx⟩ := D.fixed_nonempty S hS
  exact Finset.disjoint_left.mp (D.fixed_disjoint j) (D.fixed_subset S hS hx) (hsub hx)

theorem recover_with_fixed (t : J → A) (j : J) :
    (D.assembleFixed t).filter (fun S => S ⊆ D.support j) = D.letters j (t j) := by
  classical
  rw [assembleFixed, Finset.filter_union, D.fixed_filter_empty j, Finset.empty_union]
  exact D.toSupportAlphabet.recover_local_letter t j

theorem assembleFixed_injective : Function.Injective D.assembleFixed := by
  classical
  intro t u heq
  funext j
  apply D.distinct j
  calc
    D.letters j (t j) = (D.assembleFixed t).filter (fun S => S ⊆ D.support j) :=
      (D.recover_with_fixed t j).symm
    _ = (D.assembleFixed u).filter (fun S => S ⊆ D.support j) := by rw [heq]
    _ = D.letters j (u j) := D.recover_with_fixed u j

theorem fixedRows_disjoint_assemble (t : J → A) :
    Disjoint D.fixedRows (D.toSupportAlphabet.assemble t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro S hf hs
  obtain ⟨j, hj⟩ := (D.toSupportAlphabet.assemble_mem t S).mp hs
  obtain ⟨x, hx⟩ := D.fixed_nonempty S hf
  exact Finset.disjoint_left.mp (D.fixed_disjoint j)
    (D.fixed_subset S hf hx) (D.subset j (t j) S hj hx)

theorem assembleFixed_card (t : J → A) (r : ℕ)
    (hl : ∀ j a, (D.letters j a).card = r) :
    (D.assembleFixed t).card = D.fixedRows.card + Fintype.card J * r := by
  classical
  rw [assembleFixed, Finset.card_union_of_disjoint (D.fixedRows_disjoint_assemble t),
    D.toSupportAlphabet.assemble_card t r hl]

end FixedSeedSupport

/-- Local validity and disjointness yield actual `CorralRows` even with
the seed held fixed and all other supports independently selectable. -/
theorem fixedSeed_to_corralRows {J A : Type*} [Fintype J] {n : ℕ} [NeZero (width n)]
    (D : FixedSeedSupport (ZMod (width n)) J A) (t : J → A)
    (hcard : ∀ j a, (D.letters j a).card = 2)
    (hfixed : ∀ S ∈ D.fixedRows, ∀ V ∈ D.fixedRows, S ≠ V → Disjoint S V)
    (hlocal : ∀ j a S, S ∈ D.letters j a →
      ∀ V, V ∈ D.letters j a → S ≠ V → Disjoint S V)
    (hfixedgap : ∀ S ∈ D.fixedRows,
      finiteCyclicGapInventory (width n) (S.image ZMod.val) = Multiset.ofList (fullGapList n))
    (hgap : ∀ j a S, S ∈ D.letters j a →
      finiteCyclicGapInventory (width n) (S.image ZMod.val) = Multiset.ofList (fullGapList n)) :
    ∃ R : CorralRows (D.fixedRows.card + Fintype.card J * 2) n,
      physicalFamily R = D.assembleFixed t := by
  classical
  apply physical_family_to_corralRows (D.assembleFixed t) (D.assembleFixed_card t 2 hcard)
  · intro S hS
    rcases Finset.mem_union.mp hS with hf | ht
    · exact D.fixed_nonempty S hf
    · exact D.toSupportAlphabet.assemble_rows_nonempty t S ht
  · intro S hS V hV hSV
    rcases Finset.mem_union.mp hS with hSf | hSt <;>
      rcases Finset.mem_union.mp hV with hVf | hVt
    · exact hfixed S hSf V hVf hSV
    · obtain ⟨j, hj⟩ := (D.toSupportAlphabet.assemble_mem t V).mp hVt
      exact Finset.disjoint_of_subset_left (D.fixed_subset S hSf)
        (Finset.disjoint_of_subset_right (D.subset j (t j) V hj) (D.fixed_disjoint j))
    · obtain ⟨j, hj⟩ := (D.toSupportAlphabet.assemble_mem t S).mp hSt
      exact (Finset.disjoint_of_subset_left (D.fixed_subset V hVf)
        (Finset.disjoint_of_subset_right (D.subset j (t j) S hj) (D.fixed_disjoint j))).symm
    · exact D.toSupportAlphabet.assemble_rows_disjoint t hlocal S hSt V hVt hSV
  · intro S hS
    rcases Finset.mem_union.mp hS with hf | ht
    · exact hfixedgap S hf
    · obtain ⟨j, hj⟩ := (D.toSupportAlphabet.assemble_mem t S).mp ht
      exact hgap j (t j) S hj

end CorralFormalization.PhysicalCorral
