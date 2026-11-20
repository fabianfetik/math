import CorralFormalization.EndpointProof.Matching.AbsorptionAssembly.FiniteAssembly

/-!
The exclusion and quantifier-order part of H7 and the final paragraph of
the exact receiver.  `RawCoreSupply` and the later near-matching
supplier are assumptions, not existence theorems.  Both act on the same
actual tagged target and the same already fixed raw reservoir.
-/

open scoped Classical BigOperators

namespace EndpointMatching.AbsorptionAssembly

open EndpointFlow.AbelianTransport

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- H7 uses projection, not inverse closure, and includes zero. -/
def targetExclusion (R T : Finset (Vertex G)) : Finset G :=
  (R \ T).image Prod.snd ∪ {0}

theorem targetExclusion_card_le (R T : Finset (Vertex G)) :
    (targetExclusion R T).card ≤ (R \ T).card + 1 := by
  calc
    _ ≤ ((R \ T).image Prod.snd).card + ({0} : Finset G).card :=
      Finset.card_union_le _ _
    _ ≤ (R \ T).card + 1 := by
      simpa using Nat.add_le_add_right (Finset.card_image_le (s := R \ T) (f := Prod.snd)) 1

theorem core_subset_actualTarget {R T A : Finset (Vertex G)} (hAR : A ⊆ R)
    (havoid : Disjoint (A.image Prod.snd) (targetExclusion R T)) : A ⊆ T := by
  intro v hv
  by_contra hvT
  have hvU : v.2 ∈ targetExclusion R T := Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hAR hv, hvT⟩, rfl⟩)
  exact Finset.disjoint_left.mp havoid (Finset.mem_image.mpr ⟨v, hv, rfl⟩) hvU

theorem core_nonzero {R T A : Finset (Vertex G)}
    (havoid : Disjoint (A.image Prod.snd) (targetExclusion R T)) :
    ∀ v ∈ A, v.2 ≠ 0 := by
  intro v hv hz
  apply Finset.disjoint_left.mp havoid (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  exact Finset.mem_union_right _ (by simpa using hz)

/-- Finite contract of H1.  The order is `U`, then a core `A`, then every
later admissible residual through `AbsorbsUpTo`.  `rawMinus` is an actual
specified tagged subset of the signed original sample. -/
def RawCoreSupply (rawMinus : Finset (Vertex G)) (capacity coreBound : ℕ) : Prop :=
  ∀ U : Finset G, U.card ≤ capacity →
    ∃ A : Finset (Vertex G), A ⊆ rawMinus ∧ Disjoint (A.image Prod.snd) U ∧
      A.card ≤ coreBound ∧ AbsorbsUpTo A capacity

/-- Select the core after the target exclusion, preserving the original
raw-minus containment.  Empty absorption proves its balance and checksum. -/
theorem select_core_for_actualTarget {R T rawMinus : Finset (Vertex G)}
    {capacity coreBound : ℕ} (hminus : rawMinus ⊆ R)
    (hcore : RawCoreSupply rawMinus capacity coreBound)
    (hbudget : (R \ T).card + 1 ≤ capacity) :
    ∃ A : Finset (Vertex G), A ⊆ rawMinus ∧ A ⊆ T ∧
      (∀ v ∈ A, v.2 ≠ 0) ∧ Balanced A ∧ (∑ v ∈ A, v.2 = 0) ∧
      A.card ≤ coreBound ∧ AbsorbsUpTo A capacity := by
  obtain ⟨A, hAm, havoid, hsize, habs⟩ := hcore (targetExclusion R T)
    ((targetExclusion_card_le R T).trans hbudget)
  obtain ⟨MA⟩ := habs.matches_empty
  exact ⟨A, hAm, core_subset_actualTarget (hAm.trans hminus) havoid,
    core_nonzero havoid, matching_balanced MA, matching_sum_eq_zero MA, hsize, habs⟩

/-- Deterministic composition on one exposed sample.  The near matching is
chosen only after the core; its residual is the actual complement.  This
does not assert either probabilistic supplier or any of its constants. -/
theorem exact_on_actualTarget_of_suppliers {R T rawMinus : Finset (Vertex G)}
    {capacity coreBound : ℕ} (hminus : rawMinus ⊆ R)
    (hcore : RawCoreSupply rawMinus capacity coreBound)
    (hbudget : (R \ T).card + 1 ≤ capacity)
    (hT : Balanced T) (hsum : ∑ v ∈ T, v.2 = 0)
    (hnear : ∀ A : Finset (Vertex G), A ⊆ T → (∀ v ∈ A, v.2 ≠ 0) →
      Balanced A → (∑ v ∈ A, v.2 = 0) → A.card ≤ coreBound →
      Nonempty (CompatibleNearMatching T A capacity)) : Nonempty (Matching T) := by
  obtain ⟨A, _, hAT, hnz, hb, hs, hsize, habs⟩ :=
    select_core_for_actualTarget hminus hcore hbudget
  obtain ⟨near⟩ := hnear A hAT hnz hb hs hsize
  exact exact_of_absorber_and_nearMatching hT hsum hAT habs near


end
end EndpointMatching.AbsorptionAssembly
