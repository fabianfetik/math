import CorralFormalization.EndpointProof.AbsorberInputs.CandidatePacking.Packing
import CorralFormalization.EndpointProof.Selector.Stars.Basic

/-! The literal k-target star as an instance of the complete affine
collision interface. -/

namespace AbsorberInputs.AffineAvailability

open AbsorberInputs.CandidatePacking EndpointRouter
open scoped BigOperators

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def starData {k : ℕ} (a : Fin k → G) : Data 1 (k+1) k G where
  root := a
  constant := Fin.cases 0 (fun i => -a i)
  coefficient := Fin.cases ![1] (fun _ => ![-1])

omit [Fintype G] [DecidableEq G] in
theorem star_individual_pivots {k : ℕ} (a : Fin k → G) : (starData a).IndividualPivots := by
  intro j
  refine ⟨0, ?_⟩
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i,rfl⟩ <;>
    norm_num [starData, Switch.SmallCoefficient]

omit [Fintype G] [DecidableEq G] in
theorem star_values {k : ℕ} (a : Fin k → G) (t : Fin 1 → G) (j : Fin (k+1)) :
    (starData a).value t j = Fin.cases (t 0) (fun i => -a i-t 0) j := by
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i,rfl⟩ <;>
    simp [Data.value, GenericAffine.value, starData, sub_eq_add_neg]

/-- The complete zero, signed-pair and signed-root tests are regular for
arbitrarily many nonzero distinct targets, independently of group order. -/
theorem star_regular {k : ℕ} (a : Fin k → G) (hzero : ∀i, a i ≠ 0)
    (hinj : Function.Injective a) : (starData a).Regular := by
  intro q
  rcases q with i | (⟨⟨ij,hij⟩,sg⟩ | ⟨i,j,sg⟩)
  · right
    refine ⟨0, ?_⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩ <;>
      norm_num [Data.testCoefficient, starData, Switch.SmallCoefficient]
  · rcases ij with ⟨i,j⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
      · simp at hij
      · cases sg
        · right; refine ⟨0, ?_⟩
          norm_num [Data.testCoefficient, Data.signed, starData, Switch.SmallCoefficient]
        · left; intro t
          simpa [Data.testValue_pair, Data.signed, star_values] using hzero j
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
      · simp at hij
      · cases sg
        · left; intro t
          have hneq : a i ≠ a j := by
            intro h
            have he := hinj h
            exact (ne_of_lt (Fin.succ_lt_succ_iff.mp hij)) he
          simp only [Data.testValue_pair, Data.signed, Bool.false_eq_true, ↓reduceIte,
            star_values, Fin.cases_succ]
          intro heq
          apply hneq
          calc
            a i = a j - (-a i - t 0 - (-a j - t 0)) := by abel
            _ = a j := by rw [heq]; simp
        · right; refine ⟨0, ?_⟩
          norm_num [Data.testCoefficient, Data.signed, starData, Switch.SmallCoefficient]
  · right
    refine ⟨0, ?_⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩ <;> cases sg <;>
      norm_num [Data.testCoefficient, Data.signed, starData, Switch.SmallCoefficient]

/-- For up to three targets, the entire canonical collision list has at
most forty entries, exactly as used for the displayed star construction. -/
theorem star_collision_count_le {k : ℕ} (a : Fin k → G) (hk : k ≤ 3) :
    (starData a).collisionCount ≤ 40 := by
  have h := (starData a).collisionCount_le_canonical
  interval_cases k <;> norm_num [Nat.choose] at * <;> omega

/-- The literal star meets the general packing interface without a supplied
collision list, orbit injection, or disjointness premise. -/
theorem star_linear_packing {k : ℕ} (a : Fin k → G) (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hzero : ∀ i, a i ≠ 0)
    (hinj : Function.Injective a) (hn : 80 < Fintype.card G) :
    Nonempty (Packed (starData a) (Fintype.card G/64)) := by
  have h := exists_linear_packed (starData a) hodd (by omega)
    (star_regular a hzero hinj) (star_individual_pivots a)
    4 40 (by omega) (star_collision_count_le a hk) (by omega)
  norm_num at h ⊢
  exact h

/-- The affine coordinates agree with the maintained star construction. -/
theorem star_matches_selector {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {k : ℕ} (a : Fin k → R) (u : R) (j : Fin (k+1)) :
    (starData a).value (fun _ => u) j =
      EndpointSelector.Stars.starRepresentative a u (Fin.cases none some j) := by
  rw [star_values]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩ <;>
    rfl

theorem star_support_matches_selector {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {k : ℕ} (a : Fin k → R) (u : R) :
    (starData a).support (fun _ => u) = EndpointSelector.Stars.starSupport a u := by
  ext x
  rw [Data.mem_support, EndpointSelector.Stars.mem_starSupport]
  constructor
  · rintro ⟨j,h⟩
    refine ⟨Fin.cases none some j, ?_⟩
    simpa only [star_matches_selector] using h
  · rintro ⟨j,h⟩
    cases j with
    | none =>
      refine ⟨0, ?_⟩
      simpa only [star_matches_selector, Fin.cases_zero] using h
    | some j =>
      refine ⟨j.succ, ?_⟩
      simpa only [star_matches_selector, Fin.cases_succ] using h

theorem star_regular_of_selector_roots {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {k : ℕ} (a : Fin k → R) (h : EndpointSelector.Stars.StarRoots a) :
    (starData a).Regular := by
  apply star_regular a h.1
  intro i j hij
  by_contra hne
  exact (h.2 i j hne).1 hij

end
end AbsorberInputs.AffineAvailability
