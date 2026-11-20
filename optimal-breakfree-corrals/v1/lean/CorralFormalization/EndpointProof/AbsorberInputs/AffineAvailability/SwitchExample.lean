import CorralFormalization.EndpointProof.AbsorberInputs.CandidatePacking.Packing
import CorralFormalization.EndpointProof.Selector.TwoPairSwitch

/-! The literal four-orbit switch as an instance of the complete affine
collision interface. -/

namespace AbsorberInputs.AffineAvailability

open AbsorberInputs.CandidatePacking EndpointRouter
open scoped BigOperators

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def switchData (a b : G) : Data 1 4 2 G where
  root := ![a, b]
  constant := ![0, a+b, -a, -b]
  coefficient := ![![1], ![1], ![-1], ![-1]]

omit [Fintype G] [DecidableEq G] in
theorem switch_individual_pivots (a b : G) : (switchData a b).IndividualPivots := by
  intro j
  refine ⟨0, ?_⟩
  fin_cases j <;> norm_num [Data.IndividualPivots, switchData, Switch.SmallCoefficient]

omit [Fintype G] [DecidableEq G] in
theorem switch_values (a b u : G) (j : Fin 4) :
    (switchData a b).value (fun _ => u) j = ![u, u+a+b, -a-u, -b-u] j := by
  fin_cases j <;> simp [Data.value, GenericAffine.value, switchData] <;> abel

omit [Fintype G] [DecidableEq G] in
theorem switch_value_any (a b : G) (t : Fin 1 → G) (j : Fin 4) :
    (switchData a b).value t j = ![t 0, t 0+a+b, -a-t 0, -b-t 0] j := by
  have ht : t = fun _ => t 0 := by
    funext i
    fin_cases i
    rfl
  rw [ht]
  exact switch_values a b (t 0) j

theorem switch_regular (a b : G) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (han : a ≠ -b) : (switchData a b).Regular := by
  intro q
  rcases q with i | (⟨⟨ij,hij⟩,sg⟩ | ⟨i,j,sg⟩)
  · right
    refine ⟨0, ?_⟩
    fin_cases i <;> norm_num [Data.testCoefficient, switchData, Switch.SmallCoefficient]
  · rcases ij with ⟨i,j⟩
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals cases sg
    all_goals first
      | (right; refine ⟨0, ?_⟩;
         norm_num [Data.testCoefficient, Data.signed, switchData, Switch.SmallCoefficient]; done)
      | (left; intro t;
         simp [Data.testValue_pair, Data.signed, switch_value_any, ha, hb])
    all_goals intro hh
    all_goals first
      | (apply han; apply (add_eq_zero_iff_eq_neg).mp;
         calc
           a+b = -(t 0 - (t 0+a+b)) := by abel
           _ = 0 := by rw [hh]; simp)
      | (apply hab;
         calc
           a = b-(-a+b) := by abel
           _ = b := by rw [hh]; simp)
  · right
    refine ⟨0, ?_⟩
    fin_cases i <;> fin_cases j <;> cases sg <;>
      norm_num [Data.testCoefficient, Data.signed, switchData, Switch.SmallCoefficient]

/-- The complete list for the literal switch has no more than 32 tests. -/
theorem switch_collision_count_le (a b : G) : (switchData a b).collisionCount ≤ 32 := by
  have h := (switchData a b).collisionCount_le_canonical
  norm_num at h ⊢
  exact h

/-- The printed switch itself satisfies the general packing hypotheses;
no collision list, orbit injection or disjointness is supplied by the caller. -/
theorem switch_linear_packing (a b : G)
    (hodd : Odd (Fintype.card G)) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (han : a ≠ -b) (hn : 64 < Fintype.card G) :
    Nonempty (Packed (switchData a b) (Fintype.card G/64)) := by
  have h := exists_linear_packed (switchData a b) hodd (by norm_num)
    (switch_regular a b ha hb hab han) (switch_individual_pivots a b)
    4 32 (by norm_num) (switch_collision_count_le a b) (by omega)
  norm_num at h ⊢
  exact h

/-- The affine coordinates agree with the maintained switch construction,
not merely with another equinumerous candidate family. -/
theorem switch_matches_selector {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (a b u : R) (j : Fin 4) :
    (switchData a b).value (fun _ => u) j = EndpointSelector.representative a b u j := by
  simpa [EndpointSelector.representative] using switch_values a b u j

theorem switch_support_matches_selector {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (a b u : R) :
    (switchData a b).support (fun _ => u) = EndpointSelector.orbitSupport a b u := by
  ext x
  rw [Data.mem_support, EndpointSelector.mem_orbitSupport]
  simp only [switch_matches_selector]

theorem switch_regular_of_selector_roots {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (a b : R) (h : EndpointSelector.RootCondition a b) : (switchData a b).Regular :=
  switch_regular a b h.1 h.2.1 h.2.2.1 h.2.2.2

end
end AbsorberInputs.AffineAvailability
