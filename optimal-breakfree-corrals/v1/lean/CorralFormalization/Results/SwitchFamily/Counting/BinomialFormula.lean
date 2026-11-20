import CorralFormalization.Results.SwitchFamily.Counting.BinomialRecurrence

/-!
# The printed binomial formula (A8) for the actual layout count

C is the cardinality of actual cyclic state words, with a labelled phase
zero and its closing edge. Its trace bridge counts repeated cyclic patterns
with their actual marked phases. The proof below never identifies distinct
marked phases using an assumed free rotation action.
-/

namespace CorralFormalization.Results.SwitchFamily.Counting

open Finset

/-- Formula A8, with its printed division interpreted in a characteristic-zero
field. Both tile counts range over precisely the solutions 2a+3b=j. -/
theorem C_binomial_formula (K : Type*) [Field K] [CharZero K]
    (j : ℕ) (hj : 0 < j) :
    (C j : K)=∑ ab ∈ tileCountPairs j,
      (j : K)/((ab.1+ab.2 : ℕ) : K)*(Nat.choose (ab.1+ab.2) ab.1 : K) := by
  rw [C_eq_binomialSum j hj,binomialSum,Nat.cast_sum]
  apply sum_congr rfl
  rintro ⟨a,b⟩ hab
  have hlen := mem_tileCountPairs.mp hab
  have hpos : 0 < a+b := by omega
  rw [binomialWeight_eq_fraction K a b hpos,hlen]

/-- A statement-facing version exposing the finite solution set directly. -/
theorem C_binomial_formula_A8 (j : ℕ) (hj : 0 < j) :
    (C j : ℚ)=∑ ab ∈ ((range (j+1)) ×ˢ (range (j+1))).filter
        (fun ab : ℕ × ℕ => 2*ab.1+3*ab.2=j),
      (j : ℚ)/((ab.1+ab.2 : ℕ) : ℚ)*(Nat.choose (ab.1+ab.2) ab.1 : ℚ) :=
  C_binomial_formula ℚ j hj

/-- The same exact equality over the reals used by the paper. -/
theorem C_binomial_formula_real (j : ℕ) (hj : 0 < j) :
    (C j : ℝ)=∑ ab ∈ tileCountPairs j,
      (j : ℝ)/((ab.1+ab.2 : ℕ) : ℝ)*(Nat.choose (ab.1+ab.2) ab.1 : ℝ) :=
  C_binomial_formula ℝ j hj

/-- An equivalent two-index bounded sum; its only nonzero terms satisfy the
printed linear tile-count equation. -/
theorem C_binomial_formula_double_sum (K : Type*) [Field K] [CharZero K]
    (j : ℕ) (hj : 0 < j) :
    (C j : K)=∑ a ∈ range (j+1), ∑ b ∈ range (j+1),
      if 2*a+3*b=j then
        (j : K)/((a+b : ℕ) : K)*(Nat.choose (a+b) a : K) else 0 := by
  simpa only [tileCountPairs,sum_filter,sum_product] using C_binomial_formula K j hj

/-- Each full rational summand is integral. In general j/(a+b) itself need
not be integral, so truncating that ratio before multiplying is incorrect. -/
theorem binomial_summand_integral {j a b : ℕ} (hj : 0 < j)
    (hab : 2*a+3*b=j) :
    (a+b) ∣ j*Nat.choose (a+b) a := by
  refine ⟨binomialWeight a b,?_⟩
  have h := binomialWeight_mul a b (by omega)
  rw [hab] at h
  exact h.symm

/-- A natural-number formulation divides only after multiplying the complete
binomial summand, as justified by its proved divisibility. -/
theorem C_binomial_formula_nat (j : ℕ) (hj : 0 < j) :
    C j=∑ ab ∈ tileCountPairs j,
      (j*Nat.choose (ab.1+ab.2) ab.1)/(ab.1+ab.2) := by
  rw [C_eq_binomialSum j hj,binomialSum]
  apply sum_congr rfl
  rintro ⟨a,b⟩ hab
  have hlen := mem_tileCountPairs.mp hab
  have hk : 0 < a+b := by omega
  have hweight := binomialWeight_mul a b hk
  rw [hlen] at hweight
  rw [← hweight,Nat.mul_comm (a+b),Nat.mul_div_cancel _ hk]

end CorralFormalization.Results.SwitchFamily.Counting
