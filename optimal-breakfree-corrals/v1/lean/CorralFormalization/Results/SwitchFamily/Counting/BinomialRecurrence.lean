import CorralFormalization.Results.SwitchFamily.Counting.BinomialWeights

namespace CorralFormalization.Results.SwitchFamily.Counting

open Finset Matrix

/-- Removing a positive two-tile count shifts the actual solution set by two.
The finite bounding rectangle is only an enumeration device. -/
theorem tileCountPairs_sum_shift_two (n : ℕ) (f : ℕ → ℕ → ℕ) :
    (∑ ab ∈ tileCountPairs (n+2), if ab.1=0 then 0 else f (ab.1-1) ab.2)=
      ∑ ab ∈ tileCountPairs n, f ab.1 ab.2 := by
  classical
  have hfilter :
      (∑ ab ∈ tileCountPairs (n+2), if ab.1=0 then 0 else f (ab.1-1) ab.2)=
      ∑ ab ∈ tileCountPairs (n+2) with ab.1≠0, f (ab.1-1) ab.2 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro ab hab
    by_cases ha : ab.1=0 <;> simp [ha]
  rw [hfilter]
  refine sum_bij (fun ab _ => (ab.1-1,ab.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a,b⟩ hab
    simp only [mem_filter,mem_tileCountPairs] at hab ⊢
    omega
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd heq
    simp only [mem_filter,mem_tileCountPairs] at hab hcd
    simp only [Prod.mk.injEq] at heq ⊢
    omega
  · rintro ⟨a,b⟩ hab
    refine ⟨(a+1,b),?_,?_⟩
    · simp only [mem_filter,mem_tileCountPairs] at hab ⊢
      omega
    · simp
  · intro ab hab
    rfl

/-- The corresponding three-tile shift, retaining all boundary solutions. -/
theorem tileCountPairs_sum_shift_three (n : ℕ) (f : ℕ → ℕ → ℕ) :
    (∑ ab ∈ tileCountPairs (n+3), if ab.2=0 then 0 else f ab.1 (ab.2-1))=
      ∑ ab ∈ tileCountPairs n, f ab.1 ab.2 := by
  classical
  have hfilter :
      (∑ ab ∈ tileCountPairs (n+3), if ab.2=0 then 0 else f ab.1 (ab.2-1))=
      ∑ ab ∈ tileCountPairs (n+3) with ab.2≠0, f ab.1 (ab.2-1) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro ab hab
    by_cases hb : ab.2=0 <;> simp [hb]
  rw [hfilter]
  refine sum_bij (fun ab _ => (ab.1,ab.2-1)) ?_ ?_ ?_ ?_
  · rintro ⟨a,b⟩ hab
    simp only [mem_filter,mem_tileCountPairs] at hab ⊢
    omega
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd heq
    simp only [mem_filter,mem_tileCountPairs] at hab hcd
    simp only [Prod.mk.injEq] at heq ⊢
    omega
  · rintro ⟨a,b⟩ hab
    refine ⟨(a,b+1),?_,?_⟩
    · simp only [mem_filter,mem_tileCountPairs] at hab ⊢
      omega
    · simp
  · intro ab hab
    rfl

/-- The binomial line sum satisfies the same renewal recurrence as the
actual marked local-word count. -/
theorem binomialSum_recurrence (n : ℕ) (hn : 0 < n) :
    binomialSum (n+3)=binomialSum (n+1)+binomialSum n := by
  classical
  have hsum : binomialSum (n+3)=
      (∑ ab ∈ tileCountPairs (n+3),
        if ab.1=0 then 0 else binomialWeight (ab.1-1) ab.2)+
      (∑ ab ∈ tileCountPairs (n+3),
        if ab.2=0 then 0 else binomialWeight ab.1 (ab.2-1)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    rintro ⟨a,b⟩ hab
    have hweight := mem_tileCountPairs.mp hab
    exact binomialWeight_recurrence (by omega)
  rw [hsum,show n+3=(n+1)+2 by omega,tileCountPairs_sum_shift_two]
  rw [show n+1+2=n+3 by omega,tileCountPairs_sum_shift_three]
  rfl

@[simp] theorem binomialSum_one : binomialSum 1=0 := by decide +kernel
@[simp] theorem binomialSum_two : binomialSum 2=2 := by decide +kernel
@[simp] theorem binomialSum_three : binomialSum 3=3 := by decide +kernel

theorem binomial_tileMatrix_cube : tileMatrix^3=tileMatrix+1 := by
  rw [tileMatrix_eq]
  decide +kernel

theorem binomial_trace_recurrence (n : ℕ) :
    Matrix.trace (tileMatrix^(n+3))=
      Matrix.trace (tileMatrix^(n+1))+Matrix.trace (tileMatrix^n) := by
  rw [pow_add,binomial_tileMatrix_cube,mul_add,mul_one,← pow_succ,Matrix.trace_add]

/-- This recurrence is for the actual C, via the proved local-word/trace
bijection. It does not replace C by an assumed recurrence sequence. -/
theorem C_binomial_recurrence (n : ℕ) (hn : 0 < n) : C (n+3)=C (n+1)+C n := by
  letI : NeZero n := ⟨hn.ne'⟩
  rw [C_eq_trace,C_eq_trace,C_eq_trace]
  exact binomial_trace_recurrence n

/-- Actual cyclic local-word counts equal the explicit integral binomial sum
at every positive period, including one, two and repeated tile patterns. -/
theorem C_eq_binomialSum (n : ℕ) (hn : 0 < n) : C n=binomialSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 => simp
    | 2 => simp
    | 3 => simp
    | n+4 =>
      have hC : C (n+4)=C (n+2)+C (n+1) := by
        simpa [Nat.add_assoc] using C_binomial_recurrence (n+1) (by omega)
      have hB : binomialSum (n+4)=binomialSum (n+2)+binomialSum (n+1) := by
        simpa [Nat.add_assoc] using binomialSum_recurrence (n+1) (by omega)
      rw [hC,hB,ih (n+2) (by omega) (by omega),ih (n+1) (by omega) (by omega)]

end CorralFormalization.Results.SwitchFamily.Counting
