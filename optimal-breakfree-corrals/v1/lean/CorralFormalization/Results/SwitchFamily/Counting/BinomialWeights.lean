import CorralFormalization.Results.SwitchFamily.Counting.TraceBridge

/-!
# Integral binomial weights for marked cyclic 2/3 layouts

The rational summand in (A8) is represented by an integer. Its two terms
mark time zero inside a two-tile or a three-tile respectively. No division
by an orbit size occurs; repeated cyclic patterns retain all marked phases.
-/

namespace CorralFormalization.Results.SwitchFamily.Counting

open Finset

/-- The finite set of all nonnegative tile counts with total phase length n. -/
def tileCountPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n+1)) ×ˢ (range (n+1))).filter (fun ab => 2*ab.1+3*ab.2=n)

@[simp] theorem mem_tileCountPairs {n a b : ℕ} :
    (a,b) ∈ tileCountPairs n ↔ 2*a+3*b=n := by
  simp only [tileCountPairs,mem_filter,mem_product,mem_range]
  omega

/-- Integral form of `(2a+3b)/(a+b) * choose (a+b) a` away from the
excluded empty sequence. -/
def binomialWeight (a b : ℕ) : ℕ :=
  if a+b=0 then 0 else
    2*Nat.choose (a+b-1) b+3*Nat.choose (a+b-1) a

@[simp] theorem binomialWeight_zero_zero : binomialWeight 0 0=0 := rfl

@[simp] theorem binomialWeight_succ_zero (a : ℕ) : binomialWeight (a+1) 0=2 := by
  simp [binomialWeight]

@[simp] theorem binomialWeight_zero_succ (b : ℕ) : binomialWeight 0 (b+1)=3 := by
  simp [binomialWeight]

theorem binomialWeight_succ_succ (a b : ℕ) :
    binomialWeight (a+1) (b+1)=binomialWeight a (b+1)+binomialWeight (a+1) b := by
  have hs : a+1+(b+1)-1=a+b+1 := by omega
  have hs' : a+(b+1)-1=a+b := by omega
  have hs'' : a+1+b-1=a+b := by omega
  simp only [binomialWeight,show a+1+(b+1)≠0 by omega,
    show a+(b+1)≠0 by omega,show a+1+b≠0 by omega,if_false,hs,hs',hs'']
  rw [Nat.choose_succ_succ',Nat.choose_succ_succ']
  ring

/-- The Pascal recurrence is valid on all cells of phase weight at least
four; its two initial cells have weights two and three. -/
theorem binomialWeight_recurrence {a b : ℕ} (hlarge : 4 ≤ 2*a+3*b) :
    binomialWeight a b=
      (if a=0 then 0 else binomialWeight (a-1) b)+
      (if b=0 then 0 else binomialWeight a (b-1)) := by
  cases a with
  | zero =>
    cases b with
    | zero => omega
    | succ b =>
      cases b with
      | zero => omega
      | succ b => simp
  | succ a =>
    cases b with
    | zero =>
      cases a with
      | zero => omega
      | succ a => simp
    | succ b => simpa using binomialWeight_succ_succ a b

/-- Clearing the printed denominator gives a natural-number identity. -/
theorem binomialWeight_mul (a b : ℕ) (hpos : 0 < a+b) :
    (a+b)*binomialWeight a b=(2*a+3*b)*Nat.choose (a+b) a := by
  have hs : a+b-1+1=a+b := by omega
  have ha := Nat.choose_mul_succ_eq (a+b-1) b
  have hb := Nat.choose_mul_succ_eq (a+b-1) a
  rw [hs,Nat.add_sub_cancel_right,← Nat.choose_symm_add] at ha
  rw [hs,Nat.add_sub_cancel_left] at hb
  rw [binomialWeight,if_neg (by omega)]
  calc
    (a+b)*(2*(a+b-1).choose b+3*(a+b-1).choose a) =
        2*((a+b-1).choose b*(a+b))+3*((a+b-1).choose a*(a+b)) := by ring
    _ = (2*a+3*b)*(a+b).choose a := by rw [ha,hb]; ring

/-- The division in A8 is field division, rather than truncating natural
division (which would be incorrect already at a=b=1). -/
theorem binomialWeight_eq_fraction (K : Type*) [Field K] [CharZero K]
    (a b : ℕ) (hpos : 0 < a+b) :
    (binomialWeight a b : K)=
      ((2*a+3*b : ℕ) : K)/(a+b : ℕ)*(Nat.choose (a+b) a : K) := by
  have hk : ((a+b : ℕ) : K)≠0 := by exact_mod_cast hpos.ne'
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hk).mpr
  have hh : (binomialWeight a b : K)*((a+b : ℕ) : K)=
      ((2*a+3*b : ℕ) : K)*(Nat.choose (a+b) a : K) := by
    exact_mod_cast (by simpa [mul_comm] using binomialWeight_mul a b hpos)
  exact hh

/-- The integer sum that will be identified with the actual marked-word C. -/
def binomialSum (n : ℕ) : ℕ := ∑ ab ∈ tileCountPairs n, binomialWeight ab.1 ab.2

end CorralFormalization.Results.SwitchFamily.Counting
