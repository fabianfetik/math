import CorralFormalization.EndpointProof.Probability.RateBudget
import Mathlib.Algebra.Order.Floor.Ring

/-!
Numerical budget for the paired cover construction's nine-orbit Q primitives.

The statement is purely arithmetic. It does not construct a flow, its
orbit packing, or its prescribed reservoir labels.
-/

namespace CorralFormalization.EndpointProof.RateBudget

noncomputable section

/-- The integer form of the packing budget's allowed numerical forbidden support. -/
def flowBudget (τ : ℝ) (n : ℕ) : ℕ :=
  ⌊τ^9 * (n : ℝ) / 10^6⌋₊

/-- packing budget's real-valued bound and the integer support bound are equivalent. -/
theorem le_flowBudget_iff (τ : ℝ) (n m : ℕ) (hτ : 0 ≤ τ) :
    m ≤ flowBudget τ n ↔ (m : ℝ) ≤ τ^9 * (n : ℝ) / 10^6 := by
  unfold flowBudget
  exact Nat.le_floor_iff (by positivity)

/-- A half-mean additive Hoeffding deviation pays packing budget's `C_Q`, with
failure exponent at least `n τ^18/32000`. The actual candidate events and
their success probabilities are separate inputs. -/
theorem flow_mean_and_exponent (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hn : 2000 ≤ n) :
    let M := n / 1000
    let t := (M : ℝ) * τ^9 / 2
    (flowBudget τ n : ℝ) ≤ (M : ℝ) * τ^9 - t ∧
      (τ^18 / 32000) * n ≤ t^2 / (2 * (M : ℝ) * (1/4)) := by
  dsimp only
  have hMnat : 0 < n / 1000 := by omega
  have hM : (0 : ℝ) < (n / 1000 : ℕ) := by exact_mod_cast hMnat
  have hcountNat : n ≤ (n / 1000) * 2000 := by omega
  have hcount : (n : ℝ) ≤ ((n / 1000 : ℕ) : ℝ) * 2000 := by exact_mod_cast hcountNat
  have hτ9 : 0 ≤ τ^9 := by positivity
  have hτ18 : 0 ≤ τ^18 := by positivity
  have hmul9 := mul_le_mul_of_nonneg_right hcount hτ9
  have hmul18 := mul_le_mul_of_nonneg_right hcount hτ18
  have hfloor : (flowBudget τ n : ℝ) ≤ τ^9 * (n : ℝ) / 10^6 := by
    unfold flowBudget
    exact Nat.floor_le (by positivity)
  have htail : ((((n / 1000 : ℕ) : ℝ) * τ^9 / 2)^2) /
      (2 * ((n / 1000 : ℕ) : ℝ) * (1/4)) =
        ((n / 1000 : ℕ) : ℝ) * τ^18 / 2 := by
    field_simp [ne_of_gt hM]
    ring
  rw [htail]
  constructor <;> nlinarith

namespace SamplingConstants

/-- Two polynomial families of P- and Q-event failures, with the checked
weaker Hoeffding rates, jointly pay the single final exact-matching exponential. This
is arithmetic only: each actual event bound must be supplied separately. -/
theorem two_sampling_tails_pay_one_event
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (CP CQ : ℝ) (kP kQ : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N,
      CP * (n : ℝ)^kP * Real.exp (-((p q)^8 / 32000) * n) +
        CQ * (n : ℝ)^kQ * Real.exp (-((tau q)^18 / 32000) * n) ≤
          Real.exp (-((xi q)^4 / 10^6) * n) := by
  obtain ⟨NP, hNP⟩ := sampling_rates_pay_polynomial_union q (2 * CP) kP hq0 hq1
  obtain ⟨NQ, hNQ⟩ := sampling_rates_pay_polynomial_union q (2 * CQ) kQ hq0 hq1
  refine ⟨max NP NQ, ?_⟩
  intro n hn
  have hp := (hNP n ((le_max_left _ _).trans hn)).2
  have hq := (hNQ n ((le_max_right _ _).trans hn)).1
  nlinarith

/-- The additive-Hoeffding coefficient for a P (`true`) or Q (`false`)
primitive. It is not itself an assertion that a primitive exists. -/
def pqTailRate (q : ℝ) (isP : Bool) : ℝ :=
  if isP then (p q)^8 / 32000 else (tau q)^18 / 32000

/-- Any fixed finite collection of polynomially many P/Q query families
can share the *single* final exact-matching exponential budget. Different families
may have different polynomial degrees. Individual event bounds remain
separate inputs to the probabilistic union theorem. -/
theorem finite_sampling_tails_pay_one_event
    {T : Type*} [Fintype T] (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (C : T → ℝ) (k : T → ℕ) (isP : T → Bool) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∑ i, C i * (n : ℝ)^(k i) * Real.exp (-(pqTailRate q (isP i)) * n)) ≤
        Real.exp (-((xi q)^4 / 10^6) * n) := by
  let B : ℝ := (Fintype.card T : ℝ) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have heach : ∀ i : T, ∃ N : ℕ, ∀ n ≥ N,
      (B * C i) * (n : ℝ)^(k i) * Real.exp (-(pqTailRate q (isP i)) * n) ≤
        Real.exp (-((xi q)^4 / 10^6) * n) := by
    intro i
    obtain ⟨N, hN⟩ := sampling_rates_pay_polynomial_union q (B * C i) (k i) hq0 hq1
    refine ⟨N, ?_⟩
    intro n hn
    cases hb : isP i with
    | false => simpa only [pqTailRate, hb, Bool.false_eq_true, ↓reduceIte] using (hN n hn).1
    | true => simpa only [pqTailRate, hb, ↓reduceIte] using (hN n hn).2
  choose Ni hNi using heach
  let N := Finset.univ.sup Ni
  refine ⟨N, ?_⟩
  intro n hn
  have hi : ∀ i : T,
      C i * (n : ℝ)^(k i) * Real.exp (-(pqTailRate q (isP i)) * n) ≤
        Real.exp (-((xi q)^4 / 10^6) * n) / B := by
    intro i
    have hNiN : Ni i ≤ N := Finset.le_sup (Finset.mem_univ i)
    apply (le_div_iff₀ hB).2
    calc
      (C i * (n : ℝ)^(k i) * Real.exp (-(pqTailRate q (isP i)) * n)) * B =
          (B * C i) * (n : ℝ)^(k i) * Real.exp (-(pqTailRate q (isP i)) * n) := by ring
      _ ≤ Real.exp (-((xi q)^4 / 10^6) * n) := hNi i n (hNiN.trans hn)
  have hnonneg : 0 ≤ Real.exp (-((xi q)^4 / 10^6) * n) / B := by positivity
  have hcard : (Fintype.card T : ℝ) ≤ B := by dsimp [B]; linarith
  calc
    (∑ i, C i * (n : ℝ)^(k i) * Real.exp (-(pqTailRate q (isP i)) * n)) ≤
        ∑ _ : T, Real.exp (-((xi q)^4 / 10^6) * n) / B :=
      Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = (Fintype.card T : ℝ) * (Real.exp (-((xi q)^4 / 10^6) * n) / B) := by simp
    _ ≤ B * (Real.exp (-((xi q)^4 / 10^6) * n) / B) :=
      mul_le_mul_of_nonneg_right hcard hnonneg
    _ = Real.exp (-((xi q)^4 / 10^6) * n) := by field_simp [ne_of_gt hB]

end SamplingConstants

end
end CorralFormalization.EndpointProof.RateBudget
