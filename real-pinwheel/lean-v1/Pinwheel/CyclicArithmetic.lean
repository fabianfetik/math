import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace RealPinwheel

/-! Exact integer arithmetic for cyclic splitting. -/

/-- The number of completed `q`-cycles before the slot `j` at time `n`. -/
def cyclicQuot (q j n : ℤ) : ℤ := (n + q - 1 - j) / q

lemma cyclicQuot_eq_div_add {q j n : ℤ} (hq : 0 < q)
    (hj0 : 0 ≤ j) (hjq : j < q) :
    cyclicQuot q j n = n / q + if j < n % q then 1 else 0 := by
  have hr0 : 0 ≤ n % q := Int.emod_nonneg n hq.ne'
  have hrq : n % q < q := Int.emod_lt_of_pos n hq
  have hn : n = n % q + q * (n / q) := (Int.emod_add_mul_ediv n q).symm
  unfold cyclicQuot
  have hnum : n + q - 1 - j =
      (n % q + q * (n / q)) + q - 1 - j :=
    congrArg (fun x : ℤ => x + q - 1 - j) hn
  have hrewrite : n % q + q * (n / q) + q - 1 - j =
      (n % q + q - 1 - j) + q * (n / q) := by ring
  rw [hnum, hrewrite, Int.add_mul_ediv_left _ _ hq.ne']
  by_cases hjr : j < n % q
  · have ht0 : 0 ≤ n % q - j - 1 := by omega
    have htq : n % q - j - 1 < q := by omega
    have htd : (n % q - j - 1) / q = 0 :=
      Int.ediv_eq_zero_of_lt ht0 htq
    have hsplit : n % q + q - 1 - j =
        (n % q - j - 1) + q * 1 := by ring
    rw [hsplit, Int.add_mul_ediv_left _ _ hq.ne', htd]
    simp [hjr]
    ring
  · have ht0 : 0 ≤ n % q + q - 1 - j := by omega
    have htq : n % q + q - 1 - j < q := by omega
    have htd : (n % q + q - 1 - j) / q = 0 :=
      Int.ediv_eq_zero_of_lt ht0 htq
    rw [htd]
    simp [hjr]

theorem cyclicQuot_step {q j n : ℤ} (hq : 0 < q)
    (hj0 : 0 ≤ j) (hjq : j < q) :
    cyclicQuot q j (n + 1) - cyclicQuot q j n =
      if n % q = j then 1 else 0 := by
  have hr0 : 0 ≤ n % q := Int.emod_nonneg n hq.ne'
  have hrq : n % q < q := Int.emod_lt_of_pos n hq
  have hq1 : 1 ≤ q := by omega
  by_cases hwrap : n % q = q - 1
  · have hnrepr : n = (q - 1) + q * (n / q) := by
      calc
        n = n % q + q * (n / q) :=
          (Int.emod_add_mul_ediv n q).symm
        _ = (q - 1) + q * (n / q) := by rw [hwrap]
    have hnextrepr : n + 1 = q * (n / q + 1) := by
      calc
        n + 1 = (q - 1) + q * (n / q) + 1 := congrArg (fun x : ℤ => x + 1) hnrepr
        _ = q * (n / q + 1) := by ring
    have hnext : cyclicQuot q j (n + 1) = n / q + 1 := by
      rw [cyclicQuot, hnextrepr]
      have hres0 : 0 ≤ q - 1 - j := by omega
      have hresq : q - 1 - j < q := by omega
      have hres : (q - 1 - j) / q = 0 :=
        Int.ediv_eq_zero_of_lt hres0 hresq
      have hsplit : q * (n / q + 1) + q - 1 - j =
          (q - 1 - j) + q * (n / q + 1) := by ring
      rw [hsplit, Int.add_mul_ediv_left _ _ hq.ne', hres]
      omega
    have hcur := cyclicQuot_eq_div_add hq hj0 hjq (n := n)
    rw [hnext, hcur]
    by_cases hjlast : j = q - 1
    · simp [hwrap, hjlast]
    · have hjr : j < n % q := by omega
      have hneq : n % q ≠ j := by omega
      simp [hjr, hneq]
  · have hlt : n % q < q - 1 := by omega
    have hnextrepr : n + 1 = (n % q + 1) + q * (n / q) := by
      have hnrepr : n = n % q + q * (n / q) :=
        (Int.emod_add_mul_ediv n q).symm
      calc
        n + 1 = n % q + q * (n / q) + 1 :=
          congrArg (fun x : ℤ => x + 1) hnrepr
        _ = (n % q + 1) + q * (n / q) := by ring
    have hnextmod : (n + 1) % q = n % q + 1 := by
      have hnonneg : 0 ≤ n % q + 1 := by omega
      have hlt' : n % q + 1 < q := by omega
      calc
        (n + 1) % q = ((n % q + 1) + q * (n / q)) % q :=
          congrArg (fun x : ℤ => x % q) hnextrepr
        _ = (n % q + 1) % q := Int.add_mul_emod_self_left _ _ _
        _ = n % q + 1 := Int.emod_eq_of_lt hnonneg hlt'
    have hnextdiv : (n + 1) / q = n / q := by
      have hzero : (n % q + 1) / q = 0 := by
        apply Int.ediv_eq_zero_of_lt
        · omega
        · omega
      calc
        (n + 1) / q = ((n % q + 1) + q * (n / q)) / q :=
          congrArg (fun x : ℤ => x / q) hnextrepr
        _ = (n % q + 1) / q + n / q :=
          Int.add_mul_ediv_left _ _ hq.ne'
        _ = n / q := by rw [hzero]; omega
    have hcur := cyclicQuot_eq_div_add hq hj0 hjq (n := n)
    have hnext := cyclicQuot_eq_div_add hq hj0 hjq (n := n + 1)
    rw [hcur, hnext, hnextdiv, hnextmod]
    by_cases hjr : j < n % q
    · have hjr' : j < n % q + 1 := by omega
      have hneq : n % q ≠ j := by omega
      simp [hjr, hjr', hneq]
    · by_cases hjeq : n % q = j
      · simp [hjeq]
      · have hjr' : ¬ j < n % q + 1 := by omega
        simp [hjeq, hjr, hjr']

theorem cyclicQuot_count_bound {q j n m : ℤ} (hq : 0 < q) :
    n - m < q * (cyclicQuot q j n - cyclicQuot q j m + 1) := by
  have hupper : n + q - 1 - j <
      (cyclicQuot q j n + 1) * q := by
    apply (Int.ediv_lt_iff_lt_mul hq).mp
    dsimp [cyclicQuot]
    omega
  have hlower : cyclicQuot q j m * q ≤ m + q - 1 - j := by
    dsimp [cyclicQuot]
    exact Int.ediv_mul_le _ hq.ne'
  nlinarith

end RealPinwheel
