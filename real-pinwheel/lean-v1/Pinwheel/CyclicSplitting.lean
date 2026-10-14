import Pinwheel.Periodic
import Pinwheel.Rates
import Pinwheel.CyclicArithmetic

/-!
# Cyclic splitting of arbitrary bilateral schedules

A signed cumulative service count numbers each parent's occurrences relative
to time zero. Its differences are the actual counts on every half-open window,
including windows crossing zero. Taking this number modulo a positive group
size distributes all parent occurrences cyclically among its children.
-/

namespace RealPinwheel

open Classical

variable {α : Type*}

@[simp] theorem serviceCount_zero_length (S : ℤ → α) (i : α) (m : ℤ) :
    serviceCount S i m 0 = 0 := by
  classical
  simp [serviceCount, windowCount]

@[simp] theorem serviceCount_one_length (S : ℤ → α) (i : α) (m : ℤ) :
    serviceCount S i m 1 = if S m = i then 1 else 0 := by
  classical
  have hset : Finset.Ico m (m + 1) = {m} := by
    ext t
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  by_cases h : S m = i <;>
    simp [serviceCount, windowCount, hset, Finset.filter_singleton, h]

/-- Signed number of services between zero and `t`, before slot `t`. -/
noncomputable def serviceIndex (S : ℤ → α) (i : α) (t : ℤ) : ℤ :=
  if 0 ≤ t then (serviceCount S i 0 t : ℤ)
  else -(serviceCount S i t (-t) : ℤ)

theorem serviceIndex_step (S : ℤ → α) (i : α) (t : ℤ) :
    serviceIndex S i (t + 1) - serviceIndex S i t =
      if S t = i then 1 else 0 := by
  classical
  by_cases ht : 0 ≤ t
  · have ht1 : 0 ≤ t + 1 := by omega
    have h := serviceCount_add S i 0 t 1 ht (by omega)
    simp only [zero_add, serviceCount_one_length] at h
    simp only [serviceIndex, if_pos ht, if_pos ht1]
    rw [h]
    split_ifs <;> simp_all
  · have ht' : t ≤ -1 := by omega
    have h := serviceCount_add S i t 1 (-(t+1)) (by omega) (by omega)
    have hlen : 1 + -(t+1) = -t := by omega
    rw [hlen, serviceCount_one_length] at h
    by_cases ht1 : 0 ≤ t + 1
    · have heq : t + 1 = 0 := by omega
      simp only [heq, neg_zero, serviceCount_zero_length, add_zero] at h
      simp only [serviceIndex, if_neg ht, heq,
        serviceCount_zero_length, Nat.cast_zero]
      rw [h]
      split_ifs <;> rfl
    · simp only [serviceIndex, if_neg ht, if_neg ht1]
      rw [h]
      split_ifs <;> simp_all

/-- Any integer counter with the service increments counts every window. -/
theorem serviceCount_eq_of_counter (S : ℤ → α) (i : α) (c : ℤ → ℤ)
    (hc : ∀ t, c (t+1) - c t = if S t = i then 1 else 0)
    (m : ℤ) (L : ℕ) :
    c (m + (L : ℤ)) - c m =
      (serviceCount S i m (L : ℤ) : ℤ) := by
  classical
  induction L with
  | zero => simp
  | succ L ih =>
    have hs := hc (m + (L : ℤ))
    have hc := serviceCount_nat_add S i m L 1
    simp only [Nat.cast_one, serviceCount_one_length] at hc
    rw [hc]
    push_cast
    rw [← add_assoc]
    split_ifs at hs ⊢ <;> omega

/-- The signed counter difference is the full count on every integer window. -/
theorem serviceIndex_window (S : ℤ → α) (i : α) (m : ℤ) (L : ℕ) :
    serviceIndex S i (m + (L : ℤ)) - serviceIndex S i m =
      (serviceCount S i m (L : ℤ) : ℤ) :=
  serviceCount_eq_of_counter S i (serviceIndex S i) (serviceIndex_step S i) m L

/-- Child number for a signed parent occurrence index. -/
def cyclicChild (q : ℕ) (hq : 0 < q) (n : ℤ) : Fin q :=
  ⟨(n % (q : ℤ)).toNat, by
    have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
    have hlo := Int.emod_nonneg n (ne_of_gt hqZ)
    have hhi := Int.emod_lt_of_pos n hqZ
    omega⟩

theorem cyclicChild_eq_iff (q : ℕ) (hq : 0 < q) (n : ℤ) (j : Fin q) :
    cyclicChild q hq n = j ↔ n % (q : ℤ) = (j : ℤ) := by
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  have hlo := Int.emod_nonneg n (ne_of_gt hqZ)
  rw [Fin.ext_iff]
  change (n % (q : ℤ)).toNat = j.val ↔ _
  omega

/-- Split each parent into its positive number of children in occurrence order. -/
noncomputable def cyclicSchedule (S : ℤ → α) (q : α → ℕ)
    (hq : ∀ i, 0 < q i) (t : ℤ) : Σ i, Fin (q i) :=
  ⟨S t, cyclicChild (q (S t)) (hq (S t)) (serviceIndex S (S t) t)⟩

@[simp] theorem cyclicSchedule_parent (S : ℤ → α) (q : α → ℕ)
    (hq : ∀ i, 0 < q i) (t : ℤ) :
    (cyclicSchedule S q hq t).1 = S t := rfl

/-- A one-child layer retains every service at its original slot. -/
theorem cyclicSchedule_one (S : ℤ → α) (t : ℤ) :
    cyclicSchedule S (fun _ => 1) (fun _ => by decide) t = ⟨S t,0⟩ := by
  exact congrArg (fun j : Fin 1 => (⟨S t,j⟩ : Σ _ : α, Fin 1))
    (Subsingleton.elim _ _)

theorem cyclicSchedule_eq_iff (S : ℤ → α) (q : α → ℕ)
    (hq : ∀ i, 0 < q i) (i : α) (j : Fin (q i)) (t : ℤ) :
    cyclicSchedule S q hq t = ⟨i,j⟩ ↔
      S t = i ∧ serviceIndex S i t % (q i : ℤ) = (j : ℤ) := by
  by_cases h : S t = i
  · subst i
    simp [cyclicSchedule, cyclicChild_eq_iff]
  · constructor
    · intro he
      exact False.elim (h (congrArg Sigma.fst he))
    · intro he
      exact False.elim (h he.1)

theorem cyclicSchedule_counter_step (S : ℤ → α) (q : α → ℕ)
    (hq : ∀ i, 0 < q i) (i : α) (j : Fin (q i)) (t : ℤ) :
    cyclicQuot (q i) j (serviceIndex S i (t+1)) -
        cyclicQuot (q i) j (serviceIndex S i t) =
      if cyclicSchedule S q hq t = ⟨i,j⟩ then 1 else 0 := by
  have hqZ : 0 < (q i : ℤ) := by exact_mod_cast hq i
  have hj0 : 0 ≤ (j : ℤ) := by omega
  have hjq : (j : ℤ) < (q i : ℤ) := by exact_mod_cast j.isLt
  have hs := serviceIndex_step S i t
  by_cases h : S t = i
  · have hs' : serviceIndex S i (t+1) = serviceIndex S i t + 1 := by
      simp only [if_pos h] at hs
      omega
    rw [hs', cyclicQuot_step (q := q i) (j := j) (n := serviceIndex S i t) hqZ hj0 hjq]
    simp only [cyclicSchedule_eq_iff, h, true_and]
  · have hs' : serviceIndex S i (t+1) = serviceIndex S i t := by
      simp only [if_neg h] at hs
      omega
    rw [hs']
    simp [cyclicSchedule_eq_iff, h]

/-- Exact child count; the phase at the left boundary is retained. -/
theorem cyclicSchedule_count (S : ℤ → α) (q : α → ℕ)
    (hq : ∀ i, 0 < q i) (i : α) (j : Fin (q i)) (m : ℤ) (L : ℕ) :
    cyclicQuot (q i) j (serviceIndex S i (m + (L : ℤ))) -
        cyclicQuot (q i) j (serviceIndex S i m) =
      (serviceCount (cyclicSchedule S q hq) ⟨i,j⟩ m (L : ℤ) : ℤ) :=
  serviceCount_eq_of_counter (cyclicSchedule S q hq) ⟨i,j⟩
    (fun t => cyclicQuot (q i) j (serviceIndex S i t))
    (by
      intro t
      have hs := cyclicSchedule_counter_step S q hq i j t
      by_cases h : cyclicSchedule S q hq t = ⟨i,j⟩
      · simpa only [if_pos h] using hs
      · simpa only [if_neg h] using hs) m L

/-- Each child receives at least the integer quotient of the parent count. -/
theorem cyclicSchedule_count_bound (S : ℤ → α) (q : α → ℕ)
    (hq : ∀ i, 0 < q i) (i : α) (j : Fin (q i)) (m : ℤ) (L : ℕ) :
    (serviceCount S i m (L : ℤ) : ℤ) <
      (q i : ℤ) * ((serviceCount (cyclicSchedule S q hq) ⟨i,j⟩ m (L : ℤ) : ℤ) + 1) := by
  have hqZ : 0 < (q i : ℤ) := by exact_mod_cast hq i
  have h := cyclicQuot_count_bound (q := q i) (j := j)
    (n := serviceIndex S i (m + (L : ℤ))) (m := serviceIndex S i m) hqZ
  rw [serviceIndex_window, cyclicSchedule_count] at h
  exact h

/-- A sound splitting step, with unequal children permitted by weakening. -/
theorem validRates_cyclicSchedule (S : ℤ → α) (q : α → ℕ)
    (hq : ∀ i, 0 < q i) (b : α → ℝ) (r : (Σ i, Fin (q i)) → ℝ)
    (hS : ValidRates b S)
    (hfit : ∀ i j, (q i : ℝ) * r ⟨i,j⟩ ≤ b i) :
    ValidRates r (cyclicSchedule S q hq) := by
  intro ⟨i,j⟩ m L
  have hqR : 0 < (q i : ℝ) := by exact_mod_cast hq i
  have hc := cyclicSchedule_count_bound S q hq i j m L
  have hc' : (serviceCount S i m (L : ℤ) : ℤ) + 1 ≤
      (q i : ℤ) * ((serviceCount (cyclicSchedule S q hq) ⟨i,j⟩ m (L : ℤ) : ℤ) + 1) := by
    omega
  have hcR : (serviceCount S i m (L : ℤ) : ℝ) + 1 ≤
      (q i : ℝ) * ((serviceCount (cyclicSchedule S q hq) ⟨i,j⟩ m (L : ℤ) : ℝ) + 1) := by
    exact_mod_cast hc'
  have hf := mul_le_mul_of_nonneg_left (hfit i j) (Nat.cast_nonneg (α := ℝ) L)
  have hp := hS i m L
  apply (mul_lt_mul_iff_right₀ hqR).mp
  calc
    (q i : ℝ) * ((L : ℝ) * r ⟨i,j⟩) ≤ (L : ℝ) * b i := by nlinarith [hf]
    _ < (serviceCount S i m (L : ℤ) : ℝ) + 1 := hp
    _ ≤ (q i : ℝ) * ((serviceCount (cyclicSchedule S q hq) ⟨i,j⟩ m (L : ℤ) : ℝ) + 1) := hcR

theorem SchedulableRates.cyclicSplit {b : α → ℝ} (hb : SchedulableRates b)
    (q : α → ℕ) (hq : ∀ i, 0 < q i) (r : (Σ i, Fin (q i)) → ℝ)
    (hfit : ∀ i j, (q i : ℝ) * r ⟨i,j⟩ ≤ b i) : SchedulableRates r := by
  obtain ⟨S,hS⟩ := hb
  exact ⟨cyclicSchedule S q hq, validRates_cyclicSchedule S q hq b r hS hfit⟩

/-- Splitting stated directly in the original, bilateral service windows. -/
theorem validPeriods_cyclicSchedule (S : ℤ → α) (q : α → ℕ)
    (hq : ∀ i, 0 < q i) (a : α → ℝ) (c : (Σ i, Fin (q i)) → ℝ)
    (ha : ∀ i, 0 < a i) (hc : ∀ j, 0 < c j)
    (hS : ValidPeriods a S)
    (hfit : ∀ i j, (q i : ℝ) * a i ≤ c ⟨i,j⟩) :
    ValidPeriods c (cyclicSchedule S q hq) := by
  apply (validPeriods_iff_validRates_inv hc _).mpr
  apply validRates_cyclicSchedule S q hq (fun i => (a i)⁻¹)
    (fun j => (c j)⁻¹) ((validPeriods_iff_validRates_inv ha S).mp hS)
  intro i j
  have hf : (q i : ℝ) / c ⟨i,j⟩ ≤ 1 / a i :=
    (div_le_div_iff₀ (hc ⟨i,j⟩) (ha i)).mpr (by simpa using hfit i j)
  simpa [div_eq_mul_inv] using hf

end RealPinwheel
