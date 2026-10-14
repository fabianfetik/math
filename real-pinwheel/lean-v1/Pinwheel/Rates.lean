import Pinwheel.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace RealPinwheel

variable {α β : Type*}

theorem serviceCount_mono_length (S : ℤ → α) (i : α) (m : ℤ)
    {L K : ℤ} (h : L ≤ K) : serviceCount S i m L ≤ serviceCount S i m K := by
  classical
  unfold serviceCount windowCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_Ico] at ht ⊢
  exact ⟨⟨ht.1.1, lt_of_lt_of_le ht.1.2 (by omega)⟩, ht.2⟩

theorem ValidRates.mono {r q : α → ℝ} {S : ℤ → α}
    (hq : ValidRates q S) (hrq : ∀ i, r i ≤ q i) : ValidRates r S := by
  intro i m L
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hrq i) (Nat.cast_nonneg L))
    (hq i m L)

theorem SchedulableRates.mono {r q : α → ℝ}
    (hq : SchedulableRates q) (hrq : ∀ i, r i ≤ q i) : SchedulableRates r := by
  obtain ⟨S, hS⟩ := hq
  exact ⟨S, hS.mono hrq⟩

theorem serviceCount_relabel (e : α ≃ β) (S : ℤ → α) (i : α) (m L : ℤ) :
    serviceCount (fun t => e (S t)) (e i) m L = serviceCount S i m L := by
  classical
  unfold serviceCount windowCount
  apply congrArg Finset.card
  ext t
  simp

theorem SchedulableRates.relabel (e : α ≃ β) {r : β → ℝ}
    (h : SchedulableRates (fun i => r (e i))) : SchedulableRates r := by
  obtain ⟨S, hS⟩ := h
  refine ⟨fun t => e (S t), ?_⟩
  intro i m L
  have hc := serviceCount_relabel e S (e.symm i) m (L : ℤ)
  simp only [e.apply_symm_apply] at hc
  rw [hc]
  simpa only [e.apply_symm_apply] using hS (e.symm i) m L

theorem validPeriods_iff_validRates_inv {a : α → ℝ} (ha : ∀ i, 0 < a i)
    (S : ℤ → α) : ValidPeriods a S ↔ ValidRates (fun i => (a i)⁻¹) S := by
  constructor
  · intro hp i m L
    by_contra hn
    have hle : (serviceCount S i m (L : ℤ) : ℝ) + 1 ≤ (L : ℝ) * (a i)⁻¹ :=
      le_of_not_gt hn
    let ell := serviceCount S i m (L : ℤ) + 1
    have hell : 0 < ell := Nat.succ_pos _
    have hmul : (ell : ℝ) * a i ≤ (L : ℝ) := by
      apply (le_div_iff₀ (ha i)).mp
      simpa [ell, div_eq_mul_inv] using hle
    have hceil : ⌈(ell : ℝ) * a i⌉ ≤ (L : ℤ) := by
      apply Int.ceil_le.mpr
      exact_mod_cast hmul
    have hcount := (hp i m ell hell).trans (serviceCount_mono_length S i m hceil)
    dsimp [ell] at hcount
    omega
  · intro hr i m ell hell
    let K : ℤ := ⌈(ell : ℝ) * a i⌉
    have hprod : 0 ≤ (ell : ℝ) * a i := mul_nonneg (Nat.cast_nonneg ell) (ha i).le
    have hK : 0 ≤ K := Int.ceil_nonneg hprod
    have hKcast : (ell : ℝ) * a i ≤ (K : ℝ) := Int.le_ceil _
    have hmul : (ell : ℝ) ≤ (K : ℝ) * (a i)⁻¹ := by
      apply (le_div_iff₀ (ha i)).mpr at hKcast
      simpa [div_eq_mul_inv] using hKcast
    have hbound := hr i m K.toNat
    have hnat : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hK
    have hnatR : (K.toNat : ℝ) = (K : ℝ) := by exact_mod_cast hnat
    rw [hnat, hnatR] at hbound
    have hlt := lt_of_le_of_lt hmul hbound
    have hn : ell < serviceCount S i m K + 1 := by exact_mod_cast hlt
    exact Nat.le_of_lt_succ hn

theorem validRates_iff_validPeriods_inv {r : α → ℝ} (hr : ∀ i, 0 < r i)
    (S : ℤ → α) : ValidRates r S ↔ ValidPeriods (fun i => (r i)⁻¹) S := by
  simpa only [inv_inv] using
    (validPeriods_iff_validRates_inv (fun i => inv_pos.mpr (hr i)) S).symm

theorem schedulableRates_of_enumerations {r : α → ℝ} (hr : ∀ i, 0 < r i)
    (S : ℤ → α) (t : α → ℤ → ℤ)
    (hc : ∀ i, CompleteEnumeration (fun x => S x = i) (t i))
    (hs : ∀ (i : α) (ell : ℕ), 0 < ell → ∀ j : ℤ,
      t i (j + (ell : ℤ)) - t i j ≤ ⌈(ell : ℝ) * (r i)⁻¹⌉) :
    SchedulableRates r := by
  refine ⟨S, (validRates_iff_validPeriods_inv hr S).mpr ?_⟩
  intro i m ell hell
  exact (all_windows_span_iff_real_period (hc i) ((r i)⁻¹)).mpr (hs i) ell hell m

end RealPinwheel
