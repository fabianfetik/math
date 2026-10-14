import Pinwheel.PrimitiveReflected
import Pinwheel.WeakSeven

/-! Linear-size periodic certificates for closed weak service caps.
The witness is a bounded integer debt super-solution on the actual word. -/
namespace RealPinwheel
open PrimitivePromotion

/-- A bounded debt super-solution pays every weak window. -/
theorem weak_window_of_debt {α : Type*} (S : ℤ → α) (i : α)
    (p q : ℕ) (hq : 0 < q) (Z : ℤ → ℤ)
    (hlo : ∀ t, 0 ≤ Z t) (hhi : ∀ t, Z t ≤ q)
    (hstep : ∀ t, Z t + p - (q : ℤ) * serviceBit S i t ≤ Z (t+1)) :
    ∀ (t : ℤ) (L : ℕ),
      Int.ceil ((L : ℝ) * ((p : ℝ) / q)) - 1 ≤
        (serviceCount S i t (L : ℤ) : ℤ) := by
  have htel (t : ℤ) (L : ℕ) : deficit S i p q t L ≤ Z (t+L)-Z t := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [deficit_add, deficit_one]
      have hs := hstep (t+L)
      push_cast
      have he : t + ((L : ℤ) + 1) = t + L + 1 := by omega
      rw [he]
      omega
  intro t L
  have hd : deficit S i p q t L ≤ q := by
    have := htel t L
    have := hlo t
    have := hhi (t+L)
    omega
  have hdR : (p : ℝ) * L - (q : ℝ) * (serviceCount S i t (L : ℤ) : ℝ) ≤ q := by
    unfold deficit at hd
    exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb : (L : ℝ) * ((p : ℝ) / q) ≤ (serviceCount S i t (L : ℤ) : ℝ)+1 := by
    rw [← mul_div_assoc, div_le_iff₀ hqR]
    nlinarith
  have hc : Int.ceil ((L : ℝ) * ((p : ℝ) / q)) ≤
      (serviceCount S i t (L : ℤ) : ℤ)+1 := by
    apply Int.ceil_le.mpr
    simpa using hb
  omega

def nextPhase {P : ℕ} (hP : 0 < P) (s : Fin P) : Fin P :=
  ⟨(s.val+1)%P, Nat.mod_lt _ hP⟩

theorem phase_add_one (P : ℕ) (hP : 0 < P) (t : ℤ) :
    phase P hP (t+1) = nextPhase hP (phase P hP t) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  simp only [phase_val_eq_emod]
  change (t+1) % (P : ℤ) = (((phase P hP t).val+1)%P : ℕ)
  push_cast
  rw [phase_val_eq_emod]
  exact Int.add_emod t 1 (P : ℤ) |>.trans (by simp)

/-- Check one finite cyclic debt witness for each label. All witnesses share
one literal word, so their conclusions describe one common schedule. -/
theorem weakPeriodic_of_debt {α : Type*} [DecidableEq α]
    {P : ℕ} (hP : 0 < P) (w : Fin P → α)
    (p q : α → ℕ) (hq : ∀ i, 0 < q i) (Z : α → Fin P → ℤ)
    (hlo : ∀ i s, 0 ≤ Z i s) (hhi : ∀ i s, Z i s ≤ q i)
    (hstep : ∀ i s, Z i s + p i - (q i : ℤ) * (if w s = i then 1 else 0) ≤
      Z i (nextPhase hP s)) :
    WeakValidRates (fun i => (p i : ℝ) / q i) (periodic P hP w) := by
  intro i
  apply weak_window_of_debt (periodic P hP w) i (p i) (q i) (hq i)
    (fun t => Z i (phase P hP t))
  · exact fun t => hlo i _
  · exact fun t => hhi i _
  · intro t
    rw [phase_add_one]
    have hs := hstep i (phase P hP t)
    by_cases he : w (phase P hP t) = i
    · simpa [serviceBit, periodic, he] using hs
    · simpa [serviceBit, periodic, he] using hs

/-- Boolean checks avoid building a large dependent decision-proof tree. -/
def cyclicDebtCheck {α : Type*} [DecidableEq α] {P : ℕ} (hP : 0 < P)
    (w : Fin P → α) (i : α) (p q : ℕ) (Z : Fin P → ℤ) : Bool :=
  (List.range P).all fun k => if hk : k < P then
    decide (0 ≤ Z ⟨k,hk⟩) && decide (Z ⟨k,hk⟩ ≤ q) &&
      decide (Z ⟨k,hk⟩ + p - (q : ℤ)*(if w ⟨k,hk⟩ = i then 1 else 0) ≤
        Z (nextPhase hP ⟨k,hk⟩))
    else false

theorem cyclicDebtCheck_sound {α : Type*} [DecidableEq α] {P : ℕ} (hP : 0 < P)
    (w : Fin P → α) (i : α) (p q : ℕ) (Z : Fin P → ℤ)
    (hc : cyclicDebtCheck hP w i p q Z = true) (s : Fin P) :
    (0 ≤ Z s ∧ Z s ≤ q) ∧
      Z s + p - (q : ℤ)*(if w s = i then 1 else 0) ≤ Z (nextPhase hP s) := by
  have hs := List.all_eq_true.mp hc s.val (List.mem_range.mpr s.isLt)
  simpa [s.isLt] using hs

theorem weakPeriodic_of_debtChecks {α : Type*} [DecidableEq α]
    {P : ℕ} (hP : 0 < P) (w : Fin P → α)
    (p q : α → ℕ) (hq : ∀ i, 0 < q i) (Z : α → Fin P → ℤ)
    (hc : ∀ i, cyclicDebtCheck hP w i (p i) (q i) (Z i) = true) :
    WeakValidRates (fun i => (p i : ℝ) / q i) (periodic P hP w) := by
  have hs := fun i s => cyclicDebtCheck_sound hP w i (p i) (q i) (Z i) (hc i) s
  exact weakPeriodic_of_debt hP w p q hq Z
    (fun i s => (hs i s).1.1) (fun i s => (hs i s).1.2) (fun i s => (hs i s).2)

end RealPinwheel
