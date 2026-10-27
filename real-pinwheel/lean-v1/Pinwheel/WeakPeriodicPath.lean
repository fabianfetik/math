import Pinwheel.WeakPeriodic

/-! A one-pass list checker for cyclic weak-service debt certificates. -/
namespace RealPinwheel
variable {α : Type*} [DecidableEq α] [Inhabited α]

/-- One more state than letters; each recursive step consumes both lists. -/
def debtPathCheck (i : α) (p q : ℕ) : List α → List ℤ → Bool
  | [], [_] => true
  | a::w, u::v::z =>
      decide (0 ≤ u) && decide (u ≤ q) &&
      decide (u+p-(q : ℤ)*(if a=i then 1 else 0) ≤ v) &&
      debtPathCheck i p q w (v::z)
  | _, _ => false

theorem debtPathCheck_at (i : α) (p q : ℕ) (w : List α) (z : List ℤ)
    (hc : debtPathCheck i p q w z = true) (k : ℕ) (hk : k < w.length) :
    (0 ≤ z.getD k 0 ∧ z.getD k 0 ≤ q) ∧
      z.getD k 0+p-(q : ℤ)*(if w.getD k default=i then 1 else 0) ≤ z.getD (k+1) 0 := by
  induction w generalizing z k with
  | nil => simp at hk
  | cons a w ih =>
    cases z with
    | nil => simp [debtPathCheck] at hc
    | cons u zs =>
      cases zs with
      | nil => simp [debtPathCheck] at hc
      | cons v z =>
        simp only [debtPathCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
        cases k with
        | zero => simpa using hc.1
        | succ k =>
          have hs := ih (v::z) hc.2 k (by simpa using hk)
          simpa using hs

def listWord (w : List α) (s : Fin w.length) : α := w.getD s.val default

/-- Finite paths close at their first state and certify the same common word. -/
theorem weakPeriodic_of_paths (w : List α) (hw : w ≠ [])
    (p q : α → ℕ) (hq : ∀ i, 0 < q i) (z : α → List ℤ)
    (hcycle : ∀ i, (z i).getD w.length 0 = (z i).getD 0 0)
    (hc : ∀ i, debtPathCheck i (p i) (q i) w (z i) = true) :
    WeakValidRates (fun i => (p i : ℝ)/q i)
      (periodic w.length (List.length_pos_of_ne_nil hw) (listWord w)) := by
  let hP := List.length_pos_of_ne_nil hw
  apply weakPeriodic_of_debt hP (listWord w) p q hq
    (fun i s => (z i).getD s.val 0)
  · intro i s
    exact (debtPathCheck_at i (p i) (q i) w (z i) (hc i) s.val s.isLt).1.1
  · intro i s
    exact (debtPathCheck_at i (p i) (q i) w (z i) (hc i) s.val s.isLt).1.2
  · intro i s
    have hs := (debtPathCheck_at i (p i) (q i) w (z i) (hc i) s.val s.isLt).2
    change (z i).getD s.val 0 + p i - (q i : ℤ)*
      (if w.getD s.val default=i then 1 else 0) ≤ (z i).getD ((s.val+1)%w.length) 0
    by_cases hl : s.val+1 < w.length
    · rw [Nat.mod_eq_of_lt hl]
      exact hs
    · have he : s.val+1=w.length := by omega
      rw [he,Nat.mod_self]
      rw [he,hcycle i] at hs
      exact hs

end RealPinwheel
