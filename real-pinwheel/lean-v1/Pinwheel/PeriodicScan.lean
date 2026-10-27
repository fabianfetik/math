import Pinwheel.Periodic

namespace RealPinwheel

/-- The Boolean occurrence test used by the prefix scan. -/
def occurrenceBit (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5)
    (i : Fin 5) (s : Fin P) (k : ℕ) : Bool :=
  decide (w (phaseIndex P hP s k) = i)

lemma cyclicCount_succ (P : ℕ) (hP : 0 < P)
    (w : Fin P → Fin 5) (i : Fin 5) (s : Fin P) (k : ℕ) :
    cyclicCount P hP w i s (k + 1) =
      cyclicCount P hP w i s k +
        if occurrenceBit P hP w i s k = true then 1 else 0 := by
  rw [cyclicCount, List.range_succ, List.countP_append]
  simp [occurrenceBit]

/--
The prefix checker carries the running occurrence count in its last argument.
With `fuel = P`, `offset = 0`, and `count = 0`, each slot is inspected once.
The residual test is made for positive proper prefixes, and the zero-fuel case
checks the mean at the full period.
-/
def prefixCheck (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5)
    (c : RateCap) (i : Fin 5) (s : Fin P) :
    ℕ → ℕ → ℕ → Bool
  | 0, _offset, count => decide (MeanCap c P count)
  | fuel + 1, offset, count =>
      let next := count + if occurrenceBit P hP w i s offset then 1 else 0
      (if offset + 1 < P then decide (ResidualCap c (offset + 1) next) else true) &&
        prefixCheck P hP w c i s fuel (offset + 1) next

/-- A proposition-level unfolding of `prefixCheck`, used only for soundness. -/
def prefixSpec (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5)
    (c : RateCap) (i : Fin 5) (s : Fin P) :
    ℕ → ℕ → ℕ → Prop
  | 0, _offset, count => MeanCap c P count
  | fuel + 1, offset, count =>
      let next := count + if occurrenceBit P hP w i s offset then 1 else 0
      (if offset + 1 < P then ResidualCap c (offset + 1) next else True) ∧
        prefixSpec P hP w c i s fuel (offset + 1) next

lemma prefixCheck_eq_true_iff (P : ℕ) (hP : 0 < P)
    (w : Fin P → Fin 5) (c : RateCap) (i : Fin 5) (s : Fin P)
    (fuel offset count : ℕ) :
    prefixCheck P hP w c i s fuel offset count = true ↔
      prefixSpec P hP w c i s fuel offset count := by
  induction fuel generalizing offset count with
  | zero => simp [prefixCheck, prefixSpec]
  | succ fuel ih =>
      by_cases hlt : offset + 1 < P <;>
        simp [prefixCheck, prefixSpec, ResidualCap, ih, hlt]

lemma prefixSpec_sound (P : ℕ) (hP : 0 < P)
    (w : Fin P → Fin 5) (c : RateCap) (i : Fin 5) (s : Fin P)
    (fuel offset count : ℕ)
    (hcount : count = cyclicCount P hP w i s offset)
    (hspec : prefixSpec P hP w c i s fuel offset count) :
    (∀ h : ℕ, offset < h → h < offset + fuel → h < P →
      ResidualCap c h (cyclicCount P hP w i s h)) ∧
      (offset + fuel = P → MeanCap c P (cyclicCount P hP w i s P)) := by
  induction fuel generalizing offset count with
  | zero =>
      constructor
      · intro h hpos hlt hP'
        omega
      · intro hperiod
        have hoff : offset = P := by omega
        change MeanCap c P count at hspec
        rw [hcount, hoff] at hspec
        exact hspec
  | succ fuel ih =>
      let next := count + if occurrenceBit P hP w i s offset then 1 else 0
      change (if offset + 1 < P then ResidualCap c (offset + 1) next else True) ∧
        prefixSpec P hP w c i s fuel (offset + 1) next at hspec
      have hnext : next = cyclicCount P hP w i s (offset + 1) := by
        dsimp [next]
        rw [cyclicCount_succ, hcount]
      have hrest := ih (offset := offset + 1) (count := next) hnext hspec.2
      constructor
      · intro h hpos hlt hP'
        by_cases heq : h = offset + 1
        · subst h
          have hcur : ResidualCap c (offset + 1) next := by
            simpa [hP'] using hspec.1
          rw [hnext] at hcur
          exact hcur
        · have hgt : offset + 1 < h := by omega
          apply hrest.1 h hgt
          · omega
          · exact hP'
      · intro hperiod
        apply hrest.2
        omega

/-- Soundness for one fixed task and one fixed phase. -/
theorem prefixCheck_to_phaseCertificate
    (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5)
    (c : RateCap) (i : Fin 5) (s : Fin P)
    (hcheck : prefixCheck P hP w c i s P 0 0 = true) :
    MeanCap c P (cyclicCount P hP w i s P) ∧
      ∀ h : Fin P, 0 < h.val →
        ResidualCap c h.val (cyclicCount P hP w i s h.val) := by
  have hspec : prefixSpec P hP w c i s P 0 0 := by
    apply (prefixCheck_eq_true_iff P hP w c i s P 0 0).mp
    exact hcheck
  have hzero : (0 : ℕ) = cyclicCount P hP w i s 0 := by
    simp [cyclicCount]
  have hs := prefixSpec_sound P hP w c i s P 0 0 hzero hspec
  constructor
  · apply hs.2
    omega
  · intro h hh
    apply hs.1 h.val
    · exact hh
    · omega
    · exact h.isLt

/-- Assemble the phase-local scan certificates into `WordCertificate`. -/
theorem wordCertificate_of_prefixChecks
    (P : ℕ) (hP : 0 < P) (w : Fin P → Fin 5)
    (caps : Fin 5 → RateCap)
    (hcheck : ∀ (i : Fin 5) (s : Fin P),
      prefixCheck P hP w (caps i) i s P 0 0 = true) :
    WordCertificate P hP w caps := by
  intro i s
  exact prefixCheck_to_phaseCertificate P hP w (caps i) i s (hcheck i s)

end RealPinwheel
