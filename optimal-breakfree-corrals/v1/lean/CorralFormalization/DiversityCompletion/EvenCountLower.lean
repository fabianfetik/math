import CorralFormalization.DiversityCompletion.EvenSwitchFamily

namespace CorralFormalization.EvenSwitches

/-- Integer form of the numerical lower bound following Theorem 3.
For h=4m+2 its exponent is h²/4-h-1 = 4m²-2. -/
theorem evenSwitchFamily_numerical_lower (m : ℕ) (hm : 1 ≤ m) :
    2^(4*m*m-2) ≤ (2^(4*m*m) - 2^(2*m*m))/2 := by
  let a := 4*m*m
  let b := 2*m*m
  have ha : 2 ≤ a := by dsimp [a]; nlinarith
  have hab' : b+1 ≤ a := by dsimp [a, b]; nlinarith
  have hab : b ≤ a-1 := by omega
  have hle : (2 : ℕ)^b ≤ 2^(a-1) := Nat.pow_le_pow_right (by omega) hab
  have hfirst : (2 : ℕ)^a = 2^(a-1)*2 := by
    calc
      _ = 2^((a-1)+1) := by congr 1; omega
      _ = _ := by rw [pow_succ]
  have hsecond : (2 : ℕ)^(a-1) = 2^(a-2)*2 := by
    calc
      _ = 2^((a-2)+1) := by congr 1; omega
      _ = _ := by rw [pow_succ]
  change 2^(a-2) ≤ (2^a - 2^b)/2
  omega

theorem evenSwitchFamily_explicit_corral_lower (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : (PhysicalCorral.NonzeroPhase m → EvenLetter m) → CorralRows (height m) (order m),
      2^(4*m*m-2) ≤
        (PhysicalCorral.asymmetricOrbitIntersections (fun t => physicalCorralFamily m (F t))).card := by
  obtain ⟨F, _, hcount⟩ := evenSwitchFamily_explicit_corral_family m hm
  refine ⟨F, ?_⟩
  rw [hcount]
  exact evenSwitchFamily_numerical_lower m hm

end CorralFormalization.EvenSwitches
