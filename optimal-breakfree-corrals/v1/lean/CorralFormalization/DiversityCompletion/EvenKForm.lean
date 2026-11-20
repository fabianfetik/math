import CorralFormalization.DiversityCompletion.EvenCountLower

/-! Explicitly recover the manuscript's odd-k parameter range and
exponents from the constructive m-parameter theorem. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral

theorem odd_k_parameters (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    ∃ m : ℕ, 1 ≤ m ∧ k = 2*m+1 := by
  obtain ⟨m, hm⟩ := ho
  refine ⟨m, ?_, ?_⟩ <;> omega

theorem evenSwitchFamily_odd_k (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    ∃ m : ℕ, 1 ≤ m ∧ k = 2*m+1 ∧ height m = 2*k ∧ order m = 2*(2*k)-1 ∧
      ∃ F : (NonzeroPhase m → EvenLetter m) → CorralRows (height m) (order m),
        (Finset.univ.image (fun t => physicalCorralFamily m (F t))).card = 2^((k-1)^2) ∧
        (asymmetricOrbitIntersections (fun t => physicalCorralFamily m (F t))).card =
          (2^((k-1)^2) - 2^(((k-1)^2)/2))/2 := by
  obtain ⟨m, hm, heq⟩ := odd_k_parameters k hk ho
  have hk1 : k-1 = 2*m := by omega
  have hp : (k-1)^2 = 4*m*m := by rw [hk1]; ring
  have hp2 : (k-1)^2/2 = 2*m*m := by
    rw [hp]
    have he : 4*m*m = (2*m*m)*2 := by ring
    rw [he]
    simp
  have hheight : height m = 2*k := by rw [heq]; unfold height; ring
  have horder : order m = 2*(2*k)-1 := by unfold order; omega
  obtain ⟨F, hcount, horbits⟩ := evenSwitchFamily_explicit_corral_family m hm
  refine ⟨m, hm, heq, hheight, horder, F, ?_, ?_⟩
  · simpa only [hp] using hcount
  · rw [hp2, hp]
    exact horbits

end CorralFormalization.EvenSwitches
