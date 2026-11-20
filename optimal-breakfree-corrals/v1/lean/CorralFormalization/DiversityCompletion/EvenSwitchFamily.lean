import CorralFormalization.DiversityCompletion.EvenSwitchFamilyOrbits
import CorralFormalization.DiversityCompletion.EvenConcreteCorral

/-! The actual optimal CorralRows family and its exact asymmetric physical
orbit count, with no extra hypotheses beyond the manuscript's range. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral

theorem evenSwitchFamily_explicit_corral_family (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : (NonzeroPhase m → EvenLetter m) → CorralRows (height m) (order m),
      (Finset.univ.image (fun t => physicalCorralFamily m (F t))).card = 2^(4*m*m) ∧
      (asymmetricOrbitIntersections (fun t => physicalCorralFamily m (F t))).card =
        (2^(4*m*m) - 2^(2*m*m))/2 := by
  obtain ⟨F, hF⟩ := concreteData_realization m hm
  have heq : (fun t => physicalCorralFamily m (F t)) = (concreteData m hm).assembleFixed :=
    funext hF
  refine ⟨F, ?_, ?_⟩
  · rw [heq]
    exact concreteData_physical_count m hm
  · rw [heq]
    exact evenSwitchFamily_assembled_orbit_count m hm

end CorralFormalization.EvenSwitches
