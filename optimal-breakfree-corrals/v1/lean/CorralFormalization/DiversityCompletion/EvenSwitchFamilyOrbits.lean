import CorralFormalization.DiversityCompletion.EvenConcreteAssembly
import CorralFormalization.DiversityCompletion.EvenActualOrbit

/-! The literal assembled §6 family meets the asserted number of
asymmetric physical orbits, with no geometric or marker hypotheses. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral EvenSupportPartition

theorem evenSwitchFamily_assembled_orbit_count (m : ℕ) (hm : 1 ≤ m) :
    (asymmetricOrbitIntersections (concreteData m hm).assembleFixed).card =
      (2^(4*m*m) - 2^(2*m*m))/2 := by
  apply concreteFixedSeed_orbit_formula m hm (concreteData m hm)
  · rfl
  · intro j a
    rfl

end CorralFormalization.EvenSwitches
