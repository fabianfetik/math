import CorralFormalization.DiversityCompletion.SeedASeparation
import CorralFormalization.DiversityCompletion.EvenBMarker

namespace CorralFormalization.DiversitySymmetry

open CorralFormalization.PhysicalCorral
open CorralFormalization.EvenSwitches

/-- The actual D7-B row is not physically isometric to the actual seed,
for any allowable bit choice; no marker assumption is supplied. -/
theorem evenConstructionSeed_B_motion_ne (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (f g : Motion (evenConstructionClock (2*m+1))) :
    f.onRow (evenConstructionSeed (2*m+1)) ≠
      g.onRow (physicalSites (evenConstructionClock (2*m+1)) (rowB m a)) := by
  have hB := rowB_physical_marker m hm a
  rw [switchClock_eq_evenConstructionClock m] at hB
  apply evenSwitchFamily_seed_separation m hm _ (Or.inr _) f g
  simpa [order, height, Nat.add_assoc] using hB

theorem actual_seed_B_motion_ne (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (f g : Motion (clock m)) :
    f.onRow (physicalSites (clock m) (evenConstructionRawPrefixSet (2*m+1))) ≠
      g.onRow (physicalSites (clock m) (rowB m a)) := by
  revert f g
  rw [switchClock_eq_evenConstructionClock m]
  intro f g
  exact evenConstructionSeed_B_motion_ne m hm a f g

end CorralFormalization.DiversitySymmetry
