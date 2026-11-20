import CorralFormalization.DiversityCompletion.SeedSeparation
import CorralFormalization.DiversityCompletion.EvenAMarker

namespace CorralFormalization.DiversitySymmetry

open CorralFormalization.PhysicalCorral
open CorralFormalization.EvenSwitches

/-- The switch construction and the original even construction use the
same actual physical clock, for every m. -/
theorem switchClock_eq_evenConstructionClock (m : ℕ) :
    clock m = evenConstructionClock (2 * m + 1) := by
  have hk : 1 ≤ 2 * m + 1 := by omega
  have horder : 4 * (2 * m + 1) - 1 = order m := by
    unfold order
    have h : 4 * (2 * m + 1) = 8 * m + 4 := by ring
    omega
  have hh : 2 * (2 * m + 1) = height m := by unfold height; ring
  rw [evenConstructionClock_eq_sum (2 * m + 1) hk, evenConstructionGapWord_sum (2 * m + 1) hk,
    horder, hh]
  rfl

/-- No motion of the concrete seed equals any independent motion of any
actual D4-A row, stated on the original even construction's physical clock.
The A marker is supplied by its proved explicit construction, not assumed. -/
theorem evenConstructionSeed_A_motion_ne (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (f g : Motion (evenConstructionClock (2 * m + 1))) :
    f.onRow (evenConstructionSeed (2 * m + 1)) ≠
      g.onRow (physicalSites (evenConstructionClock (2 * m + 1)) (rowA m a)) := by
  have hA := rowA_physical_marker m hm a
  rw [switchClock_eq_evenConstructionClock m] at hA
  apply evenSwitchFamily_seed_separation m hm _ (Or.inl _) f g
  simpa only [order, height] using hA

/-- The literal concrete rows on the switch construction's actual clock.
This consumes no row validity, gap inventory, marker or separation input.
The domain includes m=1 and every permitted bit choice. -/
theorem actual_seed_A_motion_ne (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (f g : Motion (clock m)) :
    f.onRow (physicalSites (clock m) (evenConstructionRawPrefixSet (2 * m + 1))) ≠
      g.onRow (physicalSites (clock m) (rowA m a)) := by
  revert f g
  rw [switchClock_eq_evenConstructionClock m]
  intro f g
  exact evenConstructionSeed_A_motion_ne m hm a f g

end CorralFormalization.DiversitySymmetry
