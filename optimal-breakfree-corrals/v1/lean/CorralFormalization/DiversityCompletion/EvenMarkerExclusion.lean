import CorralFormalization.DiversityCompletion.EvenAlphabetValidity
import CorralFormalization.DiversityCompletion.EvenAMarker
import CorralFormalization.DiversityCompletion.EvenBMarker
import CorralFormalization.DiversityCompletion.SeedBSeparation

/-! The actual seed marker occurs in neither row of any translated
alphabet letter. This is stronger than merely separating the seed by
isometry, and supplies the local marker condition for the orbit count. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral DiversitySymmetry

def seedMarker (m : ℕ) (S : Finset (ZMod (clock m))) : Prop :=
  HasGapNeighborPair S (order m) {1, height m - 2}

def seedPhysical (m : ℕ) : Finset (ZMod (clock m)) :=
  physicalSites (clock m) (evenConstructionRawPrefixSet (2*m+1))

theorem seedPhysical_has_marker (m : ℕ) (hm : 1 ≤ m) : seedMarker m (seedPhysical m) := by
  unfold seedMarker seedPhysical
  rw [switchClock_eq_evenConstructionClock m]
  simpa [evenConstructionSeed, order, height, Nat.add_assoc] using evenSwitchFamily_seed_marker m hm

theorem seedPhysical_rigid (m : ℕ) (hm : 1 ≤ m) : RigidRow (seedPhysical m) := by
  unfold seedPhysical
  rw [switchClock_eq_evenConstructionClock m]
  exact evenSwitchFamily_seed_rigid m hm

theorem seedMarker_motion_iff (m : ℕ) (f : Motion (clock m)) (S : Finset (ZMod (clock m))) :
    seedMarker m (f.onRow S) ↔ seedMarker m S := by
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  exact hasGapNeighborPair_motion_iff f S _ _

theorem seedPair_ne_A (m : ℕ) (hm : 1 ≤ m) :
    ({1, height m - 2} : Finset ℕ) ≠ {height m, height m + 1} := by
  intro he
  have hx : (1 : ℕ) ∈ ({1, height m - 2} : Finset ℕ) := by simp
  rw [he] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  unfold height at hx
  rcases hx with hx | hx <;> omega

theorem seedPair_ne_B (m : ℕ) (hm : 1 ≤ m) :
    ({1, height m - 2} : Finset ℕ) ≠ {height m - 2, height m + 3} := by
  intro he
  have hx : (1 : ℕ) ∈ ({1, height m - 2} : Finset ℕ) := by simp
  rw [he] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  unfold height at hx
  rcases hx with hx | hx <;> omega

theorem rowA_not_seedMarker (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    ¬ seedMarker m (physicalSites (clock m) (rowA m a)) := by
  intro h
  exact seedPair_ne_A m hm ((rowA_physical_marker_iff m hm a _).mp h)

theorem rowB_not_seedMarker (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    ¬ seedMarker m (physicalSites (clock m) (rowB m a)) := by
  intro h
  exact seedPair_ne_B m hm ((rowB_physical_marker_iff m hm a _).mp h)

theorem baseLetter_not_seedMarker (m : ℕ) (hm : 1 ≤ m) (a : Choices m)
    (S : Finset (ZMod (clock m))) (hS : S ∈ baseLetter m a) : ¬ seedMarker m S := by
  simp only [baseLetter, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl
  · exact rowA_not_seedMarker m hm a
  · exact rowB_not_seedMarker m hm a

theorem alphabetLetter_not_seedMarker (m : ℕ) (hm : 1 ≤ m) (ab : Choices m × Bool)
    (S : Finset (ZMod (clock m))) (hS : S ∈ alphabetLetter m ab) : ¬ seedMarker m S := by
  rcases ab with ⟨a, b⟩
  cases b with
  | false => exact baseLetter_not_seedMarker m hm a S hS
  | true =>
    change S ∈ reflectedLetter m a at hS
    unfold reflectedLetter Motion.onFamily at hS
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hS
    intro h
    exact baseLetter_not_seedMarker m hm a R hR
      ((seedMarker_motion_iff m _ R).mp h)

theorem translatedLetter_not_seedMarker (m : ℕ) (hm : 1 ≤ m) (j : ℕ) (ab : Choices m × Bool)
    (S : Finset (ZMod (clock m))) (hS : S ∈ translatedLetter m j ab) : ¬ seedMarker m S := by
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hS
  intro h
  exact alphabetLetter_not_seedMarker m hm ab R hR
    ((seedMarker_motion_iff m _ R).mp h)

end CorralFormalization.EvenSwitches
