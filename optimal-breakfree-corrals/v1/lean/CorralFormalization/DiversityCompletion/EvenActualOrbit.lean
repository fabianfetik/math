import CorralFormalization.DiversityCompletion.EvenGlobalOrbit
import CorralFormalization.DiversityCompletion.EvenTranslationReflection

/-! Once the concrete support structure is supplied, every other input
to the physical orbit count is discharged by the literal seed and alphabet. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral DiversitySymmetry

theorem concreteFixedSeed_orbit_formula (m : ℕ) (hm : 1 ≤ m)
    (D : FixedSeedSupport (ZMod (clock m)) (NonzeroPhase m) (EvenLetter m))
    (hfixed : D.fixedRows =
      {seedPhysical m, (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (clock m))).onRow (seedPhysical m)})
    (hletters : ∀ j a, D.letters j a = translatedLetter m j.val.val a) :
    (asymmetricOrbitIntersections D.assembleFixed).card = (2^(4*m*m) - 2^(2*m*m))/2 := by
  let C : ZMod (clock m) := (((height m)^2-1 : ℕ) : ZMod (clock m))
  apply fixedSeed_physical_orbit_formula m hm D (seedPhysical m) C (seedMarker m)
    (seedPhysical_rigid m hm) (seedPhysical_has_marker m hm) (seedMarker_motion_iff m)
  · rw [hfixed]
    simp
  · intro S hS _
    rw [hfixed] at hS
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hS
  · intro j a S hS
    rw [hletters] at hS
    exact translatedLetter_not_seedMarker m hm j.val.val a S hS
  · rw [hfixed]
    dsimp [C]
    simp only [Motion.onFamily, Finset.image_insert, Finset.image_singleton]
    rw [Motion.reflection_onRow_involutive]
    exact Finset.pair_comm _ _
  · intro j a
    rw [hletters, hletters]
    change (Motion.reflection C).onFamily (translatedLetter m j.val.val a) =
      translatedLetter m (-j.val).val (flipLetter a)
    exact translatedLetter_reflection m j.val a

end CorralFormalization.EvenSwitches
