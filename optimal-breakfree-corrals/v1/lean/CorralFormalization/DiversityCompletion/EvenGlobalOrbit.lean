import CorralFormalization.DiversityCompletion.EvenLabelCount
import CorralFormalization.DiversityCompletion.FixedSeedEquivariance

/-! Assemble the exact §6 orbit count from local support data, a fixed
seed, and the actual local action of the common reflection. No global
family injectivity or global equivariance is supplied as an input. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral

theorem fixedSeed_physical_orbit_formula (m : ℕ) (hm : 1 ≤ m)
    (D : FixedSeedSupport (ZMod (clock m)) (NonzeroPhase m) (EvenLetter m))
    (R : Finset (ZMod (clock m))) (C : ZMod (clock m))
    (marker : Finset (ZMod (clock m)) → Prop)
    (hrigid : RigidRow R) (hmarker : marker R)
    (hinvariant : ∀ f : Motion (clock m), ∀ S, marker (f.onRow S) ↔ marker S)
    (hseed : R ∈ D.fixedRows)
    (hfixed_marked : ∀ S ∈ D.fixedRows, marker S → S = R ∨ S = (Motion.reflection C).onRow R)
    (hlocal_unmarked : ∀ j a S, S ∈ D.letters j a → ¬ marker S)
    (hfixed_reflection : (Motion.reflection C).onFamily D.fixedRows = D.fixedRows)
    (hletter_reflection : ∀ j a, (Motion.reflection C).onFamily (D.letters j a) =
      D.letters (negatePhase m j) (flipLetter a)) :
    (asymmetricOrbitIntersections D.assembleFixed).card = (2^(4*m*m) - 2^(2*m*m))/2 := by
  apply evenLabels_physical_orbit_formula m hm D.assembleFixed D.assembleFixed_injective
    R C marker hrigid hmarker hinvariant
  · intro t
    exact Finset.mem_union_left _ hseed
  · intro t S hS hmS
    rcases Finset.mem_union.mp hS with hf | hl
    · exact hfixed_marked S hf hmS
    · obtain ⟨j, hj⟩ := (D.toSupportAlphabet.assemble_mem t S).mp hl
      exact False.elim (hlocal_unmarked j (t j) S hj hmS)
  · intro t
    change (Motion.reflection C).onFamily (D.assembleFixed t) =
      D.assembleFixed (fun j => flipLetter (t (negatePhase m j)))
    exact D.assembleFixed_motion
      (Motion.reflection C) (negatePhase m) (negatePhase_involutive m)
      flipLetter hfixed_reflection hletter_reflection t

end CorralFormalization.EvenSwitches
