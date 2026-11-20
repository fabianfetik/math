import CorralFormalization.DiversityCompletion.EvenMarkerExclusion
import CorralFormalization.DiversityCompletion.EvenLabelCount
import CorralFormalization.DiversityCompletion.CarrierEvenSupport

/-! The actual translated alphabet letters transform by j ↦ −j and the
proved Bool flip under the physical reflection x ↦ C−x. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral DiversitySymmetry EvenSupportPartition

theorem explicitPeriod_eq_switchPeriod (m : ℕ) :
    evenConstructionPeriod (2*m+1) = 2*order m := by
  unfold evenConstructionPeriod order
  omega

theorem translatedPeriod_neg (m : ℕ) (j : ZMod (2*m+1)) :
    ((2*order m*(-j).val : ℕ) : ZMod (clock m)) =
      -((2*order m*j.val : ℕ) : ZMod (clock m)) := by
  let : NeZero (2*m+1) := ⟨by omega⟩
  have h := map_neg (periodStride (2*m+1)) j
  rw [periodStride_val, periodStride_val, explicitPeriod_eq_switchPeriod,
    ← switchClock_eq_evenConstructionClock] at h
  exact h

theorem translatedLetter_reflection (m : ℕ) (j : ZMod (2*m+1)) (ab : EvenLetter m) :
    (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (clock m))).onFamily
        (translatedLetter m j.val ab) =
      translatedLetter m (-j).val (flipLetter ab) := by
  let c : ZMod (clock m) := (((height m)^2-1 : ℕ) : ZMod (clock m))
  let d : ZMod (clock m) := ((2*order m*j.val : ℕ) : ZMod (clock m))
  let e : ZMod (clock m) := ((2*order m*(-j).val : ℕ) : ZMod (clock m))
  have he : e = -d := translatedPeriod_neg m j
  have hcompose : (Motion.reflection c).compose (.rotation d) =
      (Motion.rotation e).compose (.reflection c) := by
    rw [he]
    simp only [Motion.compose]
    congr 1
    ring
  calc
    _ = ((Motion.reflection c).compose (.rotation d)).onFamily (alphabetLetter m ab) :=
      (Motion.onFamily_compose _ _ _).symm
    _ = ((Motion.rotation e).compose (.reflection c)).onFamily (alphabetLetter m ab) := by rw [hcompose]
    _ = (Motion.rotation e).onFamily ((Motion.reflection c).onFamily (alphabetLetter m ab)) :=
      Motion.onFamily_compose _ _ _
    _ = _ := by
      rw [alphabetLetter_reflection]
      rfl

end CorralFormalization.EvenSwitches
