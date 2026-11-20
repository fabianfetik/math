import CorralFormalization.EndpointProof.Matching.Fractional.Fourier.Convolution
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.PhysicalCoordinates
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Joint

open scoped Classical BigOperators Matrix ComplexConjugate
namespace EndpointMatching.Fractional.Fourier
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointMatching.Fractional.RobustWeights
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

def centeredRawMask (q : ℝ) (s : OriginalSample G) (r : Fin 3) (g : G) : ℂ :=
  ((rawBit s r g - q : ℝ) : ℂ)

def centeredSignedMask (q : ℝ) (s : OriginalSample G) (r : Fin 3) (g : G) : ℂ :=
  ((setBit (signedSets (rawTarget s) r) g - q : ℝ) : ℂ)

@[simp] theorem coefficient_centeredRawMask (q : ℝ) (s : OriginalSample G)
    (r : Fin 3) (χ : AddChar G ℂ) :
    coefficient (centeredRawMask q s r) χ = fourierError q s r χ := rfl

/-- Signing the first and third roles is exactly reflection of the same
physical sample, never a fresh sample or an extra assumption. -/
theorem centeredSignedMask_eq (q : ℝ) (s : OriginalSample G) (r : Fin 3) (g : G) :
    centeredSignedMask q s r g = centeredRawMask q s r (signCoordinate r g) := by
  unfold centeredSignedMask centeredRawMask
  rw [signedSets_bit]
  congr 1
  simp [rawTarget,rawBit_eq,setBit]
  rfl

/-- Every signed raw role inherits exactly the raw-event Fourier bound. -/
theorem GoodFourier.signed_coefficient_le {q ε : ℝ} {s : OriginalSample G}
    (h : GoodFourier q ε s) (r : Fin 3) (χ : AddChar G ℂ) :
    ‖coefficient (centeredSignedMask q s r) χ‖ ≤ ε*(Fintype.card G : ℝ) := by
  have hs : centeredSignedMask q s r =
      fun g => centeredRawMask q s r (signCoordinate r g) := by
    funext g
    exact centeredSignedMask_eq q s r g
  rw [hs]
  by_cases hr : r = 1
  · subst r
    simpa only [signCoordinate, ↓reduceIte, coefficient_centeredRawMask] using h 1 χ
  · simp only [signCoordinate, hr, ↓reduceIte]
    rw [coefficient_reflection, coefficient_centeredRawMask]
    exact h r χ⁻¹

/-- All three full signed raw convolution blocks on the original sample
have L² operator norm at most εn. -/
theorem GoodFourier.signed_convolution_L2_le {q ε : ℝ} (hε : 0 ≤ ε)
    {s : OriginalSample G} (h : GoodFourier q ε s) (r : Fin 3) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := G)
      (convolutionMatrix (centeredSignedMask q s r))‖ ≤ ε*(Fintype.card G : ℝ) := by
  apply convolution_L2_operator_norm_le _ _ (by positivity)
  exact GoodFourier.signed_coefficient_le h r

end
end EndpointMatching.Fractional.Fourier
