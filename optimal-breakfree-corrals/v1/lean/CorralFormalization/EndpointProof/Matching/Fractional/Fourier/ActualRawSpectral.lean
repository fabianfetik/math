import CorralFormalization.EndpointProof.Matching.Fractional.Fourier.ThreeBlocks
import CorralFormalization.EndpointProof.Matching.Fractional.Fourier.RawMasks
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.SpectralSquare

/-!
# The actual raw three-role matrix has L² operator norm at most `2 ε n`

Every block is the restriction of a full convolution on the same signed raw
mask. Rows use their actual signed coordinates and columns their negatives.
These maps are injective. The target need not retain raw Fourier accuracy:
restriction is an L² contraction for every later actual target.
-/

open scoped Classical BigOperators Matrix

namespace EndpointMatching.Fractional.Fourier

open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore EndpointMatching.Fractional.RobustWeights

noncomputable section

set_option maxHeartbeats 1500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

section GenericCoordinates

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The exact convolution representation of an ordered off-diagonal block
for arbitrary signed coordinates, including all signs. -/
theorem offDiagonalBlock_complex_eq_convolution_submatrix
    (coord : (Fin 3 × I) → G) (s : OriginalSample G) (q : ℝ)
    (r t : Fin 3) (hrt : r ≠ t) :
    complexify (roleBlock (offDiagonal coord (signedSets (rawTarget s)) q) r t) =
      (convolutionMatrix (centeredSignedMask q s (thirdRole r t))).submatrix
        (fun i => coord (r, i)) (fun j => -coord (t, j)) := by
  ext i j
  simp only [complexify, roleBlock, offDiagonal, hrt, if_false,
    requiredCoordinate, Matrix.submatrix_apply, convolutionMatrix, centeredSignedMask]
  congr 2
  abel_nf

/-- Each injected off-diagonal block inherits the full raw Fourier bound. -/
theorem GoodFourier.offDiagonalBlock_L2_le {q ε : ℝ} (hε : 0 ≤ ε)
    {s : OriginalSample G} (h : GoodFourier q ε s)
    (coord : (Fin 3 × I) → G)
    (hcoord : ∀ r, Function.Injective (fun i => coord (r, i)))
    (r t : Fin 3) (hrt : r ≠ t) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (roleBlock (offDiagonal coord (signedSets (rawTarget s)) q) r t)‖ ≤
        ε * (Fintype.card G : ℝ) := by
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (complexify (roleBlock (offDiagonal coord (signedSets (rawTarget s)) q) r t))‖ :=
      real_L2_operator_norm_le_complex _
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((convolutionMatrix (centeredSignedMask q s (thirdRole r t))).submatrix
          (fun i => coord (r, i)) (fun j => -coord (t, j)))‖ := by
      rw [offDiagonalBlock_complex_eq_convolution_submatrix coord s q r t hrt]
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (convolutionMatrix (centeredSignedMask q s (thirdRole r t)))‖ := by
      apply submatrix_L2_operator_norm_le
      · exact hcoord r
      · intro i j hij
        exact hcoord t (neg_injective hij)
    _ ≤ _ := GoodFourier.signed_convolution_L2_le hε h (thirdRole r t)

/-- Generic injected three-role raw matrices pay exactly two block bounds. -/
theorem GoodFourier.offDiagonal_L2_le {q ε : ℝ} (hε : 0 ≤ ε)
    {s : OriginalSample G} (h : GoodFourier q ε s)
    (coord : (Fin 3 × I) → G)
    (hcoord : ∀ r, Function.Injective (fun i => coord (r, i))) :
    l2OperatorNorm (offDiagonal coord (signedSets (rawTarget s)) q) ≤
      2 * ε * (Fintype.card G : ℝ) := by
  rw [l2OperatorNorm_eq_clm]
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (offDiagonal coord (signedSets (rawTarget s)) q)‖ ≤
      2 * (ε * (Fintype.card G : ℝ)) := by
    apply three_role_L2_operator_norm_le _ _ (by positivity)
    · intro r
      ext i j
      simp [roleBlock, offDiagonal]
    · exact fun r t hrt => GoodFourier.offDiagonalBlock_L2_le hε h coord hcoord r t hrt
  nlinarith

end GenericCoordinates

/-- The actual chart gives the exact convolution restriction, without a
parallel surrogate matrix or target Fourier premise. -/
theorem actualRawBlock_complex_eq_convolution_submatrix
    (W : Finset (Vertex G)) (hW : Balanced W) (s : OriginalSample G) (q : ℝ)
    (r t : Fin 3) (hrt : r ≠ t) :
    complexify (roleBlock (actualRawMatrix W hW (signedSets (rawTarget s)) q) r t) =
      (convolutionMatrix (centeredSignedMask q s (thirdRole r t))).submatrix
        (fun i => actualCoordinate W hW (r, i))
        (fun j => -actualCoordinate W hW (t, j)) :=
  offDiagonalBlock_complex_eq_convolution_submatrix (actualCoordinate W hW) s q r t hrt

/-- The actual off-diagonal block bound, for every later balanced inventory. -/
theorem GoodFourier.actualRawBlock_L2_le {q ε : ℝ} (hε : 0 ≤ ε)
    {s : OriginalSample G} (h : GoodFourier q ε s)
    (W : Finset (Vertex G)) (hW : Balanced W) (r t : Fin 3) (hrt : r ≠ t) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (roleBlock (actualRawMatrix W hW (signedSets (rawTarget s)) q) r t)‖ ≤
        ε * (Fintype.card G : ℝ) :=
  GoodFourier.offDiagonalBlock_L2_le hε h (actualCoordinate W hW)
    (actualCoordinate_injective W hW) r t hrt

/-- The full actual raw matrix has precisely the required `2 ε n` bound.
No order, distance, colour-zero or nonempty-target hypothesis is required. -/
theorem GoodFourier.actualRawMatrix_L2_le {q ε : ℝ} (hε : 0 ≤ ε)
    {s : OriginalSample G} (h : GoodFourier q ε s)
    (W : Finset (Vertex G)) (hW : Balanced W) :
    l2OperatorNorm (actualRawMatrix W hW (signedSets (rawTarget s)) q) ≤
      2 * ε * (Fintype.card G : ℝ) :=
  GoodFourier.offDiagonal_L2_le hε h (actualCoordinate W hW) (actualCoordinate_injective W hW)

/-- The literal original-sample event provides the complete adaptive
spectral supplier, with the manuscript's `epsilon = q⁴/100000`. -/
theorem fractionalRawEvent_actualRawMatrix_L2_le {q : ℝ} {s : OriginalSample G}
    (h : fractionalRawEvent q s) :
    ∀ (W : Finset (Vertex G)) (hW : Balanced W),
      l2OperatorNorm (actualRawMatrix W hW (signedSets (rawTarget s)) q) ≤
        2 * epsilon q * (Fintype.card G : ℝ) := by
  intro W hW
  exact GoodFourier.actualRawMatrix_L2_le (by unfold epsilon; positivity) h.1 W hW

end
end EndpointMatching.Fractional.Fourier
