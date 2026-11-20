import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.RawSquare
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.ActualMatrix
import CorralFormalization.EndpointProof.Matching.Fractional.ActualWeightsFromSmallSquare

/-! The actual raw Euclidean operator estimate supplies the small-square
input.  All scaling, row bounds and target-size inequalities are proved. -/

open scoped Classical BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

open EndpointOriginalReservoir EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore EndpointMatching.Fractional.ActualRemainder
noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The remaining analytic premise is solely the genuine raw L2 estimate
on the actual target restriction; no inverse or weights are assumed. -/
theorem fractionalRawEvent_actual_normalized_square_of_l2
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    {s : OriginalSample G} (hraw : fractionalRawEvent q s)
    (W : Finset (Vertex G)) (hW : Balanced W) [Nonempty (CommonIndex W)]
    (hdist : (taggedDistance (signedRawTarget s) W : ℝ) ≤ EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ))
    (hL2 : l2OperatorNorm (actualRawMatrix W hW (signedSets (rawTarget s)) q) ≤
      2 * epsilon q * (Fintype.card G : ℝ)) :
    ‖normalizeError (q * (Fintype.card (CommonIndex W) : ℝ))
        (actualRawMatrix W hW (signedSets (rawTarget s)) q) *
      normalizeError (q * (Fintype.card (CommonIndex W) : ℝ))
        (actualRawMatrix W hW (signedSets (rawTarget s)) q)‖ ≤ 33 / 100000 := by
  have hmpos : (0 : ℝ) < Fintype.card (CommonIndex W) := by exact_mod_cast Fintype.card_pos
  have hd : 0 < q * (Fintype.card (CommonIndex W) : ℝ) := mul_pos hq0 hmpos
  have hed : editDistance (physicalSets W) (rawTarget s) ≤ EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ) := by
    rw [physicalSets_taggedDistance]
    exact hdist
  have hs := fractionalRawEvent_target_size_bounds hq0 hq1 hraw (physicalSets W) hed (0 : Fin 3)
  rw [physicalSets_balanced_card W hW] at hs
  have hscale : q ^ 2 * (Fintype.card G : ℝ) / 2 ≤
      q * (Fintype.card (CommonIndex W) : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hs.1 hq0.le]
  have hmn : (Fintype.card (CommonIndex W) : ℝ) ≤ Fintype.card G := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun i => actualCoordinate W hW (0,i)) (actualCoordinate_injective W hW 0)
  exact offDiagonal_normalized_square_le (actualCoordinate W hW) (signedSets (rawTarget s))
    q (Fintype.card G : ℝ) (q * (Fintype.card (CommonIndex W) : ℝ)) hq0.le (by linarith)
    (Nat.cast_nonneg _) hmn hd hscale hL2

/-- Uniform actual raw L2 estimates discharge the precise small-square
property consumed by the complete actual robust supplier.  Nonemptiness is
derived from the original raw event and the paid target distance. -/
theorem actualRawSmallSquare_of_l2 {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    {s : OriginalSample G} (hraw : fractionalRawEvent q s)
    (hL2 : ∀ (W : Finset (Vertex G)) (hW : Balanced W),
      l2OperatorNorm (actualRawMatrix W hW (signedSets (rawTarget s)) q) ≤
        2 * epsilon q * (Fintype.card G : ℝ)) :
    ActualRawSmallSquare q s := by
  intro W hW _ hdist
  have hed : editDistance (physicalSets W) (rawTarget s) ≤
      EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ) := by
    rw [physicalSets_taggedDistance]
    exact hdist
  have hs := fractionalRawEvent_target_size_bounds hq0 hq1 hraw (physicalSets W) hed (0 : Fin 3)
  rw [physicalSets_balanced_card W hW] at hs
  have hnpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hmpos : (0 : ℝ) < Fintype.card (CommonIndex W) := by nlinarith
  have hmNat : 0 < Fintype.card (CommonIndex W) := by exact_mod_cast hmpos
  haveI : Nonempty (CommonIndex W) := Fintype.card_pos_iff.mp hmNat
  exact fractionalRawEvent_actual_normalized_square_of_l2 hq0 hq1 hraw W hW hdist (hL2 W hW)

end
end EndpointMatching.Fractional.RobustWeights
