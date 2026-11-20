import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.ActualSquare
import CorralFormalization.EndpointProof.Matching.UniversalCore.RawSampleAlignment

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.RobustWeights
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The standalone robust fractional supplier in the paper's physical
convention. Zero endpoint coordinates and coincident endpoints remain
allowed; only the zero colour is excluded. The target and F are quantified
after the original sample. -/
def PhysicalRobustFractionalEvent (q : ℝ) (s : OriginalSample G) : Prop :=
  ∀ (X Y C : Finset G), X.card = Y.card → X.card = C.card → (0:G) ∉ C →
    (physicalEditDistance (originalTailSet s) (originalHeadSet s) (originalColourSet s) X Y C : ℝ) ≤
      rho q*(Fintype.card G : ℝ) →
    ∀ (F : Finset (Finset (Vertex G))),
      (∀ z, ((banAt F z).card : ℝ) ≤ beta q*(Fintype.card G : ℝ)) →
      ∃ w : AllowedEdge (signedTarget X Y C) F → ℝ,
        (∀ e, 1/(2*(q*(X.card : ℝ))) ≤ w e ∧ w e ≤ 3/(2*(q*(X.card : ℝ)))) ∧
        ∀ v : signedTarget X Y C, (∑ e, if v ∈ localEdge e then w e else 0) = 1

/-- The written robust fractional supplier is reduced to the same explicit
raw L² estimate; there is no disjoint-endpoints or checksum premise. -/
theorem physicalRobustFractionalEvent_of_raw_and_L2
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) (s : OriginalSample G)
    (hraw : fractionalRawEvent q s)
    (hL2 : ∀ (W : Finset (Vertex G)) (hW : Balanced W),
      l2OperatorNorm (actualRawMatrix W hW (signedSets (rawTarget s)) q) ≤
        2 * epsilon q * (Fintype.card G : ℝ)) :
    PhysicalRobustFractionalEvent q s := by
  have hsmall := actualRawSmallSquare_of_l2 hq0 hq1 hraw hL2
  intro X Y C hXY hXC hC hd F hban
  let W := signedTarget X Y C
  have hW : Balanced W := signedTarget_balanced hXY hXC
  have hzero : (2,(0:G)) ∉ W := by
    intro hz
    have hmem : (2, -(0:G)) ∈ signedTarget X Y C := by simpa [W] using hz
    exact hC ((signedTarget_color_mem X Y C 0).mp hmem)
  have hdist : (taggedDistance (signedRawTarget s) W : ℝ) ≤ rho q*(Fintype.card G : ℝ) := by
    dsimp [W]
    rw [raw_taggedDistance_eq_physical]
    exact hd
  have hcard : (slice W 0).card = X.card := by
    dsimp [W]
    rw [signedTarget_slice_tail, Finset.card_image_of_injective]
    exact fun a b h => neg_injective (congrArg Prod.snd h)
  obtain ⟨w,hw,hload⟩ := actual_interval_weights_of_raw_and_smallSquare q hq0 hq1 s hraw hsmall
    F hban W hW hzero hdist
  refine ⟨w,?_,hload⟩
  simpa only [hcard] using hw

end
end EndpointMatching.UniversalCore
