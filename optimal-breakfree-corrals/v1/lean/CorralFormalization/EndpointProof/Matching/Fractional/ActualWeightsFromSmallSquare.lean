import CorralFormalization.EndpointProof.Matching.Fractional.ActualRobust
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.ActualMatrix
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.RawAdapter

open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder EndpointMatching.Fractional.RobustWeights
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The one remaining spectral inequality on the actual raw matrix, uniformly
after every admissible target. This is a numerical matrix property, not a
fractional- or integral-matching conclusion. -/
def ActualRawSmallSquare (q : ℝ) (s : OriginalSample G) : Prop :=
  ∀ (W : Finset (Vertex G)) (hW : Balanced W),
    (2,(0:G)) ∉ W →
    (taggedDistance (signedRawTarget s) W : ℝ) ≤ rho q*(Fintype.card G : ℝ) →
    ‖normalizeError (q*(Fintype.card (CommonIndex W) : ℝ))
        (actualRawMatrix W hW (signedSets (rawTarget s)) q) *
      normalizeError (q*(Fintype.card (CommonIndex W) : ℝ))
        (actualRawMatrix W hW (signedSets (rawTarget s)) q)‖ ≤ 33/100000

/-- The proved raw event and the small-square estimate yield interval-bounded
fractional-perfect weights on every balanced nearby actual inventory with
nonzero colours, including inventories with a zero endpoint and arbitrary
admissible later edge bans. -/
theorem actual_interval_weights_of_raw_and_smallSquare
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) (s : OriginalSample G)
    (hraw : fractionalRawEvent q s) (hsquare : ActualRawSmallSquare q s)
    (F : Finset (Finset (Vertex G)))
    (hban : ∀ z, ((banAt F z).card : ℝ) ≤ beta q * (Fintype.card G : ℝ))
    (W : Finset (Vertex G)) (hW : Balanced W) (hC : (2,(0:G)) ∉ W)
    (hdist : (taggedDistance (signedRawTarget s) W : ℝ) ≤ rho q*(Fintype.card G : ℝ)) :
    ∃ w : AllowedEdge W F → ℝ,
      (∀ e, 1/(2*(q*((slice W 0).card : ℝ))) ≤ w e ∧
        w e ≤ 3/(2*(q*((slice W 0).card : ℝ)))) ∧
      ∀ v : W, (∑ e, if v ∈ localEdge e then w e else 0) = 1 := by
  obtain ⟨hlo,hhi⟩ := fractionalRawEvent_tagged_size_bounds hq0 hq1 hraw W hdist
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hm : 0 < ((slice W 0).card : ℝ) := by nlinarith
  have hmNat : 0 < (slice W 0).card := by exact_mod_cast hm
  have hmCard : Fintype.card (CommonIndex W) = (slice W 0).card := by simp [CommonIndex, PartIndex]
  have hmCardPos : 0 < Fintype.card (CommonIndex W) := by rw [hmCard]; exact hmNat
  have : Nonempty (CommonIndex W) := Fintype.card_pos_iff.mp hmCardPos
  let m : ℝ := Fintype.card (CommonIndex W)
  let d : ℝ := q*m
  let X : ℝ := q^2 * Fintype.card G
  let R := signedSets (rawTarget s)
  have hmr : m = (slice W 0).card := by dsimp [m]; exact_mod_cast hmCard
  have hd : 0 < d := by dsimp [d]; rw [hmr]; positivity
  have hX : X ≤ 2*d := by
    dsimp [X,d]
    rw [hmr]
    have h := mul_le_mul_of_nonneg_left hlo (le_of_lt hq0)
    nlinarith
  have hdecomp := actual_gram_decomposition W hW R q
  have hdiag := fractionalRawEvent_actualDegreeMatrix_norm_le hq0 hq1 hraw W hW hC hdist
  have hedit := fractionalRawEvent_actualEditMatrix_norm_le W hW hdist
  have hrawnorm := fractionalRawEvent_actualRawMatrix_norm_le hq0.le hq1 hraw W hW hC hdist
  have hdegree := fractionalRawEvent_actual_hdegree hq0 hq1 hraw W hW hC hdist
  have hban' : ∀ v : W, (actualBannedDegree F v.val : ℝ) ≤ X/2000 := by
    intro v
    have h := hban v.val
    dsimp [actualBannedDegree, banAt, beta, X] at *
    nlinarith
  have hsq := hsquare W hW hC hdist
  obtain ⟨w,hw,hload⟩ := actual_interval_weights_of_raw_matrix_estimates W hW F d X hd hX
    (actualDegreeMatrix W hW d) (actualEditMatrix W hW R) (actualRawMatrix W hW R q)
    (by simpa only [d,m,R] using hdecomp)
    (by simpa only [d,m,X,mul_assoc] using hdiag)
    (by simpa only [X,R,mul_assoc] using hedit)
    (by simpa only [X,R,mul_assoc] using hrawnorm)
    (by simpa only [d,m,R] using hsq)
    (by simpa only [d,m,X,mul_assoc] using hdegree) hban'
  refine ⟨w,?_,hload⟩
  simpa only [d,hmr] using hw

/-- The nonzero-residual interface consumed by the exact receiver is a
specialization of the stronger nonzero-colour statement above. -/
theorem actualFractionalWeights_of_raw_and_smallSquare
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) (s : OriginalSample G)
    (hraw : fractionalRawEvent q s) (hsquare : ActualRawSmallSquare q s)
    (F : Finset (Finset (Vertex G)))
    (hban : ∀ z, ((banAt F z).card : ℝ) ≤ beta q * (Fintype.card G : ℝ)) :
    ActualFractionalWeights (signedRawTarget s) F q (rho q*(Fintype.card G : ℝ)) := by
  intro W hW hnonzero hdist
  have hC : (2,(0:G)) ∉ W := by
    intro h
    exact hnonzero (2,0) h rfl
  exact actual_interval_weights_of_raw_and_smallSquare q hq0 hq1 s hraw hsquare F hban W hW hC hdist

end
end EndpointMatching.UniversalCore
