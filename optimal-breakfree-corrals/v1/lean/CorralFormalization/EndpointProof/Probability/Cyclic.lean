import CorralFormalization.EndpointProof.Probability.SelectorsAndAffineFlows
import Mathlib.Data.ZMod.Basic

/-!
The literal cyclic-group specialization used by the corral manuscript.
This imports the joint selector/affine-candidate result, not the full
endpoint theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Classical

namespace EndpointFullProduct

open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

/-- The concrete selectors and all admissible affine paired-cover candidates
are jointly supplied in the original cyclic model, uniformly for every
sufficiently large odd modulus. The later six-root layout/cover bridge is
not part of this statement. -/
theorem cyclic_selectors_and_affine_event
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n] (hodd : Odd n) (hn : max N 2000 ≤ n),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample (ZMod n) | ¬ OriginalAdmitsSelectorsAndAffineFlow
          (by simpa only [ZMod.card] using hodd) (by simpa only [ZMod.card] using (show 1000 ≤ n by omega))
          (selectorExternalBudget (p q) n) (flowBudget (tau q) n) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * n) := by
  obtain ⟨N,hN⟩ := original_selectors_and_affine_flow_probability q hq0 hq1
  refine ⟨N, ?_⟩
  intro n _ hodd hn
  have hodd' : Odd (Fintype.card (ZMod n)) := by simpa only [ZMod.card] using hodd
  have hn' : max N 2000 ≤ Fintype.card (ZMod n) := by simpa only [ZMod.card] using hn
  simpa only [ZMod.card] using hN (ZMod n) hodd' hn'

end
end EndpointFullProduct
