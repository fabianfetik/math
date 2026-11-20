import CorralFormalization.EndpointProof.Matching.UniversalCore.CorePhysicalReceiver
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Budget
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Candidates

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.ActualRemainder
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [AddCommGroup G] in
/-- The independently developed raw-event role sets are the receiver's
same physical original-sample sets. -/
@[simp] theorem rawSet_zero_eq_originalTail (s : OriginalSample G) :
    rawSet s 0 = originalTailSet s := by
  ext x
  simp [rawSet,selected,sites,originalTailSet]

omit [AddCommGroup G] in
@[simp] theorem rawSet_one_eq_originalHead (s : OriginalSample G) :
    rawSet s 1 = originalHeadSet s := by
  ext x
  simp [rawSet,selected,sites,originalHeadSet]

omit [AddCommGroup G] in
@[simp] theorem rawSet_two_eq_originalColour (s : OriginalSample G) :
    rawSet s 2 = originalColourSet s := by
  ext x
  simp [rawSet,selected,sites,originalColourSet]

@[simp] theorem signedRawTarget_eq_original (s : OriginalSample G) :
    signedRawTarget s = signedTarget (originalTailSet s) (originalHeadSet s) (originalColourSet s) := by
  simp [signedRawTarget]

/-- The tagged symmetric-difference budget is literally the receiver's
six-term physical edit distance on this same sample. -/
theorem raw_taggedDistance_eq_physical (s : OriginalSample G) (X Y C : Finset G) :
    taggedDistance (signedRawTarget s) (signedTarget X Y C) =
      physicalEditDistance (originalTailSet s) (originalHeadSet s) (originalColourSet s) X Y C := by
  rw [signedRawTarget_eq_original, taggedDistance_signedTarget]

end
end EndpointMatching.UniversalCore
