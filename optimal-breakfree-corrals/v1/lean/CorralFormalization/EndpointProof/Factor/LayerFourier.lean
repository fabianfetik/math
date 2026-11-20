import CorralFormalization.EndpointProof.Probability.LayeredSample.TransitionFourier

/-!
# One role interface for vertex and colour transition layers

The layer-sample Fourier theorem is already proved for both signed vertex
and colour roles. This file packages those checked cases behind the same
role index used to apply ordinary-transition to arbitrary later triples.
-/

open scoped BigOperators Classical
namespace EndpointLayeredSample

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}

/-- Unified role index for choosing any later signed triple of layers. -/
def signedRoleSet (s : Sample G m) (role : RawRole m) (negative : Bool) : Finset G :=
  match role with
  | Sum.inl v => signedVertexSet s v negative
  | Sum.inr c => signedColourSet s c negative

theorem TransitionFourierEvent.roleFourierGood {d : Densities m} {η : ℝ} {s : Sample G m}
    (h : TransitionFourierEvent d η s) (role : RawRole m) (negative : Bool) :
    EndpointTransitions.FourierGood (signedRoleSet s role negative) (roleDensity d role) η := by
  cases role with
  | inl v => exact h.1 v negative
  | inr c => exact h.2 c negative

end
end EndpointLayeredSample
