import CorralFormalization.EndpointProof.Factor.RouterBudget
import CorralFormalization.EndpointProof.Probability.LayeredSample.RouterReservoir

/-!
# The paper ledger on the same augmented sample

These are the actual installer and port-selector applications on the reserve
augmentation that also supplies exact-matching and the ordinary transitions.
-/

open scoped BigOperators Classical
namespace EndpointLayeredSample

open EndpointRouter
noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}

/-- The paper ledger pays the concrete two-layer primitive installation
inside the thinned reserves of this very sample. -/
theorem AugmentedRouterReservoirEvent.install_explicitLedger
    {u : ℝ} {s : AugmentedSample G m} (h : AugmentedRouterReservoirEvent u s)
    (tracks : ℕ) (queries : List (Query G)) (F external intermediate : Finset G)
    (hlegal : ∀ q ∈ queries, q.Legal)
    (htracks : (queries.map Query.arity).sum = 2*tracks)
    (hexternal : external.card ≤ 2*tracks) (hintermediate : intermediate.card ≤ tracks)
    (hledger : ((F.card + 22*tracks : ℕ) : ℝ) ≤
      explicitRouterDensity u * (Fintype.card G : ℝ)/4) :
    ∃ installed : List (Primitive G),
      List.Forall₂ (Primitive.Good
        {g | (thinnedReserves s).1 g = true} {g | (thinnedReserves s).2 g = true})
        queries installed ∧
      installed.Pairwise (fun P Q => Disjoint P.support Q.support) ∧
      (∀ P ∈ installed, Disjoint P.support (F ∪ external ∪ intermediate)) := by
  have h' : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) (routerBits s) := by
    simpa only [AugmentedRouterReservoirEvent, explicitSwitchBudget_eq_routerExplicitBudget] using h
  have hp := h'.install_explicitLedger u (routerBits s) tracks queries F external intermediate
    hlegal htracks hexternal hintermediate hledger
  simpa only [vertexReservoir, colorReservoir, routerBits_vertex, routerBits_colour] using hp

/-- Under the same ledger, the actual thinned vertex pool supplies the
intermediate ports once the eventual numerical threshold is met. -/
theorem AugmentedRouterReservoirEvent.choose_ports_explicitLedger
    {u : ℝ} {s : AugmentedSample G m} (h : AugmentedRouterReservoirEvent u s)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (F : Finset G) (previous : G) (deltas : List G)
    (hledger : ((F.card + 22*deltas.length : ℕ) : ℝ) ≤
      explicitRouterDensity u * (Fintype.card G : ℝ)/4)
    (hn : 8 ≤ u*(Fintype.card G : ℝ)) :
    ∃ ports : List G,
      ports.length = deltas.length ∧ ports.Nodup ∧
      (∀ p ∈ ports, p ∈ vertexPool (routerBits s) ∧ p ∉ F) ∧
      List.Forall₂ (fun difference delta => difference ≠ delta ∧ difference ≠ -delta)
        (EndpointFactor.edgeLabels (fun a b : G => b-a) (previous::ports)) deltas := by
  exact h.choose_ports F previous deltas
    (explicitLedger_port_slack u _ _ _ hu hu1 hledger hn)

end
end EndpointLayeredSample
