import CorralFormalization.EndpointProof.Factor.FactorParameters
import CorralFormalization.EndpointProof.Router.ReservoirEvent

/-!
# Applying the paper's router ledger to the actual reservoir event

These adapters connect the real `|F|+22ℓ ≤ bn/4` budget to the proved
finite greedy installer and intermediate-port selector. They do not yet
assemble all installed primitives into the final track-indexed router.
-/

open scoped BigOperators
namespace EndpointRouter

open EndpointLayeredSample
noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem routerTrialBudget_eq_density_floor (u : ℝ) (n : ℕ) :
    routerTrialBudget u n = ⌊explicitRouterDensity u * (n : ℝ)⌋₊ := by
  unfold routerTrialBudget explicitRouterDensity
  congr 1
  ring

/-- The paper's stricter `bn/4` ledger pays the full integer `bn` budget
of the actual primitive installer. -/
theorem explicitLedger_le_installerBudget (u : ℝ) (n F ℓ : ℕ)
    (hledger : ((F + 22*ℓ : ℕ) : ℝ) ≤ explicitRouterDensity u * (n : ℝ)/4) :
    F + 21*ℓ ≤ routerTrialBudget u n := by
  rw [routerTrialBudget_eq_density_floor]
  apply Nat.le_floor
  have hb : 0 ≤ explicitRouterDensity u * (n : ℝ) := by
    unfold explicitRouterDensity
    positivity
  push_cast at hledger ⊢
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  nlinarith

/-- The same ledger leaves strictly enough sampled vertices for all
intermediate ports, once `u*n ≥ 8`. -/
theorem explicitLedger_port_slack (u : ℝ) (n F ℓ : ℕ)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hledger : ((F + 22*ℓ : ℕ) : ℝ) ≤ explicitRouterDensity u * (n : ℝ)/4)
    (hn : 8 ≤ u*(n : ℝ)) :
    (F : ℝ) + ℓ + 2 < u*(n : ℝ)/2 := by
  have hb := (explicitRouterDensity_bounds u hu hu1).2
  have hbn := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) n)
  push_cast at hledger
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  nlinarith

/-- The actual common reservoir event installs all primitives for a legal
two-layer query schedule under the paper's displayed forbidden-set ledger. -/
theorem ReservoirEvent.install_explicitLedger (u : ℝ) (ω : Bool × G → Bool)
    (h : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) ω)
    (tracks : ℕ) (queries : List (Query G)) (F external intermediate : Finset G)
    (hlegal : ∀ q ∈ queries, q.Legal)
    (htracks : (queries.map Query.arity).sum = 2*tracks)
    (hexternal : external.card ≤ 2*tracks) (hintermediate : intermediate.card ≤ tracks)
    (hledger : ((F.card + 22*tracks : ℕ) : ℝ) ≤
      explicitRouterDensity u * (Fintype.card G : ℝ)/4) :
    ∃ installed : List (Primitive G),
      List.Forall₂ (Primitive.Good (vertexReservoir ω) (colorReservoir ω)) queries installed ∧
      installed.Pairwise (fun P Q => Disjoint P.support Q.support) ∧
      (∀ P ∈ installed, Disjoint P.support (F ∪ external ∪ intermediate)) := by
  exact install_router_primitives_explicit_budget (vertexReservoir ω) (colorReservoir ω)
    (routerTrialBudget u (Fintype.card G)) tracks queries F external intermediate hlegal htracks
    hexternal hintermediate (explicitLedger_le_installerBudget u _ _ _ hledger) h.1

/-- The same sample and ledger provide actual fresh intermediate ports. -/
theorem ReservoirEvent.choose_ports_explicitLedger (u : ℝ) (ω : Bool × G → Bool)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (h : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) ω)
    (F : Finset G) (previous : G) (deltas : List G)
    (hledger : ((F.card + 22*deltas.length : ℕ) : ℝ) ≤
      explicitRouterDensity u * (Fintype.card G : ℝ)/4)
    (hn : 8 ≤ u*(Fintype.card G : ℝ)) :
    ∃ ports : List G,
      ports.length = deltas.length ∧ ports.Nodup ∧
      (∀ p ∈ ports, p ∈ vertexPool ω ∧ p ∉ F) ∧
      List.Forall₂ (fun difference delta => difference ≠ delta ∧ difference ≠ -delta)
        (EndpointFactor.edgeLabels (fun a b : G => b-a) (previous::ports)) deltas := by
  exact h.choose_ports u (routerTrialBudget u (Fintype.card G)) ω F previous deltas
    (explicitLedger_port_slack u _ _ _ hu hu1 hledger hn)

end
end EndpointRouter
