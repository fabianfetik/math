import CorralFormalization.EndpointProof.Factor.Adapter
import CorralFormalization.Results.ConnectorPrefixFloor

/-!
A uniform factor-supplier interface for the actual endpoint proposition.

This file does not construct the required factors. It makes their exact
quantified existence an explicit premise and proves the deterministic
connection from that premise to the existing endpoint and diversity types.
-/

open scoped BigOperators

namespace EndpointFactor

open CorralFormalization.LatinCompletion.TerraceCompletion

/-- The actual finite factor system, its target endpoints, and its exact
vertex and colour inventories. Its existence is not proved by this file. -/
def FactorSupply {n : ℕ} [NeZero n] (W D : Finset (ZMod n))
    (x y : ZMod n) : Prop :=
  ∃ (m : ℕ) (F : FactorSystem (fun a b : ZMod n => b - a) (Fin m) (Fin m)),
    F.initial = x ∧ F.terminal = y ∧
      (∀ v, F.vertexInventory (fun a b : ZMod n => b - a) v ↔ v ∈ W) ∧
      (∀ d, F.colorInventory (fun a b : ZMod n => b - a) d ↔ d ∈ D)

theorem endpointPathClaim_of_factorSupply {n : ℕ} [NeZero n]
    (W D : Finset (ZMod n)) (x y : ZMod n) (H : FactorSupply W D x y) :
    EndpointPathClaim W D x y := by
  obtain ⟨m, F, hx, hy, hW, hD⟩ := H
  have hp := F.endpointPathClaim W D hW hD
  simpa only [hx, hy] using hp

/-- Exact quantifier order of the cyclic endpoint proposition, with a
concrete factor-system supplier in place of the path conclusion. -/
def UniformFactorSupply : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
    ∀ (n : ℕ) [NeZero n], Odd n → n0 ≤ n →
      ∀ (W D : Finset (ZMod n)) (x y : ZMod n),
        (n : ℝ) - ε0 * (n : ℝ) ≤ (W.card : ℝ) →
        x ∈ W → y ∈ W → x ≠ y → 0 ∉ D →
        D.card + 1 = W.card → (∑ z ∈ D, z) = y - x → FactorSupply W D x y

/-- A genuine uniform factor-system supplier would discharge the project's
exact endpoint hypothesis. The supplier remains an explicit input. -/
theorem oddCyclicEndpointCompletion_of_uniformFactorSupply (H : UniformFactorSupply) :
    OddCyclicRainbowEndpointCompletion := by
  obtain ⟨ε0, hε0, n0, h⟩ := H
  refine ⟨ε0, hε0, n0, ?_⟩
  intro n inst hodd hn W D x y hsize hx hy hxy hz hcard hsum
  exact endpointPathClaim_of_factorSupply W D x y
    (h n hodd hn W D x y hsize hx hy hxy hz hcard hsum)

/-- The paper's exact-floor finite lower bound, conditional on the explicit
uniform existence of suitable factor systems. -/
theorem factorSupply_floor_total_lower (H : UniformFactorSupply) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ) / 100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          CorralLatinTailMarker.latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤
            CorralFormalization.PhysicalCensus.A_h h (hh0.trans hh) := by
  exact oddCyclicEndpointCompletion_floor_total_lower (oddCyclicEndpointCompletion_of_uniformFactorSupply H)

end EndpointFactor
