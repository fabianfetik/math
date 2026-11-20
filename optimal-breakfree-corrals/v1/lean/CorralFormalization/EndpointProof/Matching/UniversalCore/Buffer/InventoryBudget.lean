import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.CoreConnection
import CorralFormalization.EndpointProof.Probability.SelectorSlack
import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality.PermutationExistenceTheorem
import CorralFormalization.EndpointProof.Matching.CoreCapacityReceiver

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointFullProduct
open EndpointMatching.AbsorptionAssembly
open CorralFormalization.EndpointProof.RateBudget
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The actual Q pair inventory's full numerical inverse support costs at
most two numerical coordinates per listed pair. -/
theorem available_inventory_support_card_le (ω : FullSample G) (U : Finset G) :
    let Q := availablePairInventory (ReservoirVertex ω true) U
    (support ((Finset.univ.biUnion Q).biUnion id)).card ≤
      2 * ∑ p : Fin 3, (Q p).card := by
  let Q := availablePairInventory (ReservoirVertex ω true) U
  let T := (Finset.univ : Finset (Fin 3)).biUnion Q
  have hlegal := availablePairInventory_legal (ReservoirVertex ω true)
    (pairReservoir_of_reservoirVertex ω true) U
  have hone : ∀ S ∈ T, (support S).card ≤ 2 := by
    intro S hS
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hS
    exact legalPair_support_card_le (hlegal p S hp)
  have hT : T.card ≤ ∑ p : Fin 3, (Q p).card := Finset.card_biUnion_le
  change (support (T.biUnion id)).card ≤ _
  rw [support_biUnion]
  calc
    _ ≤ ∑ S ∈ T, (support S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ T, 2 := Finset.sum_le_sum hone
    _ = 2 * T.card := by simp [Nat.mul_comm]
    _ ≤ 2 * ∑ p : Fin 3, (Q p).card := Nat.mul_le_mul_left 2 hT

/-- The exact selector installation cost is bounded by the total number
of Q-pairs and the numerical exclusion size. -/
theorem available_inventory_selector_cost_le (ω : FullSample G) (U : Finset G) (K : ℕ) :
    let Q := availablePairInventory (ReservoirVertex ω true) U
    2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
      ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
        1724 * ((Q p).card - K)) ≤
      2 * U.card + 5176 * ∑ p : Fin 3, (Q p).card := by
  let Q := availablePairInventory (ReservoirVertex ω true) U
  have hsup := available_inventory_support_card_le ω U
  change (support ((Finset.univ.biUnion Q).biUnion id)).card ≤
    2 * ∑ p : Fin 3, (Q p).card at hsup
  have hunion := Finset.card_union_le U (support ((Finset.univ.biUnion Q).biUnion id))
  have hterm : (∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
        1724 * ((Q p).card - K))) ≤
      ∑ p : Fin 3, 5172 * (Q p).card := by
    apply Finset.sum_le_sum
    intro p _
    omega
  have hsum : (∑ p : Fin 3, 5172 * (Q p).card) =
      5172 * ∑ p : Fin 3, (Q p).card := by rw [Finset.mul_sum]
  rw [hsum] at hterm
  change 2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
    ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
      1724 * ((Q p).card - K)) ≤ 2 * U.card + 5176 * ∑ p : Fin 3, (Q p).card
  omega

/-- Under the paper's actual τ/p separation, the Q-inventory upper bounds
pay every P-selector support query, including the floor of its budget. -/
theorem selector_budget_of_inventory_upper (ω : FullSample G) (U : Finset G)
    (τ p : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3)
    (hτp : τ ≤ p^4 / 10^30)
    (hU : U.card ≤ quadraticCoreCapacity τ (Fintype.card G))
    (hQ : ∀ part : Fin 3,
      ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ≤
        τ * (Fintype.card G : ℝ)) :
    let Q := availablePairInventory (ReservoirVertex ω true) U
    2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
      ∑ part : Fin 3, (2 * (2 * (862 * ((Q part).card - paddingQuota τ (Fintype.card G)))) +
        1724 * ((Q part).card - paddingQuota τ (Fintype.card G))) ≤
      selectorExternalBudget p (Fintype.card G) := by
  let n : ℝ := Fintype.card G
  let Q := availablePairInventory (ReservoirVertex ω true) U
  let K := paddingQuota τ (Fintype.card G)
  let cost : ℕ := 2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
    ∑ part : Fin 3, (2 * (2 * (862 * ((Q part).card - K))) + 1724 * ((Q part).card - K))
  apply (le_selectorExternalBudget_iff p (Fintype.card G) cost).2
  have hcostNat := available_inventory_selector_cost_le ω U K
  have hcost : (cost : ℝ) ≤ 2 * U.card + 5176 * ∑ part : Fin 3, ((Q part).card : ℝ) := by
    exact_mod_cast hcostNat
  have hQsum : (∑ part : Fin 3, ((Q part).card : ℝ)) ≤ 3 * τ * n := by
    calc
      _ ≤ ∑ _part : Fin 3, τ * n := Finset.sum_le_sum (fun part _ => hQ part)
      _ = _ := by simp [n]; ring
  have hcap : (quadraticCoreCapacity τ (Fintype.card G) : ℝ) ≤
      (1 / 10^6 : ℝ) * τ^2 * n := by
    unfold quadraticCoreCapacity
    exact Nat.floor_le (by positivity)
  have hu : (U.card : ℝ) ≤ quadraticCoreCapacity τ (Fintype.card G) := by exact_mod_cast hU
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have ht : τ^2 * n ≤ τ * n / 3 := by
    have hx : 0 ≤ ((1 / 3 : ℝ) - τ) * τ * n := by positivity
    nlinarith
  have htp : τ * n ≤ (p^4 / 10^30) * n := mul_le_mul_of_nonneg_right hτp hn
  have hp4 : 0 ≤ p^4 * n := by positivity
  nlinarith

/-- The degree-16 core's explicit cardinality expression is bounded by
864 pairs per part, hence by 2592 τn under the pair-availability upper counts. -/
theorem core_card_of_inventory_upper (ω : FullSample G) (U : Finset G) (K : ℕ)
    (τ : ℝ) (A : Finset (Vertex G))
    (hA : A.card ≤ (∑ p : Fin 3, 862 *
        ((availablePairInventory (ReservoirVertex ω true) U p).card - K)) +
      ∑ p : Fin 3, 2 * (availablePairInventory (ReservoirVertex ω true) U p).card)
    (hQ : ∀ p : Fin 3,
      ((availablePairInventory (ReservoirVertex ω true) U p).card : ℝ) ≤
        τ * (Fintype.card G : ℝ)) :
    (A.card : ℝ) ≤ 2592 * τ * (Fintype.card G : ℝ) := by
  let Q := availablePairInventory (ReservoirVertex ω true) U
  have hterm : (∑ p : Fin 3, 862 * ((Q p).card - K)) +
        ∑ p : Fin 3, 2 * (Q p).card ≤ 864 * ∑ p : Fin 3, (Q p).card := by
    have h₁ : (∑ p : Fin 3, 862 * ((Q p).card - K)) ≤
        ∑ p : Fin 3, 862 * (Q p).card := by
      apply Finset.sum_le_sum
      intro p _
      omega
    calc
      _ ≤ (∑ p : Fin 3, 862 * (Q p).card) + ∑ p : Fin 3, 2 * (Q p).card := by
        exact Nat.add_le_add_right h₁ _
      _ = _ := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        omega
  have hcard : (A.card : ℝ) ≤ 864 * ∑ p : Fin 3, ((Q p).card : ℝ) := by
    have hnat : A.card ≤ 864 * ∑ p : Fin 3, (Q p).card := hA.trans hterm
    exact_mod_cast hnat
  have hQsum : (∑ p : Fin 3, ((Q p).card : ℝ)) ≤
      3 * τ * (Fintype.card G : ℝ) := by
    calc
      _ ≤ ∑ _p : Fin 3, τ * (Fintype.card G : ℝ) := Finset.sum_le_sum (fun p _ => hQ p)
      _ = _ := by simp; ring
  nlinarith

/-- The lower pair-availability inventory bound and a robust graph at every positive
size supply exactly the selector-query inequalities used by the core. -/
theorem selector_query_of_inventory_lower (ω : FullSample G) (U : Finset G)
    (τ : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3)
    (hnlarge : (4000 : ℝ) ≤ τ^2 * Fintype.card G)
    (hQlower : ∀ part : Fin 3, τ * (Fintype.card G : ℝ) / 3 ≤
      ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ))
    (hgraph : ∀ s : ℕ, 1 ≤ s → Nonempty (ContiguousSelectionGraph s 16)) :
    ∀ part, let Q := availablePairInventory (ReservoirVertex ω true) U part
      1 ≤ Q.card - paddingQuota τ (Fintype.card G) ∧
      Q.card - paddingQuota τ (Fintype.card G) ≤ Q.card ∧
      Q.card ≤ 2 * (Q.card - paddingQuota τ (Fintype.card G)) ∧
      Nonempty (ContiguousSelectionGraph (Q.card - paddingQuota τ (Fintype.card G)) 16) := by
  let n : ℝ := Fintype.card G
  let K := paddingQuota τ (Fintype.card G)
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hk : (K : ℝ) ≤ τ * n / 10000 := by
    unfold K paddingQuota
    exact Nat.floor_le (by positivity)
  have ht : τ^2 * n ≤ τ * n / 3 := by
    have hx : 0 ≤ ((1 / 3 : ℝ) - τ) * τ * n := by positivity
    nlinarith
  intro part
  let Q := availablePairInventory (ReservoirVertex ω true) U part
  have hlower : τ * n / 3 ≤ (Q.card : ℝ) := hQlower part
  have h₁real : (K : ℝ) + 1 ≤ (Q.card : ℝ) := by nlinarith
  have h₂real : (2 : ℝ) * K ≤ (Q.card : ℝ) := by nlinarith
  have h₁ : K + 1 ≤ Q.card := by exact_mod_cast h₁real
  have h₂ : 2 * K ≤ Q.card := by exact_mod_cast h₂real
  change 1 ≤ Q.card - K ∧ Q.card - K ≤ Q.card ∧
    Q.card ≤ 2 * (Q.card - K) ∧ Nonempty (ContiguousSelectionGraph (Q.card - K) 16)
  refine ⟨by omega, by omega, by omega, ?_⟩
  exact hgraph (Q.card - K) (by omega)

/-- On a fixed sample, actual Q event, P selectors and the pair-availability Q-count
range suffice for every later U. The graph is supplied by the proved
deterministic degree-16 existence theorem. -/
theorem fixed_core_of_inventory_bounds (ω : FullSample G)
    (τ p : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3) (hτp : τ ≤ p^4 / 10^30)
    (hodd : Odd (Fintype.card G)) (hnlarge : (4000 : ℝ) ≤ τ^2 * Fintype.card G)
    (hQevent : Buffer.CoreConstructionEvent τ ω)
    (hlocal : ColouredSelectors ω (selectorExternalBudget p (Fintype.card G)))
    (hQbounds : ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      ∀ part : Fin 3,
        τ * (Fintype.card G : ℝ) / 3 ≤
            ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ∧
        ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ≤
            τ * (Fintype.card G : ℝ)) :
    ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      ∃ A : Finset (Vertex G),
        (∀ v ∈ A, v.2 ≠ 0 ∧ signedMinus v.1 ω v.2) ∧
        Disjoint (support A) U ∧
        (A.card : ℝ) ≤ 2592 * τ * (Fintype.card G : ℝ) ∧
        AbsorbsUpTo A (quadraticCoreCapacity τ (Fintype.card G)) := by
  have hquery : ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      ∀ part, let Q := availablePairInventory (ReservoirVertex ω true) U part
        1 ≤ Q.card - paddingQuota τ (Fintype.card G) ∧
        Q.card - paddingQuota τ (Fintype.card G) ≤ Q.card ∧
        Q.card ≤ 2 * (Q.card - paddingQuota τ (Fintype.card G)) ∧
        Nonempty (ContiguousSelectionGraph (Q.card - paddingQuota τ (Fintype.card G)) 16) := by
    intro U hU
    exact selector_query_of_inventory_lower ω U τ hτ hτmax hnlarge
      (fun part => (hQbounds U hU part).1)
      EndpointSelector.FixedCardinality.GraphExpansion.PermutationExistence.selectionGraph_nonempty
  have hbudget : ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      let Q := availablePairInventory (ReservoirVertex ω true) U
      2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
        ∑ part : Fin 3, (2 * (2 * (862 * ((Q part).card - paddingQuota τ (Fintype.card G)))) +
          1724 * ((Q part).card - paddingQuota τ (Fintype.card G))) ≤
        selectorExternalBudget p (Fintype.card G) := by
    intro U hU
    exact selector_budget_of_inventory_upper ω U τ p hτ hτmax hτp hU
      (fun part => (hQbounds U hU part).2)
  intro U hU
  obtain ⟨A,hraw,havoid,hcard,habs⟩ :=
    explicitQEvent_core_of_selector_graph_and_budgets τ hτ hτmax hodd hnlarge ω
      (selectorExternalBudget p (Fintype.card G)) hlocal hQevent hquery hbudget U hU
  refine ⟨A,hraw,havoid,?_,habs⟩
  exact core_card_of_inventory_upper ω U (paddingQuota τ (Fintype.card G)) τ A hcard
    (fun part => (hQbounds U hU part).2)

/-- The actual nonzero signed raw-minus sample used by the matching receiver. -/
def nonzeroRawMinus (ω : FullSample G) : Finset (Vertex G) :=
  Finset.univ.filter (fun v => v.2 ≠ 0 ∧
    signedMinus v.1 ω v.2)

/-- The fixed-core result feeds the existing actual-target matching
receiver's RawCoreSupply interface, preserving the quadratic capacity and
the order ∀U ∃A ∀S. Q event, P selectors and Q counts remain hypotheses. -/
theorem rawCoreSupply_of_inventory_bounds (ω : FullSample G)
    (τ p : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3) (hτp : τ ≤ p^4 / 10^30)
    (hodd : Odd (Fintype.card G)) (hnlarge : (4000 : ℝ) ≤ τ^2 * Fintype.card G)
    (hQevent : Buffer.CoreConstructionEvent τ ω)
    (hlocal : ColouredSelectors ω (selectorExternalBudget p (Fintype.card G)))
    (hQbounds : ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      ∀ part : Fin 3,
        τ * (Fintype.card G : ℝ) / 3 ≤
            ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ∧
        ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ≤
            τ * (Fintype.card G : ℝ)) :
    RawCoreSupply (nonzeroRawMinus ω)
      (quadraticCoreCapacity τ (Fintype.card G)) ⌊2592 * τ * (Fintype.card G : ℝ)⌋₊ := by
  intro U hU
  obtain ⟨A,hraw,havoid,hsize,habs⟩ :=
    fixed_core_of_inventory_bounds ω τ p hτ hτmax hτp hodd hnlarge hQevent hlocal hQbounds U hU
  refine ⟨A,?_,?_,?_,habs⟩
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hraw v hv⟩
  · exact havoid.mono_left Finset.subset_union_left
  · exact Nat.le_floor hsize

/-- The remaining Q-pair estimate, uniformly after any allowable U. -/
def InventoryBounds (τ : ℝ) (ω : FullSample G) : Prop :=
  ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
    ∀ part : Fin 3,
      τ * (Fintype.card G : ℝ) / 3 ≤
          ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ∧
      ((availablePairInventory (ReservoirVertex ω true) U part).card : ℝ) ≤
          τ * (Fintype.card G : ℝ)

/-- The paper-shaped quadratic core is a deterministic consequence of
the three same-sample events: Q supplies, P selectors, and Q pair counts.
No graph or buffer supplier remains as a separate assumption. -/
theorem explicit_universal_core_of_events (ω : FullSample G)
    (τ p : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1 / 3) (hτp : τ ≤ p^4 / 10^30)
    (hodd : Odd (Fintype.card G)) (hnlarge : (4000 : ℝ) ≤ τ^2 * Fintype.card G)
    (hQevent : Buffer.CoreConstructionEvent τ ω)
    (hlocal : ColouredSelectors ω (selectorExternalBudget p (Fintype.card G)))
    (hQbounds : InventoryBounds τ ω) :
    ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
      ∃ A : Finset (Vertex G),
        (∀ v ∈ A, v.2 ≠ 0 ∧ signedMinus v.1 ω v.2) ∧
        Disjoint (support A) U ∧
        (A.card : ℝ) < 16200 * τ * (Fintype.card G : ℝ) ∧
        Balanced A ∧ (∑ v ∈ A, v.2 = 0) ∧
        AbsorbsUpTo A (quadraticCoreCapacity τ (Fintype.card G)) := by
  intro U hU
  obtain ⟨A,hraw,havoid,hsize,habs⟩ :=
    fixed_core_of_inventory_bounds ω τ p hτ hτmax hτp hodd hnlarge hQevent hlocal hQbounds U hU
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpositive : 0 < τ * (Fintype.card G : ℝ) := mul_pos hτ hn
  have hsize' : (A.card : ℝ) < 16200 * τ * (Fintype.card G : ℝ) := by nlinarith
  obtain ⟨M⟩ := habs.matches_empty
  exact ⟨A,hraw,havoid,hsize',matching_balanced M,matching_sum_eq_zero M,habs⟩

end
end EndpointMatching.UniversalCore
