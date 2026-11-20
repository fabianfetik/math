import CorralFormalization.EndpointProof.Probability.LayeredSample.RouterSwitch
import CorralFormalization.EndpointProof.Router.ReservoirEvent

/-!
The proved local router reservoir event on the actual layer augmentation.

This includes both exchange and idle primitive supply, and the vertex-bank
size used for intermediate ports.  It does not assert the global two-layer
router assembly or the final spanning factor.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointMatching.Fractional.Rounding

noncomputable section
universe v

theorem explicitSwitchBudget_eq_routerExplicitBudget (u : ℝ) (n : ℕ) :
    explicitSwitchBudget u n = EndpointRouter.routerTrialBudget u n := by
  unfold explicitSwitchBudget switchBudgetDensity EndpointRouter.routerTrialBudget
  congr 1
  ring

/-- The actual local reservoir event, using the exact thinned channels and
the literal paper floor budget. -/
def AugmentedRouterReservoirEvent {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (u : ℝ) (s : AugmentedSample G m) : Prop :=
  EndpointRouter.ReservoirEvent u (explicitSwitchBudget u (Fintype.card G)) (routerBits s)

def reservoirFailureBound (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ)^4 + (n : ℝ)^2 + 1) * Real.exp (-(u^18 / 32000) * (n : ℝ))

/-- The router theorem's actual probability estimate is transferred by
equality of laws.  No router probability premise is assumed. -/
theorem augmentedRouterReservoirEvent_failure_probability
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (hr : 0 < d.r) (u : ℝ) (hu0 : 0 ≤ u) (hur : u ≤ d.r)
    (hodd : Odd (Fintype.card G)) (hn : 4000 ≤ Fintype.card G) :
    (augmentedMeasure (G := G) d (u / d.r) (div_nonneg hu0 hr.le)
      ((div_le_one hr).mpr hur)).real {s | ¬ AugmentedRouterReservoirEvent u s} ≤
      reservoirFailureBound u (Fintype.card G) := by
  have hp := routerBits_measurePreserving (G := G) d hr u hu0 hur
  have htail := EndpointRouter.reservoirEvent_probability
    hodd hn u hu0 (hur.trans d.r_le_one)
    (explicitSwitchBudget u (Fintype.card G)) (explicitSwitchBudget_le u (Fintype.card G))
  rw [← hp.measureReal_preimage (by measurability)] at htail
  simpa only [AugmentedRouterReservoirEvent, reservoirFailureBound, Set.preimage_ofPred_eq,
    show -(u^18 * (Fintype.card G : ℝ)) / 32000 =
      -(u^18 / 32000) * (Fintype.card G : ℝ) by ring] using htail

theorem reservoirFailureBound_tendsto_zero (u : ℝ) (hu : 0 < u) :
    Tendsto (reservoirFailureBound u) atTop (𝓝 0) := by
  have h4 := switchFailureBound_tendsto_zero u hu
  have h2 : Tendsto (fun n : ℕ =>
      (n : ℝ)^2 * Real.exp (-(u^18 / 32000) * (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      2 (u^18 / 32000) (by positivity)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_ofNat] using h
  have h0 : Tendsto (fun n : ℕ =>
      Real.exp (-(u^18 / 32000) * (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      0 (u^18 / 32000) (by positivity)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_zero, one_mul] using h
  have hsum := (h4.add h2).add h0
  simp only [add_zero] at hsum
  refine Tendsto.congr ?_ hsum
  intro n
  simp only [switchFailureBound, reservoirFailureBound]
  ring

/-- exact-matching, every later ordinary-transition transition, every raw pair/size event, both local
router primitive types and enough intermediate-port vertices hold on one
actual reserve augmentation.  The sole nonstandard theorem parameters are
the same explicit AKS and Pippenger inputs as before. -/
theorem exists_goodAugmented_layeredTransitions_and_routerReservoir
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{v} K D₀ C)
    (hPippenger : EndpointTransitions.PippengerTheorem.{v})
    {m : ℕ} (d : Densities m) (t u : ℝ)
    (hq : 0 < d.q) (hqthird : d.q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10)
    (hr : 0 < d.r) (hu : 0 < u) (hur : u ≤ d.r) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∀ η : ℝ,
      0 < η → η ≤ d.q/1000 → η ≤ t/100 → η ≤ d.q^2*μ/1000 →
      ∃ N : ℕ, ∀ (G : Type v) [Fintype G] [AddCommGroup G],
        Odd (Fintype.card G) → N ≤ Fintype.card G →
        ∃ s : AugmentedSample G m,
          GoodSample d (explicitSizeTolerance (Fintype.card G)) (forgetAugmented s) ∧
          LayerTransitionEvent d t η (forgetAugmented s) ∧
          AugmentedRouterReservoirEvent u s := by
  let event : ∀ (G : Type v) [Fintype G] [AddCommGroup G], AugmentedSample G m → Prop :=
    fun G _ _ => AugmentedRouterReservoirEvent u
  have hrouter : ∃ N : ℕ, ∀ (G : Type v) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (augmentedMeasure (G := G) d (u / d.r) (div_nonneg hu.le hr.le)
        ((div_le_one hr).mpr hur)).real {s | ¬ event G s} ≤
          reservoirFailureBound u (Fintype.card G) := by
    refine ⟨4000, ?_⟩
    intro G _ _ hodd hn
    exact augmentedRouterReservoirEvent_failure_probability d hr u hu.le hur hodd hn
  exact exists_goodAugmented_and_layeredTransitions hAKS hPippenger d t (u / d.r)
    hq hqthird ht httenth (div_nonneg hu.le hr.le) ((div_le_one hr).mpr hur)
    event (reservoirFailureBound u) (reservoirFailureBound_tendsto_zero u hu) hrouter

/-- The reservoir used by the actual primitive theorem lies inside the
raw vertex reserve of this same layer sample. -/
theorem routerVertexReservoir_subset_rawReserve
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ} (s : AugmentedSample G m) :
    EndpointRouter.vertexReservoir (routerBits s) ⊆
      (vertexSet (forgetAugmented s) (reserveVertex m) : Set G) := by
  intro g hg
  apply Finset.mem_coe.mpr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, thinnedVertex_mem_reserve s g ?_⟩
  exact hg

/-- The reservoir used by the actual primitive theorem lies inside the
raw colour reserve of this same layer sample. -/
theorem routerColourReservoir_subset_rawReserve
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ} (s : AugmentedSample G m) :
    EndpointRouter.colorReservoir (routerBits s) ⊆
      (colourSet (forgetAugmented s) (reserveColour m) : Set G) := by
  intro g hg
  apply Finset.mem_coe.mpr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, thinnedColour_mem_reserve s g ?_⟩
  exact hg

/-- Physical local supply from the two actual thinned reserve channels,
for every later legal exchange or idle query and forbidden set. -/
theorem AugmentedRouterReservoirEvent.local_apply
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {u : ℝ} {s : AugmentedSample G m} (h : AugmentedRouterReservoirEvent u s)
    (q : EndpointRouter.Query G) (hq : q.Legal) (F : Finset G)
    (hF : F.card ≤ explicitSwitchBudget u (Fintype.card G)) :
    ∃ P : EndpointRouter.Primitive G,
      P.Good {g | (thinnedReserves s).1 g = true} {g | (thinnedReserves s).2 g = true} q ∧
      Disjoint P.support F := by
  have hp := h.1 q hq F hF
  simpa only [EndpointRouter.vertexReservoir, EndpointRouter.colorReservoir,
    routerBits_vertex, routerBits_colour] using hp

/-- The very same event installs any later finite legal schedule whose
explicit numerical support cost fits the paid floor budget. -/
theorem AugmentedRouterReservoirEvent.install
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {u : ℝ} {s : AugmentedSample G m} (h : AugmentedRouterReservoirEvent u s)
    (queries : List (EndpointRouter.Query G)) (F : Finset G)
    (hlegal : ∀ q ∈ queries, q.Legal)
    (hbudget : F.card + (queries.map (fun q => 9*q.arity)).sum ≤
      explicitSwitchBudget u (Fintype.card G)) :
    ∃ installed : List (EndpointRouter.Primitive G),
      List.Forall₂ (EndpointRouter.Primitive.Good
        {g | (thinnedReserves s).1 g = true} {g | (thinnedReserves s).2 g = true})
        queries installed ∧
      installed.Pairwise (fun P Q => Disjoint P.support Q.support) ∧
      (∀ P ∈ installed, Disjoint P.support F) := by
  have hp := EndpointRouter.ReservoirEvent.install
    u (explicitSwitchBudget u (Fintype.card G)) (routerBits s) h queries F hlegal hbudget
  simpa only [EndpointRouter.vertexReservoir, EndpointRouter.colorReservoir,
    routerBits_vertex, routerBits_colour] using hp

theorem AugmentedRouterReservoirEvent.vertex_pool_bound
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {u : ℝ} {s : AugmentedSample G m} (h : AugmentedRouterReservoirEvent u s) :
    u * (Fintype.card G : ℝ) / 2 ≤ (EndpointRouter.vertexPool (routerBits s)).card := h.2

/-- The paid pool-size estimate supports the existing concrete
intermediate-port chooser, with its explicit later cardinality budget. -/
theorem AugmentedRouterReservoirEvent.choose_ports
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    {u : ℝ} {s : AugmentedSample G m} (h : AugmentedRouterReservoirEvent u s)
    (F : Finset G) (previous : G) (deltas : List G)
    (hcard : (F.card : ℝ) + deltas.length + 2 < u * (Fintype.card G : ℝ) / 2) :
    ∃ ports : List G,
      ports.length = deltas.length ∧ ports.Nodup ∧
      (∀ p ∈ ports, p ∈ EndpointRouter.vertexPool (routerBits s) ∧ p ∉ F) ∧
      List.Forall₂ (fun difference delta => difference ≠ delta ∧ difference ≠ -delta)
        (EndpointFactor.edgeLabels (fun a b : G => b-a) (previous::ports)) deltas := by
  exact EndpointRouter.ReservoirEvent.choose_ports
    u (explicitSwitchBudget u (Fintype.card G)) (routerBits s) h F previous deltas hcard

end
end EndpointLayeredSample
