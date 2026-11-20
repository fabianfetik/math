import CorralFormalization.EndpointProof.Router.Installation.Installed
import CorralFormalization.EndpointProof.Router.Installation.Legal

/-! # The paper's actual fixed two-layer installation

One sample event is fixed first. Every later forbidden set and disjoint pair of
ordered external port sets satisfying the paper ledger is then accepted. The
intermediate ports and local geometry are chosen now; no closing permutation
occurs in their premises. The construction is valid also for one track, when
both layers consist entirely of idle units.
-/
namespace EndpointRouter
open EndpointLayeredSample
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G]

/-- All geometric installation data follow from the proved event and paid
port hypotheses, without an extra primitive or geometry supplier. -/
theorem ReservoirEvent.install_explicit_geometry {n : ℕ} (u : ℝ) (ω : Bool × G → Bool)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (h : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) ω)
    (F : Finset G) (input output : Fin n → G)
    (hin : Function.Injective input) (hout : Function.Injective output)
    (hcross : ∀ i j, input i ≠ output j)
    (hledger : ((F.card + 22*n : ℕ) : ℝ) ≤ explicitRouterDensity u * (Fintype.card G : ℝ)/4)
    (hn : 8 ≤ u*(Fintype.card G : ℝ)) :
    ∃ middle : Fin n → G,
      ∃ first : LayerGeometry (firstMatchingLayer n) input middle,
        ∃ second : LayerGeometry (secondMatchingLayer n) middle output,
          TwoLayerSupport first second ∧
          TwoLayerGood (vertexReservoir ω) (colorReservoir ω) first second ∧
          (∀ i, middle i ∈ vertexReservoir ω ∧ middle i ∉ F) ∧
          (∀ v, Disjoint (twoLayerUnitSupport first second v) F) := by
  obtain ⟨middle,hmid,hfresh,hdiff⟩ :=
    h.choose_intermediate_ports u ω hu hu1 F input output hledger hn
  have hports : Function.Injective (routerPort input middle output) :=
    routerPort_injective_of_fresh input middle output hin hout hcross hmid
      (fun i => fun he => (hfresh i).2 (Finset.mem_union_right _ he))
  obtain ⟨hlegal₁,hlegal₂⟩ := alternating_queries_legal input middle output hports hdiff
  obtain ⟨first,second,hsupport,hgood,hF⟩ :=
    h.install_geometry u ω (firstMatchingLayer n) (secondMatchingLayer n)
      input middle output F hports hlegal₁ hlegal₂ hledger
  refine ⟨middle,first,second,hsupport,hgood,?_,hF⟩
  intro i
  constructor
  · simpa only [vertexPool,Finset.mem_filter,Finset.mem_univ,true_and,vertexReservoir,Set.mem_ofPred_eq] using (hfresh i).1
  · intro hi
    exact (hfresh i).2 (Finset.mem_union_left _ hi)

/-- For a positive track count the displayed ledger itself already implies
all finite port-selection slack; no further order threshold is needed. -/
theorem explicitLedger_vertex_threshold {n : ℕ} (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1)
    (htracks : 0 < n) (F : Finset G)
    (hledger : ((F.card + 22*n : ℕ) : ℝ) ≤ explicitRouterDensity u * (Fintype.card G : ℝ)/4) :
    8 ≤ u*(Fintype.card G : ℝ) := by
  have hb := (explicitRouterDensity_bounds u hu hu1).2
  have hbN := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  have hpositive : (1 : ℝ) ≤ n := by exact_mod_cast htracks
  have hF : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  push_cast at hledger
  nlinarith

/-- Exactly the paper's positive-track installation quantifiers. In particular
`n = 1` requires no exception and no extra size hypothesis. -/
theorem ReservoirEvent.install_explicit_geometry_positive {n : ℕ} (u : ℝ) (ω : Bool × G → Bool)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (h : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) ω) (htracks : 0 < n)
    (F : Finset G) (input output : Fin n → G)
    (hin : Function.Injective input) (hout : Function.Injective output)
    (hcross : ∀ i j, input i ≠ output j)
    (hledger : ((F.card + 22*n : ℕ) : ℝ) ≤ explicitRouterDensity u * (Fintype.card G : ℝ)/4) :
    ∃ middle : Fin n → G,
      ∃ first : LayerGeometry (firstMatchingLayer n) input middle,
        ∃ second : LayerGeometry (secondMatchingLayer n) middle output,
          TwoLayerSupport first second ∧
          TwoLayerGood (vertexReservoir ω) (colorReservoir ω) first second ∧
          (∀ i, middle i ∈ vertexReservoir ω ∧ middle i ∉ F) ∧
          (∀ v, Disjoint (twoLayerUnitSupport first second v) F) :=
  h.install_explicit_geometry u ω hu hu1 F input output hin hout hcross hledger
    (explicitLedger_vertex_threshold u hu hu1 htracks F hledger)

end
end EndpointRouter
