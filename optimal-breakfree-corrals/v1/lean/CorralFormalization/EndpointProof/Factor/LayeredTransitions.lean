import CorralFormalization.EndpointProof.Factor.LayerFourier
import CorralFormalization.EndpointProof.Transitions.Ordinary

/-!
# Ordinary transitions on the same sample as exact-matching

The original layer sample supplies the three Fourier inputs of the ordinary transition lemma, with the
correct individual densities and signs. The final theorem fixes one sample
before every choice of roles, signs and later targets. No independence of
different categorical roles is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical
namespace EndpointLayeredSample

open EndpointTransitions EndpointFlow.AbelianTransport
open EndpointMatching.Fractional.Rounding

noncomputable section
universe u

variable {G : Type u} [Fintype G] [AddCommGroup G] {m : ℕ}

/-- The actual ordinary matchings guaranteed for all role triples and all
later balanced targets satisfying the one-sided edit and size budgets. -/
def LayerTransitionEvent (d : Densities m) (t η : ℝ) (s : Sample G m) : Prop :=
  ∀ (roles : Fin 3 → RawRole m) (negative : Fin 3 → Bool),
    (∀ i, DensityWindow d.q (roleDensity d (roles i))) →
    ∀ (T : Fin 3 → Finset G) (ℓ : ℕ),
      (∀ i, (T i).card = ℓ) →
      |(ℓ : ℝ) - d.q * (Fintype.card G : ℝ)| ≤ η * (Fintype.card G : ℝ) →
      (∀ i, (((signedRoleSet s (roles i) (negative i)) \ T i).card : ℝ) ≤
        η * (Fintype.card G : ℝ)) →
      ∃ (P : Finset (Vertex G)) (M : Matching P), P ⊆ targetVertices T ∧
        (ℓ : ℝ) - t * (Fintype.card G : ℝ) ≤ (M.edges.card : ℝ)

/-- ordinary-transition supplies every such later transition from one proved Fourier event.
The only imported matching input is the explicit Pippenger theorem. -/
theorem layeredTransitions_of_transitionFourier
    (hPippenger : PippengerTheorem.{u}) {m : ℕ} (d : Densities m) (t : ℝ)
    (hq : 0 < d.q) (hqthird : d.q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∀ η : ℝ,
      0 < η → η ≤ d.q/1000 → η ≤ t/100 → η ≤ d.q^2*μ/1000 →
      ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
        N ≤ Fintype.card G → ∀ s : Sample G m,
          TransitionFourierEvent d η s → LayerTransitionEvent d t η s := by
  obtain ⟨μ, hμ, hμhalf, hJ⟩ := existsToleranceForOrdinaryMatching hPippenger d.q t hq hqthird ht httenth
  refine ⟨μ, hμ, hμhalf, ?_⟩
  intro η hη hηq hηt hημ
  obtain ⟨N, hN⟩ := hJ η hη hηq hηt hημ
  refine ⟨N, ?_⟩
  intro G _ _ hn s hf roles negative ha T ℓ hbalance hsize hloss
  exact hN G hn (fun i => roleDensity d (roles i)) ha
    (fun i => signedRoleSet s (roles i) (negative i))
    (fun i => hf.roleFourierGood (roles i) (negative i))
    T ℓ hbalance hsize hloss

/-- One original sample supports exact-matching, all pair banks, all raw sizes, and
every later ordinary transition. The router event is not included here. -/
theorem exists_goodSample_and_layeredTransitions
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (hPippenger : PippengerTheorem.{u}) {m : ℕ} (d : Densities m) (t : ℝ)
    (hq : 0 < d.q) (hqthird : d.q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∀ η : ℝ,
      0 < η → η ≤ d.q/1000 → η ≤ t/100 → η ≤ d.q^2*μ/1000 →
      ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
        Odd (Fintype.card G) → N ≤ Fintype.card G →
        ∃ s : Sample G m,
          GoodSample d (explicitSizeTolerance (Fintype.card G)) s ∧ LayerTransitionEvent d t η s := by
  obtain ⟨μ, hμ, hμhalf, htransition⟩ :=
    layeredTransitions_of_transitionFourier hPippenger d t hq hqthird ht httenth
  refine ⟨μ, hμ, hμhalf, ?_⟩
  intro η hη hηq hηt hημ
  obtain ⟨N1, hN1⟩ := htransition η hη hηq hηt hημ
  obtain ⟨N2, hN2⟩ := exists_goodSample_and_transitionFourier hAKS d hq η hη
  refine ⟨max N1 N2, ?_⟩
  intro G _ _ hodd hn
  obtain ⟨s, hgood, hfourier⟩ := hN2 G hodd (by omega)
  exact ⟨s, hgood, hN1 G (by omega) s hfourier⟩

/-- A proved router-event tail can be joined on the actual independent
augmentation. The router's event and failure bound remain explicit inputs;
no independence between the resulting good events is assumed. -/
theorem exists_goodAugmented_and_layeredTransitions
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (hPippenger : PippengerTheorem.{u}) {m : ℕ} (d : Densities m) (t coin : ℝ)
    (hq : 0 < d.q) (hqthird : d.q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10)
    (hcoin0 : 0 ≤ coin) (hcoin1 : coin ≤ 1)
    (router : ∀ (G : Type u) [Fintype G] [AddCommGroup G], AugmentedSample G m → Prop)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hrouter : ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (augmentedMeasure (G := G) d coin hcoin0 hcoin1).real
        {s | ¬ router G s} ≤ error (Fintype.card G)) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∀ η : ℝ,
      0 < η → η ≤ d.q/1000 → η ≤ t/100 → η ≤ d.q^2*μ/1000 →
      ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
        Odd (Fintype.card G) → N ≤ Fintype.card G →
        ∃ s : AugmentedSample G m,
          GoodSample d (explicitSizeTolerance (Fintype.card G)) (forgetAugmented s) ∧
          LayerTransitionEvent d t η (forgetAugmented s) ∧ router G s := by
  obtain ⟨μ, hμ, hμhalf, htransition⟩ :=
    layeredTransitions_of_transitionFourier hPippenger d t hq hqthird ht httenth
  obtain ⟨Nr, hr⟩ := hrouter
  obtain ⟨Ng, hg⟩ := goodSample_failure_probability hAKS d hq
  refine ⟨μ, hμ, hμhalf, ?_⟩
  intro η hη hηq hηt hημ
  obtain ⟨Nt, ht'⟩ := htransition η hη hηq hηt hημ
  have hsum : Tendsto (fun n : ℕ =>
      (explicitFailureBound d n + fourierFailureBound m (η^2) n) + error n) atTop (𝓝 0) := by
    simpa only [add_zero] using
      ((explicitFailureBound_tendsto_zero d hq).add
        (fourierFailureBound_tendsto_zero m (η^2) (sq_pos_of_pos hη))).add herror
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (explicitFailureBound d n + fourierFailureBound m (η^2) n) + error n < 1 :=
    (tendsto_order.1 hsum).2 1 (by norm_num)
  obtain ⟨Ns, hs⟩ := eventually_atTop.1 hsmall
  refine ⟨max Nt (max Ng (max Nr (max Ns 1))), ?_⟩
  intro G _ _ hodd hn
  let n := Fintype.card G
  have hnpos : 0 < n := by dsimp [n]; omega
  have hgood0 := hg G hodd (by omega) (explicitSizeTolerance n) (explicitSizeTolerance_nonneg n)
  rw [failureBound_explicitSizeTolerance d n hnpos] at hgood0
  have hgood := goodSample_and_fourier_explicitBound d (η^2) (sq_nonneg η) hgood0
  have hrouter' := hr G hodd (by omega)
  obtain ⟨s, hs0, hsF, hsR⟩ := exists_goodFourierAugmented_and_event_of_error_lt_one
    d coin hcoin0 hcoin1 (explicitSizeTolerance n) (η^2)
    (explicitFailureBound d n + fourierFailureBound m (η^2) n) (error n)
    hgood (router G) hrouter' (hs n (by dsimp [n]; omega))
  refine ⟨s, hs0, ?_, hsR⟩
  exact ht' G (by omega) (forgetAugmented s) (transitionFourierEvent_of_fourierEvent hsF)

end
end EndpointLayeredSample
