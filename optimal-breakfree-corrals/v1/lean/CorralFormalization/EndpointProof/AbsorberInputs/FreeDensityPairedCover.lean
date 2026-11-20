import CorralFormalization.EndpointProof.AbsorberInputs.TetrahedronCategoricalCounts
import CorralFormalization.EndpointProof.Flow.Tetrahedron.PairedCover
import CorralFormalization.EndpointProof.Matching.UniversalCore.PairedCoverProperties

/-! paired cover construction's tetrahedron/ordinary cover under a free categorical Q density.
The probability theorem constructs one event before every residual and
numerical exclusion. No upstream q-law, supplier or good-event premise is
required. Buffer availability is joined in the companion module. -/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace AbsorberInputs.CategoricalQ
open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointFlow.AbelianTransport EndpointMatching.Tetrahedron EndpointMatching.UniversalCore
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem parameters_failure_probability (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (hτ : 0 < (τ : ℝ))
    (hn : 1152 ≤ Fintype.card G) (budget : ℕ)
    (hbudget : (budget : ℝ) ≤ (τ : ℝ)^2*(Fintype.card G : ℝ)/192) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label |
      ¬ TetrahedronParametersAvailable (categoricalQ w) budget} ≤
      (Fintype.card G : ℝ)^6*Real.exp (-(τ : ℝ)^24*(Fintype.card G : ℝ)/2304) +
      6*(Fintype.card G : ℝ)^7*Real.exp (-(τ : ℝ)^20*(Fintype.card G : ℝ)/100) := by
  have ht := parameters_probability_of_count_tails (orbitMeasure (O := OddOrbit G) p τ h)
    categoricalQ (τ : ℝ) (Fintype.card G : ℝ)
    (Real.exp (-(τ : ℝ)^24*(Fintype.card G : ℝ)/2304))
    (Real.exp (-(τ : ℝ)^20*(Fintype.card G : ℝ)/100)) budget hτ (by positivity) hbudget
    (fun rq => by simpa only [not_le,categoricalTotalCount] using
      tetrahedron_lower_tail hodd p τ h (queryRoots rq) rq.2 hn)
    (fun rq i g => by
      apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
        (section_upper_tail hodd p τ h (queryRoots rq) i g)
      intro w hw
      change 2*(τ : ℝ)^10*(Fintype.card G : ℝ)^2 < _
      have hc : (((goodCandidates (categoricalQ w) (queryRoots rq)).filter
          (fun t => tetrahedronDirection i t = g)).card : ℝ) ≤
          categoricalSectionCount (queryRoots rq) i g w := by
        dsimp only [categoricalSectionCount]
        exact_mod_cast Finset.card_le_card (goodSection_subset_validReduced hodd w (queryRoots rq) i g)
      exact lt_of_lt_of_le (not_le.mp hw) hc)
  have hc : (Fintype.card (AdmissibleRootQuery G) : ℝ) ≤ (Fintype.card G : ℝ)^6 := by
    exact_mod_cast admissibleRootQuery_card_le (G := G)
  apply ht.trans
  calc
    _ ≤ (Fintype.card G : ℝ)^6*Real.exp (-(τ : ℝ)^24*(Fintype.card G : ℝ)/2304) +
        (Fintype.card G : ℝ)^6*6*(Fintype.card G : ℝ)*
          Real.exp (-(τ : ℝ)^20*(Fintype.card G : ℝ)/100) := by gcongr
    _ = _ := by ring

/-- The full real-budget, exact-pair-count output of printed paired-cover. -/
def PairedCoverAvailabilityEvent (τ : ℝ) (w : OddOrbit G → Label) : Prop :=
  ∀ S : Finset (Vertex G), Balanced S → (∀ v ∈ S, v.2 ≠ 0) →
    (∑ v ∈ S, v.2 = 0) → ∀ U : Finset G,
    2*(U.card : ℝ)+20*(S.card : ℝ) ≤ τ^2*(Fintype.card G : ℝ)/1000 →
    ∃ C : FourThirdsPairedCover (categoricalQ w) S U,
      C.pairsPerPart = 4*((slice S 0).card-1) ∧
      C.added.card ≤ 8*S.card ∧
      Disjoint (support C.added)
        ((U ∪ S.image Prod.snd) ∪ (U ∪ S.image Prod.snd).image Neg.neg)

theorem explicitPairedCoverEvent_of_parameters (hodd : Odd (Fintype.card G))
    (τ : ℝ) (w : OddOrbit G → Label)
    (hparams : TetrahedronParametersAvailable (categoricalQ w)
      (quadraticCoverBudget τ (Fintype.card G))) : PairedCoverAvailabilityEvent τ w := by
  intro S hb hnz hsum U hbudget
  have hbudget' : 2*U.card+20*S.card ≤ quadraticCoverBudget τ (Fintype.card G) := by
    unfold quadraticCoverBudget
    apply Nat.le_floor
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hbudget
  obtain ⟨C,hC⟩ := fourThirds_cover_exact_abelian hodd (categoricalQ w)
    (quadraticCoverBudget τ (Fintype.card G))
    (fourPairSupplier_of_parameters _ _ hparams) S hb hnz hsum U hbudget'
  exact ⟨C,hC,C.added_card_le,C.avoids_closure⟩

theorem explicitPairedCoverEvent_failure_probability (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (hτ : 0 < (τ : ℝ))
    (hn : 1152 ≤ Fintype.card G) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label | ¬ PairedCoverAvailabilityEvent (τ : ℝ) w} ≤
      (Fintype.card G : ℝ)^6*Real.exp (-(τ : ℝ)^24*(Fintype.card G : ℝ)/2304) +
      6*(Fintype.card G : ℝ)^7*Real.exp (-(τ : ℝ)^20*(Fintype.card G : ℝ)/100) := by
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (parameters_failure_probability hodd p τ h hτ hn
      (quadraticCoverBudget (τ : ℝ) (Fintype.card G)) ?_)
  · intro w hbad hgood
    exact hbad (explicitPairedCoverEvent_of_parameters hodd (τ : ℝ) w hgood)
  · have hf : (quadraticCoverBudget (τ : ℝ) (Fintype.card G) : ℝ) ≤
        (τ : ℝ)^2*(Fintype.card G : ℝ)/1000 := by
      unfold quadraticCoverBudget
      exact Nat.floor_le (by positivity)
    nlinarith [sq_nonneg (τ : ℝ),Nat.cast_nonneg (α := ℝ) (Fintype.card G)]

/-- Free Q density: p=0, every 0<tau<=1/3. There is no parent-law relation
and no assumed packed availability or matching event. -/
theorem free_density_paired_cover_probability (hodd : Odd (Fintype.card G))
    (τ : ℝ≥0) (hτ : 0 < (τ : ℝ)) (hτmax : (τ : ℝ) ≤ 1/3)
    (hn : 1152 ≤ Fintype.card G) :
    (orbitMeasure 0 τ (by exact_mod_cast (show (3:ℝ)*0+3*(τ : ℝ) ≤ 1 by linarith))).real
      {w : OddOrbit G → Label | ¬ PairedCoverAvailabilityEvent (τ : ℝ) w} ≤
      (Fintype.card G : ℝ)^6*Real.exp (-(τ : ℝ)^24*(Fintype.card G : ℝ)/2304) +
      6*(Fintype.card G : ℝ)^7*Real.exp (-(τ : ℝ)^20*(Fintype.card G : ℝ)/100) :=
  explicitPairedCoverEvent_failure_probability hodd 0 τ _ hτ hn

end
end AbsorberInputs.CategoricalQ
