import CorralFormalization.EndpointProof.AbsorberInputs.BufferCategoricalCounts

/-! Full printed paired-cover on one categorical Q law of any fixed density
0<tau<=1/3, including the disjoint padding buffers used downstream. -/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
namespace AbsorberInputs.CategoricalQ
open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointFlow.AbelianTransport EndpointMatching.UniversalCore
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]
local notation "catQ" => EndpointMatching.Tetrahedron.categoricalQ
local notation "BParam" => EndpointMatching.UniversalCore.Buffer.Parameters

/-- Exactly floor(tau n/1000) actual matchable buffers are chosen after U,
with pairwise disjoint numerical inverse-orbit supports and avoiding U. -/
def BufferCountEvent (τ : ℝ) (w : OddOrbit G → Label) : Prop :=
  ∀ U : Finset G, U.card ≤ quadraticCoreCapacity τ (Fintype.card G) →
    ∃ B : Finset (BParam G), B.card = paddingBufferCount τ (Fintype.card G) ∧
      (∀ t ∈ B, t ∈ EndpointMatching.UniversalCore.Buffer.goodCandidates (catQ w) ∧
        Disjoint (EndpointMatching.UniversalCore.Buffer.pairSupport t) U) ∧
      (∀ t ∈ B, ∀ u ∈ B, t ≠ u →
        Disjoint (EndpointMatching.UniversalCore.Buffer.pairSupport t)
          (EndpointMatching.UniversalCore.Buffer.pairSupport u)) ∧
      (∀ t ∈ B, Nonempty (Matching (Finset.univ.biUnion
        (EndpointMatching.UniversalCore.Buffer.pick t))))

theorem explicitBufferEvent_of_counts (hodd : Odd (Fintype.card G))
    (τ : ℝ) (hτ : 0 < τ) (hτmax : τ ≤ 1/3) (w : OddOrbit G → Label)
    (hcounts : BufferCounts.BufferCountEvent τ w) : BufferCountEvent τ w := by
  have hold : EndpointMatching.UniversalCore.Buffer.CountEvent τ (labelSection hodd w) := by
    simpa only [EndpointMatching.UniversalCore.Buffer.CountEvent,
      EndpointMatching.UniversalCore.Buffer.categoricalTotalCount,
      reservoir_labelSection,BufferCounts.BufferCountEvent] using hcounts
  intro U hU
  obtain ⟨B,hcard,hgood,hdis⟩ :=
    EndpointMatching.UniversalCore.Buffer.countEvent_disjoint_buffers τ hτ
      (labelSection hodd w) hold U (paddingBufferCount τ (Fintype.card G))
      (EndpointMatching.UniversalCore.Buffer.explicit_buffer_budget τ hτ hτmax U hU)
  rw [reservoir_labelSection] at hgood
  refine ⟨B,hcard,hgood,hdis,?_⟩
  intro t ht
  have hv : EndpointMatching.UniversalCore.Buffer.GeometricallyValid t :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hgood t ht).1).1).2
  exact EndpointMatching.UniversalCore.Buffer.matching_of_valid hodd t hv

/-- One event before every paired-cover query and every independent later
buffer exclusion. Each cover and buffer family is a genuine finite output. -/
def PairedCoverAndBuffersEvent (τ : ℝ) (w : OddOrbit G → Label) : Prop :=
  PairedCoverAvailabilityEvent τ w ∧ BufferCountEvent τ w

theorem pairedCoverAndBuffers_explicit_failure_probability (hodd : Odd (Fintype.card G))
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (hτ : 0 < (τ : ℝ))
    (hτmax : (τ : ℝ) ≤ 1/3) (hn : 1152 ≤ Fintype.card G) :
    (orbitMeasure p τ h).real {w : OddOrbit G → Label | ¬ PairedCoverAndBuffersEvent (τ : ℝ) w} ≤
      (Fintype.card G : ℝ)^6*Real.exp (-(τ : ℝ)^24*(Fintype.card G : ℝ)/2304) +
      6*(Fintype.card G : ℝ)^7*Real.exp (-(τ : ℝ)^20*(Fintype.card G : ℝ)/100) +
      Real.exp (-(τ : ℝ)^6*(Fintype.card G : ℝ)/144) +
      3*(Fintype.card G : ℝ)*Real.exp (-(τ : ℝ)^4*(Fintype.card G : ℝ)/4) := by
  have hsub : {w : OddOrbit G → Label | ¬ PairedCoverAndBuffersEvent (τ : ℝ) w} ⊆
      {w | ¬ PairedCoverAvailabilityEvent (τ : ℝ) w} ∪
        {w | ¬ BufferCounts.BufferCountEvent (τ : ℝ) w} := by
    intro w hbad
    by_contra hnot
    have hc : PairedCoverAvailabilityEvent (τ : ℝ) w := by
      by_contra hc
      exact hnot (Or.inl hc)
    have hb : BufferCounts.BufferCountEvent (τ : ℝ) w := by
      by_contra hb
      exact hnot (Or.inr hb)
    exact hbad ⟨hc,explicitBufferEvent_of_counts hodd (τ : ℝ) hτ hτmax w hb⟩
  have hC := explicitPairedCoverEvent_failure_probability hodd p τ h hτ hn
  have hB := BufferCounts.bufferCountEvent_failure_probability hodd p τ h (by omega)
  have ht := (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add hC hB))
  linarith

theorem pairedCoverFailure_le_exponentialBound (τ n : ℝ) (hτ0 : 0 ≤ τ) (hτmax : τ ≤ 1)
    (hn : 1 ≤ n) :
    n^6*Real.exp (-τ^24*n/2304) + 6*n^7*Real.exp (-τ^20*n/100) +
      Real.exp (-τ^6*n/144) + 3*n*Real.exp (-τ^4*n/4) ≤
      11*n^7*Real.exp (-τ^24*n/2304) := by
  have hn0 : 0 ≤ n := by linarith
  have h20 : τ^24 ≤ τ^20 := pow_le_pow_of_le_one hτ0 hτmax (by norm_num)
  have h6 : τ^24 ≤ τ^6 := pow_le_pow_of_le_one hτ0 hτmax (by norm_num)
  have h4 : τ^24 ≤ τ^4 := pow_le_pow_of_le_one hτ0 hτmax (by norm_num)
  have e20 : Real.exp (-τ^20*n/100) ≤ Real.exp (-τ^24*n/2304) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right h20 hn0,mul_nonneg (pow_nonneg hτ0 20) hn0]
  have e6 : Real.exp (-τ^6*n/144) ≤ Real.exp (-τ^24*n/2304) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right h6 hn0,mul_nonneg (pow_nonneg hτ0 6) hn0]
  have e4 : Real.exp (-τ^4*n/4) ≤ Real.exp (-τ^24*n/2304) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right h4 hn0,mul_nonneg (pow_nonneg hτ0 4) hn0]
  have hn6 : 1 ≤ n^6 := one_le_pow₀ hn
  have hn7eq : n^7 = n^6*n := by ring
  have hn67 : n^6 ≤ n^7 := by rw [hn7eq]; nlinarith
  have hn17 : 1 ≤ n^7 := one_le_pow₀ hn
  have hnn7 : n ≤ n^7 := by rw [hn7eq]; nlinarith
  calc
    _ ≤ n^6*Real.exp (-τ^24*n/2304) + 6*n^7*Real.exp (-τ^24*n/2304) +
        Real.exp (-τ^24*n/2304) + 3*n*Real.exp (-τ^24*n/2304) := by
      have a := mul_le_mul_of_nonneg_left e20 (show 0 ≤ 6*n^7 by positivity)
      have b := mul_le_mul_of_nonneg_left e4 (show 0 ≤ 3*n by positivity)
      linarith
    _ ≤ _ := by
      have a := mul_le_mul_of_nonneg_right hn67 (Real.exp_nonneg (-τ^24*n/2304))
      have b := mul_le_mul_of_nonneg_right hn17 (Real.exp_nonneg (-τ^24*n/2304))
      have c := mul_le_mul_of_nonneg_right hnn7 (Real.exp_nonneg (-τ^24*n/2304))
      nlinarith

/-- The full free-density paired-cover event, including the same-sample disjoint
padding buffers, with the printed rate and explicit absolute constant 11.
Only oddness, 0<tau<=1/3 and the universal order threshold n>=1152 remain. -/
theorem free_density_ordinary_cover_probability (hodd : Odd (Fintype.card G))
    (τ : ℝ≥0) (hτ : 0 < (τ : ℝ)) (hτmax : (τ : ℝ) ≤ 1/3)
    (hn : 1152 ≤ Fintype.card G) :
    (orbitMeasure 0 τ (by exact_mod_cast (show (3:ℝ)*0+3*(τ : ℝ) ≤ 1 by linarith))).real
      {w : OddOrbit G → Label | ¬ PairedCoverAndBuffersEvent (τ : ℝ) w} ≤
      11*(Fintype.card G : ℝ)^7*Real.exp (-(τ : ℝ)^24*(Fintype.card G : ℝ)/2304) := by
  apply (pairedCoverAndBuffers_explicit_failure_probability hodd 0 τ _ hτ hτmax hn).trans
  exact pairedCoverFailure_le_exponentialBound (τ : ℝ) (Fintype.card G : ℝ) τ.coe_nonneg
    (by linarith) (by exact_mod_cast (show 1 ≤ Fintype.card G by omega))

end
end AbsorberInputs.CategoricalQ
