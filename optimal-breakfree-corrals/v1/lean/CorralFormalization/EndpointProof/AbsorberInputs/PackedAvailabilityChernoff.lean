import CorralFormalization.EndpointProof.Router.Bernoulli
import CorralFormalization.EndpointProof.Selector.PrimitiveAvailability
import CorralFormalization.EndpointProof.Probability.SelectorSameSample

/-!
The mean-scale packed-availability tail for the maintained categorical candidate packings.
The concentration theorem already exists for arbitrary finite probability
spaces. This module applies it to the actual categorical success indicators,
retains the paper's p^4 n/4000 successful-count conclusion, and instantiates
the four real selector primitive families on one unchanged augmentation.
The abstract affine e/m/C0 packing theorem is not asserted here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

namespace AbsorberInputs

open EndpointOriginalReservoir EndpointBlockAvailability EndpointSharedSample
open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

/-- Existing multiplicative Chernoff applied to categorical word indicators.
The word may depend on the candidate, provided its success probability is s. -/
theorem categorical_half_mean_lower_tail {I J : Type*} [Fintype I] [Fintype J]
    (p τ : ℝ≥0) (h : 3*p+3*τ ≤ 1) (demand : I → J → Label)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs : ∀ i, successProbability p τ (demand i) = s) :
    (sampleMeasure p τ h).real
      {w : I → J → Label | (∑ i, successIndicator demand i w) ≤
        (Fintype.card I : ℝ)*s/2} ≤
      Real.exp (-((Fintype.card I : ℝ)*s)/8) := by
  apply EndpointRouter.Bernoulli.half_mean_lower_tail _ _ s hs0 hs1
  · intro i w
    simp only [successIndicator]
    split_ifs <;> simp
  · intro i
    exact (integral_successIndicator p τ h demand i).trans (hs i)
  · exact iIndepFun_pi (X := fun i x => if x = demand i then (1 : ℝ) else 0)
      (fun _ => by fun_prop)

/-- The actual common successful-count event, before every query. -/
def FourOrbitSuccessfulCounts {G Q I J : Type*} [Fintype G] [AddCommGroup G]
    [Fintype I] [Fintype J] (p : ℝ)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (ω : FullSample G) : Prop :=
  ∀ r, p^4*(Fintype.card G : ℝ)/4000 ≤
    ((Finset.univ.filter (fun i => project (e r) (fullLabels ω) i = demand r i)).card : ℝ)

/-- Every homogeneous packed family with mean at least p^4 has the literal
packed-availability p^4 n/4000 count and p^4 n/16000 exponent. All sampling relations and
deterministic embeddings are visible; no good event is a hypothesis. -/
theorem full_four_orbit_successful_counts
    {G Q I J : Type*} [Fintype G] [AddCommGroup G]
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = EndpointOriginalReservoir.rho q η*a)
    (hQ : (τ : ℝ) = EndpointOriginalReservoir.rho q η*b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (hcard : Fintype.card I = Fintype.card G/1000)
    (hsuccess : ∀ r, ∃ s : ℝ, (p : ℝ)^4 ≤ s ∧ s ≤ 1 ∧
      ∀ i, successProbability p τ (demand r i) = s) :
    (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω : FullSample G | ¬ FourOrbitSuccessfulCounts (p : ℝ) e demand ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-((p : ℝ)^4*(Fintype.card G : ℝ))/16000) := by
  let μ := fullMeasure (G := G) q η a b hq0 hq1 hη0 hη1 ha hb hab
  have hMnat : Fintype.card G ≤ 2000*Fintype.card I := by omega
  have hM : (Fintype.card G : ℝ) ≤ 2000*(Fintype.card I : ℝ) := by exact_mod_cast hMnat
  have htail (r : Q) : μ.real
      {ω | ((Finset.univ.filter (fun i => project (e r) (fullLabels ω) i = demand r i)).card : ℝ) <
        (p : ℝ)^4*(Fintype.card G : ℝ)/4000} ≤
      Real.exp (-((p : ℝ)^4*(Fintype.card G : ℝ))/16000) := by
    obtain ⟨s,hs,hs1,heq⟩ := hsuccess r
    have hs0 : 0 ≤ s := (pow_nonneg p.coe_nonneg 4).trans hs
    have hmean : (p : ℝ)^4*(Fintype.card G : ℝ)/4000 ≤ (Fintype.card I : ℝ)*s/2 := by
      have h1 := mul_le_mul_of_nonneg_left hM (pow_nonneg p.coe_nonneg 4)
      have h2 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) (Fintype.card I))
      nlinarith
    have hrate : (p : ℝ)^4*(Fintype.card G : ℝ)/16000 ≤ (Fintype.card I : ℝ)*s/8 := by
      nlinarith
    have hmp := (project_measurePreserving p τ h (e r)).comp
      (fullLabels_measurePreserving hodd q η a b hq0 hq1 hη0 hη1 ha hb hab p τ h hP hQ)
    have hraw := categorical_half_mean_lower_tail p τ h (demand r) s hs0 hs1 heq
    rw [← hmp.measureReal_preimage (by measurability)] at hraw
    apply (measureReal_mono ?_ (measure_ne_top μ _)).trans
      (hraw.trans (Real.exp_le_exp.mpr (by linarith)))
    intro ω hω
    change (∑ i, successIndicator (demand r) i (project (e r) (fullLabels ω))) ≤ _
    rw [sum_successIndicator_eq_card]
    exact hω.le.trans hmean
  have hsub : {ω : FullSample G | ¬ FourOrbitSuccessfulCounts (p : ℝ) e demand ω} ⊆
      ⋃ r : Q, {ω | ((Finset.univ.filter
        (fun i => project (e r) (fullLabels ω) i = demand r i)).card : ℝ) <
        (p : ℝ)^4*(Fintype.card G : ℝ)/4000} := by
    intro ω hbad
    simp only [FourOrbitSuccessfulCounts, not_forall, not_le] at hbad
    obtain ⟨r,hr⟩ := hbad
    exact Set.mem_iUnion.mpr ⟨r,hr⟩
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    ((measureReal_iUnion_fintype_le _).trans (by
      simpa using Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => htail r)))

/-- The successful-count conclusion pays the entire primitive numerical
budget, on the same sample and for every later forbidden set. -/
theorem FourOrbitSuccessfulCounts.available
    {G Q I J : Type*} [Fintype G] [AddCommGroup G]
    [Fintype I] [Fintype J] [DecidableEq I]
    {p : ℝ} (hp : 0 < p)
    {e : Q → I × J ↪ OddOrbit G} {demand : Q → I → J → Label}
    {ω : FullSample G} (hgood : FourOrbitSuccessfulCounts p e demand ω) :
    FullAvailable e demand (selectorBudget p (Fintype.card G)) ω := by
  apply countGood_implies_universallyAvailable
    (fun r => support (e r) orbitPlace)
    (fun r ω i => project (e r) (fullLabels ω) i = demand r i)
    (fun r => support_pairwise (e r) orbitPlace)
  intro r
  have hbudget : (selectorBudget p (Fintype.card G) : ℝ) ≤
      p^4*(Fintype.card G : ℝ)/10^10 := by
    unfold selectorBudget
    exact Nat.floor_le (by positivity)
  have hpos : 0 < p^4*(Fintype.card G : ℝ) := by positivity
  have hcount := hgood r
  have hlt : (selectorBudget p (Fintype.card G) : ℝ) <
      ((Finset.univ.filter
        (fun i => project (e r) (fullLabels ω) i = demand r i)).card : ℝ) := by
    nlinarith
  have hnat : selectorBudget p (Fintype.card G) <
      (Finset.univ.filter (fun i => project (e r) (fullLabels ω) i = demand r i)).card := by
    exact_mod_cast hlt
  apply lt_of_lt_of_eq hnat
  congr 1
  ext i
  simp only [Finset.mem_filter]

/-- The same count event supplies the actual numerical avoidance interface
at the printed primitive budget. The forbidden set is universally later. -/
theorem full_four_orbit_budget_chernoff
    {G Q I J : Type*} [Fintype G] [AddCommGroup G]
    [Fintype Q] [Fintype I] [Fintype J] [DecidableEq I]
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G)
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (p τ : ℝ≥0) (hp : 0 < (p : ℝ)) (h : 3*p+3*τ ≤ 1)
    (hP : (p : ℝ) = EndpointOriginalReservoir.rho q η*a)
    (hQ : (τ : ℝ) = EndpointOriginalReservoir.rho q η*b)
    (e : Q → I × J ↪ OddOrbit G) (demand : Q → I → J → Label)
    (hcard : Fintype.card I = Fintype.card G/1000)
    (hsuccess : ∀ r, ∃ s : ℝ, (p : ℝ)^4 ≤ s ∧ s ≤ 1 ∧
      ∀ i, successProbability p τ (demand r i) = s) :
    (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω : FullSample G | ¬ FullAvailable e demand (selectorBudget p (Fintype.card G)) ω} ≤
      (Fintype.card Q : ℝ) *
        Real.exp (-((p : ℝ)^4*(Fintype.card G : ℝ))/16000) := by
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (full_four_orbit_successful_counts hodd hn q η a b hq0 hq1 hη0 hη1 ha hb hab
      p τ hp h hP hQ e demand hcard hsuccess)
  intro ω hbad hgood
  exact hbad (hgood.available hp)

end
end AbsorberInputs
