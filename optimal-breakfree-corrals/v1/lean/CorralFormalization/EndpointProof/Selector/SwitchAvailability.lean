import CorralFormalization.EndpointProof.Selector.PackedOrbitSupply
import CorralFormalization.EndpointProof.Probability.SamplingParameterChoices

/-!
# The actual exact-matching parameters and the concrete selector two-pair switch event

This is the bounded primitive, with roots in tagged A. It is not the complete
coloured k-selector, absorber, exact matching theorem, or endpoint theorem.
-/

open scoped Classical NNReal

universe u

namespace EndpointSelector

open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

section Finite

variable {G : Type*} [CommRing G] [Fintype G]

/-- Literal exact-matching parameters; the only sampling inputs are `0 < q ≤ 1/2`.
All root queries and all later forbidden supports are included in the event. -/
theorem original_switch_budget
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 2000 ≤ Fintype.card G) :
    (EndpointFullProduct.originalMeasure q (le_of_lt hq0) hq1).real
      {s : EndpointFullProduct.OriginalSample G |
        ¬ EndpointFullProduct.OriginalAdmitsAvailable (queryEmbedding hodd (by omega))
          (fun _ _ ↦ switchDemand) (selectorBudget (p q) (Fintype.card G)) s} ≤
      (Fintype.card G : ℝ)^2 *
        Real.exp (-(p q^8 / 32000) * (Fintype.card G : ℝ)) := by
  obtain ⟨hη0,hη1,hα,hβ,hαβ,hp,hcat,hP,hQ⟩ :=
    samplingParameters_admissible q hq0 hq1
  exact original_sample_switch_budget hodd hn q eta (1/4) (tau q / rho q)
    (le_of_lt hq0) hq1 hη0 hη1 hα hβ hαβ (pNN q) (tauNN q) hp hcat hP hQ

/-- The projected common augmentation supplies an actual original-model
two-pair switch for each later root/forbidden-set query. -/
theorem successful_switch_of_originalAdmitsAvailable
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (s : EndpointFullProduct.OriginalSample G)
    (hgood : EndpointFullProduct.OriginalAdmitsAvailable (queryEmbedding hodd hn)
      (fun _ _ ↦ switchDemand) budget s)
    (r : RootQuery G) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ u : G, Valid r.val.1 r.val.2 u ∧
      Disjoint (orbitSupport r.val.1 r.val.2 u) F ∧
      (∀ v ∈ interior r.val.1 r.val.2 u, EndpointFullProduct.originalSigned v.1 s v.2) ∧
      IsTwoEdgeMatchingOn (leftState r.val.1 r.val.2 u)
        (interior r.val.1 r.val.2 u ∪ target r.val.1) ∧
      IsTwoEdgeMatchingOn (rightState r.val.1 r.val.2 u)
        (interior r.val.1 r.val.2 u ∪ target r.val.2) := by
  obtain ⟨ω,hω,havailable⟩ := hgood
  obtain ⟨u,hv,hd,hP,hl,hr⟩ :=
    successful_switch_in_original_model hodd hn budget ω havailable r F hF
  refine ⟨u,hv,hd,?_,hl,hr⟩
  intro v hv
  rw [← hω]
  exact (hP v hv).2

/-- One common augmentation of the same original sample works for every
subsequent root query and every subsequent forbidden set. This is existential
in ω and does not assert that other augmentations are successful. -/
theorem one_augmentation_all_switches
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (s : EndpointFullProduct.OriginalSample G)
    (hgood : EndpointFullProduct.OriginalAdmitsAvailable (queryEmbedding hodd hn)
      (fun _ _ ↦ switchDemand) budget s) :
    ∃ ω : EndpointFullProduct.FullSample G,
      EndpointFullProduct.originalProcess ω = s ∧
      ∀ (r : RootQuery G) (F : Finset G), F.card ≤ budget →
        ∃ u : G, Valid r.val.1 r.val.2 u ∧
          Disjoint (orbitSupport r.val.1 r.val.2 u) F ∧
          (∀ v ∈ interior r.val.1 r.val.2 u, PVertex ω v ∧
            EndpointFullProduct.originalSigned v.1 s v.2) ∧
          IsTwoEdgeMatchingOn (leftState r.val.1 r.val.2 u)
            (interior r.val.1 r.val.2 u ∪ target r.val.1) ∧
          IsTwoEdgeMatchingOn (rightState r.val.1 r.val.2 u)
            (interior r.val.1 r.val.2 u ∪ target r.val.2) := by
  obtain ⟨ω,hω,havailable⟩ := hgood
  refine ⟨ω,hω,?_⟩
  intro r F hF
  obtain ⟨u,hv,hd,hP,hl,hr⟩ :=
    successful_switch_in_original_model hodd hn budget ω havailable r F hF
  refine ⟨u,hv,hd,?_,hl,hr⟩
  intro v hv
  exact ⟨(hP v hv).1, by rw [← hω]; exact (hP v hv).2⟩

end Finite

/-- For each fixed paper density q, a single group-independent threshold works
for every finite odd commutative ring, hence for every sufficiently large odd
cyclic group. The failure exponent is exactly uniform exact-matching theorem's ξ⁴/10⁶; this event supplies
the two-pair A-root primitive only. -/
theorem original_switch_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type u) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (EndpointFullProduct.originalMeasure q (le_of_lt hq0) hq1).real
        {s : EndpointFullProduct.OriginalSample G |
          ¬ EndpointFullProduct.OriginalAdmitsAvailable (queryEmbedding hodd (by omega))
            (fun _ _ ↦ switchDemand) (selectorBudget (p q) (Fintype.card G)) s} ≤
        Real.exp (-(xi q^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := sampling_rates_pay_polynomial_union q 1 2 hq0 hq1
  refine ⟨N,?_⟩
  intro G _ _ hodd hn
  have hn2000 : 2000 ≤ Fintype.card G := (le_max_right N 2000).trans hn
  have hnN : N ≤ Fintype.card G := (le_max_left N 2000).trans hn
  have hh := original_switch_budget q hq0 hq1 hodd hn2000
  exact hh.trans (by simpa only [one_mul] using (hN (Fintype.card G) hnN).2)

end

end EndpointSelector
