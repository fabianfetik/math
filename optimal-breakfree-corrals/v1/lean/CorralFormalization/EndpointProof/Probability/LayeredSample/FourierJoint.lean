import CorralFormalization.EndpointProof.Probability.LayeredSample.Fourier
import CorralFormalization.EndpointProof.Probability.LayeredSample.Augmentation

/-! Fixing one raw sample with exact-matching, all pair banks, all sizes and Fourier. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointMatching.Fractional.Rounding

noncomputable section
universe u

def fourierFailureBound (m : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (4 * (2 * m + 7 : ℕ) : ℝ) * (n : ℝ) * Real.exp (-(ε^2 / 4) * (n : ℝ))

theorem fourierFailureBound_tendsto_zero (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fourierFailureBound m ε) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    1 (ε^2 / 4) (by positivity)).comp tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun n : ℕ =>
      (n : ℝ) * Real.exp (-(ε^2 / 4) * (n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using h
  have hC : Tendsto (fun _n : ℕ => (4 * (2 * m + 7 : ℕ) : ℝ)) atTop
      (𝓝 (4 * (2 * m + 7 : ℕ) : ℝ)) := tendsto_const_nhds
  have hsum := hC.mul h'
  simp only [mul_zero] at hsum
  refine Tendsto.congr ?_ hsum
  intro n
  simp only [fourierFailureBound]
  ring

theorem goodSample_and_fourier_explicitBound
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (ε : ℝ) (hε : 0 ≤ ε)
    (hgood : (sampleMeasure (G := G) d).real
      {s | ¬ GoodSample d (explicitSizeTolerance (Fintype.card G)) s} ≤
        explicitFailureBound d (Fintype.card G)) :
    (sampleMeasure (G := G) d).real
      {s | ¬ (GoodSample d (explicitSizeTolerance (Fintype.card G)) s ∧ FourierEvent d ε s)} ≤
      explicitFailureBound d (Fintype.card G) + fourierFailureBound m ε (Fintype.card G) := by
  have h := goodSample_and_fourier_failure_probability d _ _ ε hε hgood
  simpa only [fourierFailureBound,
    show -ε^2 * (Fintype.card G : ℝ) / 4 = -(ε^2/4) * (Fintype.card G : ℝ) by ring]
    using h

/-- One group-uniform threshold and one fixed actual sample support all
later exact-matching targets, all numerical pair banks and every signed ordinary
Fourier triple.  Generic means are the actual `a` and `c`. -/
theorem exists_goodSample_and_fourier_explicitTolerance
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    {m : ℕ} (d : Densities m) (hq0 : 0 < d.q) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      ∃ s : Sample G m,
        GoodSample d (explicitSizeTolerance (Fintype.card G)) s ∧ FourierEvent d ε s := by
  obtain ⟨N, hN⟩ := goodSample_failure_probability hAKS d hq0
  have hsum : Tendsto (fun n : ℕ => explicitFailureBound d n + fourierFailureBound m ε n)
      atTop (𝓝 0) := by
    simpa only [add_zero] using (explicitFailureBound_tendsto_zero d hq0).add
      (fourierFailureBound_tendsto_zero m ε hε)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      explicitFailureBound d n + fourierFailureBound m ε n < 1 :=
    (tendsto_order.1 hsum).2 1 (by norm_num)
  obtain ⟨Nsmall, hNsmall⟩ := eventually_atTop.1 hsmall
  refine ⟨max N (max Nsmall 1), ?_⟩
  intro G _ _ hodd hn
  let n := Fintype.card G
  have hn0 : 0 < n := by dsimp [n]; omega
  have hp := hN G hodd (by omega) (explicitSizeTolerance n) (explicitSizeTolerance_nonneg n)
  rw [failureBound_explicitSizeTolerance d n hn0] at hp
  have hjoint := goodSample_and_fourier_explicitBound d ε hε.le hp
  have hs : explicitFailureBound d n + fourierFailureBound m ε n < 1 :=
    hNsmall n (by dsimp [n]; omega)
  by_contra hnone
  have heq : {s : Sample G m |
      ¬ (GoodSample d (explicitSizeTolerance n) s ∧ FourierEvent d ε s)} = Set.univ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact fun h => hnone ⟨s, h⟩
  rw [heq, probReal_univ] at hjoint
  linarith

/-- An actual router event on the augmented sample can be joined to the
proved Fourier/layer event by its own displayed failure estimate. -/
theorem augmented_good_fourier_and_event_failure_probability
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (tol ε B e : ℝ)
    (hgood : (sampleMeasure (G := G) d).real
      {s | ¬ (GoodSample d tol s ∧ FourierEvent d ε s)} ≤ B)
    (event : AugmentedSample G m → Prop)
    (hevent : (augmentedMeasure d t ht0 ht1).real {s | ¬ event s} ≤ e) :
    (augmentedMeasure d t ht0 ht1).real
      {s | ¬ (GoodSample d tol (forgetAugmented s) ∧
        FourierEvent d ε (forgetAugmented s) ∧ event s)} ≤ B + e := by
  have hp := forgetAugmented_measurePreserving (G := G) d t ht0 ht1
  rw [← hp.measureReal_preimage (by measurability)] at hgood
  have heq : {s : AugmentedSample G m |
      ¬ (GoodSample d tol (forgetAugmented s) ∧
        FourierEvent d ε (forgetAugmented s) ∧ event s)} =
      (forgetAugmented ⁻¹' {s | ¬ (GoodSample d tol s ∧ FourierEvent d ε s)}) ∪
        {s | ¬ event s} := by
    ext s
    simp only [not_and_or, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  exact (measureReal_union_le _ _).trans (add_le_add hgood hevent)

/-- The error budget gives one actual common augmentation before any of
the later queries internal to the supplied events. -/
theorem exists_goodFourierAugmented_and_event_of_error_lt_one
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (tol ε B e : ℝ)
    (hgood : (sampleMeasure (G := G) d).real
      {s | ¬ (GoodSample d tol s ∧ FourierEvent d ε s)} ≤ B)
    (event : AugmentedSample G m → Prop)
    (hevent : (augmentedMeasure d t ht0 ht1).real {s | ¬ event s} ≤ e)
    (hsmall : B + e < 1) :
    ∃ s : AugmentedSample G m,
      GoodSample d tol (forgetAugmented s) ∧
        FourierEvent d ε (forgetAugmented s) ∧ event s := by
  have hp := augmented_good_fourier_and_event_failure_probability d t ht0 ht1
    tol ε B e hgood event hevent
  by_contra hnone
  have heq : {s : AugmentedSample G m |
      ¬ (GoodSample d tol (forgetAugmented s) ∧
        FourierEvent d ε (forgetAugmented s) ∧ event s)} = Set.univ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact fun hs => hnone ⟨s, hs⟩
  rw [heq, probReal_univ] at hp
  linarith

end
end EndpointLayeredSample
