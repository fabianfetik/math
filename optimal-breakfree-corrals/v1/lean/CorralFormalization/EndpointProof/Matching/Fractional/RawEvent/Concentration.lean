import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Original

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ComplexConjugate NNReal

namespace EndpointFractionalRawEvent
open EndpointOriginalReservoir EndpointFullProduct EndpointFiniteProductConcentration
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Oscillation one for every real weighted coefficient with weights bounded
by one. In particular this covers both real components of every character. -/
theorem weightedCenteredSum_boundedDifferences (q : ℝ) (i : Fin 3) (a : G → ℝ)
    (ha : ∀ g, |a g| ≤ 1) :
    CoordinateBoundedDifferences (weightedCenteredSum q i a) (fun _ => 1) := by
  intro k w w' hw
  have he : weightedCenteredSum q i a w-weightedCenteredSum q i a w' =
      (bit i (w k)-bit i (w' k))*a k := by
    unfold weightedCenteredSum
    rw [← Finset.sum_sub_distrib,Finset.sum_eq_single k]
    · ring
    · intro g _ hg; rw [hw g hg]; ring
    · simp
  rw [he,abs_mul]
  exact mul_le_one₀ (bit_abs_sub_le_one i _ _) (abs_nonneg _) (ha k)

private theorem bit_product_abs_sub (i j : Fin 3) (a b c d : Site) :
    |bit i a*bit j b-bit i c*bit j d| ≤ 1 := by
  have h₁ : 0 ≤ bit i a*bit j b := mul_nonneg (bit_nonneg _ _) (bit_nonneg _ _)
  have h₂ : 0 ≤ bit i c*bit j d := mul_nonneg (bit_nonneg _ _) (bit_nonneg _ _)
  have h₃ : bit i a*bit j b ≤ 1 := mul_le_one₀ (bit_le_one _ _) (bit_nonneg _ _) (bit_le_one _ _)
  have h₄ : bit i c*bit j d ≤ 1 := mul_le_one₀ (bit_le_one _ _) (bit_nonneg _ _) (bit_le_one _ _)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The two factors can share or overlap sites. A site influences at most
two summands since each partner-coordinate map is a permutation. -/
theorem siteProductCount_boundedDifferences (i j : Fin 3) (a b : Equiv.Perm G) :
    CoordinateBoundedDifferences (siteProductCount i j a b) (fun _ => 2) := by
  intro k w w' hw
  unfold siteProductCount
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ g, (bit i (w (a g))*bit j (w (b g))-bit i (w' (a g))*bit j (w' (b g)))|
        ≤ ∑ g, |bit i (w (a g))*bit j (w (b g))-bit i (w' (a g))*bit j (w' (b g))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g, ((if a g=k then (1:ℝ) else 0)+(if b g=k then (1:ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro g _
      have h := bit_product_abs_sub i j (w (a g)) (w (b g)) (w' (a g)) (w' (b g))
      by_cases ha : a g=k <;> by_cases hb : b g=k
      · simp only [ha,hb,ite_true] at h ⊢; linarith
      · simpa only [ha,hb,ite_true,ite_false,add_zero] using h
      · simpa only [ha,hb,ite_true,ite_false,zero_add] using h
      · rw [hw (a g) ha,hw (b g) hb]; simp [ha,hb]
    _ = 2 := by
      rw [Finset.sum_add_distrib]
      simp_rw [← a.eq_symm_apply,← b.eq_symm_apply]
      norm_num

/-- Sensitivity two for every rooted raw degree on the actual regrouped
site process. No independence of different root counts is asserted. -/
theorem rawDegree_boundedDifferences (i : Fin 3) (v : G) :
    CoordinateBoundedDifferences (fun w : SiteSample G => rawDegree (unsites w) i v)
      (fun _ => 2) := by
  let subR : Equiv.Perm G := ⟨fun x => x-v,fun x => x+v,by intro x; simp,by intro x; simp⟩
  let subL : Equiv.Perm G := ⟨fun x => v-x,fun x => v-x,by intro x; simp,by intro x; simp⟩
  let addR : Equiv.Perm G := ⟨fun x => x+v,fun x => x-v,by intro x; simp,by intro x; simp⟩
  fin_cases i
  · simpa [CoordinateBoundedDifferences,rawDegree,rawBit,siteProductCount,subR] using
      siteProductCount_boundedDifferences (G := G) 1 2 (Equiv.refl G) subR
  · simpa [CoordinateBoundedDifferences,rawDegree,rawBit,siteProductCount,subL] using
      siteProductCount_boundedDifferences (G := G) 0 2 (Equiv.refl G) subL
  · simpa [CoordinateBoundedDifferences,rawDegree,rawBit,siteProductCount,addR] using
      siteProductCount_boundedDifferences (G := G) 0 1 (Equiv.refl G) addR

/-- Reusable two-sided sub-Gaussian bound; events need not be independent. -/
theorem twoSided_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ≥0) (h : HasSubgaussianMGF X c μ)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t < |X ω|} ≤ 2*Real.exp (-t^2/(2*c)) := by
  have hu := h.measure_ge_le ht
  have hl := h.neg.measure_ge_le ht
  simp only [Pi.neg_apply] at hl
  have hsub : {ω | t < |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    change t < |X ω| at hω
    change t ≤ X ω ∨ t ≤ -X ω
    rcases lt_abs.mp hω with hω | hω
    · exact Or.inl hω.le
    · exact Or.inr (by linarith)
  calc
    _ ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) :=
      measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real {ω | t ≤ X ω}+μ.real {ω | t ≤ -X ω} := measureReal_union_le _ _
    _ ≤ 2*Real.exp (-t^2/(2*c)) := by linarith

/-- Exact original-law MGF for each real weighted Fourier component. -/
theorem weightedCenteredSum_hasSubgaussianMGF (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (i : Fin 3) (a : G → ℝ) (ha : ∀ g, |a g| ≤ 1) :
    HasSubgaussianMGF (fun s : OriginalSample G => weightedCenteredSum q i a (sites s))
      ((Fintype.card G : ℝ≥0)/4) (originalMeasure q hq0 hq1) := by
  have hs := hasSubgaussianMGF_of_measurePreserving
    (fun _ : G => (siteLaw q hq0 hq1).measure)
    (originalMeasure (G := G) q hq0 hq1) sites (sites_measurePreserving q hq0 hq1)
    (fun _ => 1) (weightedCenteredSum q i a) (weightedCenteredSum_boundedDifferences q i a ha)
  have hi : (∫ s : OriginalSample G, weightedCenteredSum q i a (sites s)
      ∂originalMeasure q hq0 hq1) = 0 := by
    have hp := sites_measurePreserving (G := G) q hq0 hq1
    have h := integral_map (μ := originalMeasure q hq0 hq1) hp.measurable.aemeasurable
      (measurable_of_countable (weightedCenteredSum q i a)).aestronglyMeasurable
    rw [hp.map_eq] at h
    rw [← h,weightedCenteredSum_expectation]
  norm_num [hi,Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv] at hs ⊢
  exact hs

/-- The raw degree center has a conservative common proxy n, covering all
roots and the dependent endpoint colour counts on the same sample. -/
theorem rawDegree_hasSubgaussianMGF (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (i : Fin 3) (v : G) (hv : i=2 → v ≠ 0) :
    HasSubgaussianMGF
      (fun s : OriginalSample G => rawDegree s i v-q^2*(Fintype.card G : ℝ))
      (Fintype.card G : ℝ≥0) (originalMeasure q hq0 hq1) := by
  have hs := hasSubgaussianMGF_of_measurePreserving
    (fun _ : G => (siteLaw q hq0 hq1).measure)
    (originalMeasure (G := G) q hq0 hq1) sites (sites_measurePreserving q hq0 hq1)
    (fun _ => 2) (fun w => rawDegree (unsites w) i v) (rawDegree_boundedDifferences i v)
  simpa [rawDegree_expectation q hq0 hq1 i v hv] using hs

/-- A convenient weakened raw-degree tail in manuscript units. -/
theorem rawDegree_twoSided_tail (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (i : Fin 3) (v : G) (hv : i=2 → v ≠ 0) :
    (originalMeasure (G := G) q hq0 hq1).real
      {s | ρ*(Fintype.card G : ℝ) < |rawDegree s i v-q^2*(Fintype.card G : ℝ)|} ≤
      2*Real.exp (-ρ^2*(Fintype.card G : ℝ)/4) := by
  have hs := rawDegree_hasSubgaussianMGF q hq0 hq1 i v hv
  have h := twoSided_tail _ _ _ hs (ρ*(Fintype.card G : ℝ)) (by positivity)
  have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have he : -(ρ*(Fintype.card G : ℝ))^2/(2*(Fintype.card G : ℝ)) =
      -ρ^2*(Fintype.card G : ℝ)/2 := by field_simp <;> ring
  simp only [NNReal.coe_natCast] at h
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ρ])) (by norm_num))

/-- Bound both real and imaginary Fourier components using the actual
original sample. The factor two threshold leaves a simple union argument. -/
theorem weightedCenteredSum_twoSided_tail (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (i : Fin 3) (a : G → ℝ) (ha : ∀ g, |a g| ≤ 1) :
    (originalMeasure (G := G) q hq0 hq1).real
      {s | ε*(Fintype.card G : ℝ)/2 < |weightedCenteredSum q i a (sites s)|} ≤
      2*Real.exp (-ε^2*(Fintype.card G : ℝ)/4) := by
  have hs := weightedCenteredSum_hasSubgaussianMGF q hq0 hq1 i a ha
  have h := twoSided_tail _ _ _ hs (ε*(Fintype.card G : ℝ)/2) (by positivity)
  have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have he : -(ε*(Fintype.card G : ℝ)/2)^2/(2*((Fintype.card G : ℝ)/4)) =
      -ε^2*(Fintype.card G : ℝ)/2 := by field_simp <;> ring
  simp only [NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat] at h
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ε])) (by norm_num))

end
end EndpointFractionalRawEvent
