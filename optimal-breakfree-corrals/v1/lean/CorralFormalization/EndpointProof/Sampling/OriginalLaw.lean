import CorralFormalization.EndpointProof.Sampling.FullProduct

/-! The original vertex/colour law after forgetting every auxiliary coin. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace EndpointFullProduct

open EndpointOriginalReservoir

noncomputable section

def originalAt (s : Coordinate) : Part × Bool := (s.1, s.2.1)

theorem coordinate_original_measurePreserving
    (q η : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    MeasurePreserving originalAt (coordinateLaw q η hq0 hq1 hη0 hη1).measure
      ((vertexLaw q hq0 hq1).measure.prod (coinLaw q hq0 (by linarith)).measure) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← finiteLaw_measure_prod]
  apply Measure.ext_of_measureReal_singleton
  rintro ⟨v, c⟩
  rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton _)]
  change (coordinateLaw q η hq0 hq1 hη0 hη1).measure.real
      {s | originalAt s = (v, c)} =
    ((vertexLaw q hq0 hq1).prod (coinLaw q hq0 (by linarith))).measure.real
      {s | s = (v, c)}
  rw [FiniteLaw.real_event, FiniteLaw.real_event, eventMass_eq]
  simp only [coordinateLaw_weight, originalAt, Prod.mk.injEq]
  rw [original_vertex_colour_joint_mass]
  rfl

variable {G : Type*} [Fintype G] [AddCommGroup G]

abbrev OriginalSample (G : Type*) := (G → Part) × (G → Bool)

def originalProcess (ω : FullSample G) : OriginalSample G :=
  (fun g ↦ (ω.1 g).1, fun g ↦ (ω.1 g).2.1)

/-- Exactly the source law of the uniform exact-matching theorem: a G-indexed categorical vertex process,
and an independent G-indexed Bernoulli colour process, both including zero. -/
def originalMeasure (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    Measure (OriginalSample G) :=
  (Measure.pi fun _ : G ↦ (vertexLaw q hq0 hq1).measure).prod
    (Measure.pi fun _ : G ↦ (coinLaw q hq0 (by linarith)).measure)

instance originalMeasure_probability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    IsProbabilityMeasure (originalMeasure (G := G) q hq0 hq1) := by
  unfold originalMeasure
  infer_instance

/-- No premise specifies a law for regrouped variables. This pushforward is
derived from the actual original G-coordinate product and independent coins. -/
theorem originalProcess_measurePreserving
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    MeasurePreserving (originalProcess (G := G))
      (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab)
      (originalMeasure q hq0 hq1) := by
  have hpi := measurePreserving_pi
    (fun _ : G ↦ (coordinateLaw q η hq0 hq1 hη0 hη1).measure)
    (fun _ : G ↦ (vertexLaw q hq0 hq1).measure.prod
      (coinLaw q hq0 (by linarith)).measure)
    (fun _ ↦ coordinate_original_measurePreserving q η hq0 hq1 hη0 hη1)
  have hsplit := measurePreserving_arrowProdEquivProdArrow Part Bool G
    (fun _ ↦ (vertexLaw q hq0 hq1).measure)
    (fun _ ↦ (coinLaw q hq0 (by linarith)).measure)
  exact (hsplit.comp hpi).comp measurePreserving_fst

/-- The original signed sets used in the packed availability lemma. -/
def originalSigned (part : Part) (s : OriginalSample G) (g : G) : Prop :=
  if part = 0 then s.1 (-g) = 0
  else if part = 1 then s.1 g = 1 else s.2 (-g) = true

theorem signedMinus_subset_originalSigned (part : Part) (ω : FullSample G) (g : G)
    (h : signedMinus part ω g) : originalSigned part (originalProcess ω) g := by
  fin_cases part <;> simp_all [signedMinus, rawMinus, originalRole, originalSigned,
    originalProcess]

omit [Fintype G] in
theorem original_signed_vertex_disjoint (s : OriginalSample G) (g : G) :
    ¬ (originalSigned 0 s (-g) ∧ originalSigned 1 s g) := by
  simp only [originalSigned, ↓reduceIte, neg_neg]
  rintro ⟨h0, h1⟩
  have he := h0.symm.trans h1
  norm_num at he

end
end EndpointFullProduct
