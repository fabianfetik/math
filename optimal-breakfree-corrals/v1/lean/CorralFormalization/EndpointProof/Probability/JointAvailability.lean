import CorralFormalization.EndpointProof.Sampling.FullAvailability

/-!
Finite conjunction of independently established events on one actual
augmented source sample, followed by projection to the original law.

This is a union-bound and quantifier-order theorem. It does not establish
any of the supplied primitive events, candidate packings, or matching claims.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFullProduct

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The same augmentation of the same original sample satisfies every event. -/
def OriginalAdmitsEvents {T : Type*} (events : T → FullSample G → Prop)
    (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧ ∀ i, events i ω

/-- Two events hold on one common augmentation, not on separately chosen
augmentations. Each event may itself quantify over all later queries. -/
def OriginalAdmitsBoth (A B : FullSample G → Prop) (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧ A ω ∧ B ω

/-- A single original-sample event supports all finitely many augmented
events, with the union of their individual failure bounds. In particular,
the augmentation is chosen before every event index and before any later
query quantified within an event. No event-independence is assumed. -/
theorem original_sample_admits_finite_events {T : Type*} [Fintype T]
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1)
    (events : T → FullSample G → Prop) (error : T → ℝ)
    (herror : ∀ i, (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
      {ω | ¬ events i ω} ≤ error i) :
    (originalMeasure q hq0 hq1).real
      {s : OriginalSample G | ¬ OriginalAdmitsEvents events s} ≤ ∑ i, error i := by
  have hp := originalProcess_measurePreserving (G := G)
    q η a b hq0 hq1 hη0 hη1 ha hb hab
  rw [← hp.measureReal_preimage (by measurability)]
  calc
    (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
        (originalProcess ⁻¹' {s : OriginalSample G | ¬ OriginalAdmitsEvents events s})
      ≤ (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
          (⋃ i, {ω | ¬ events i ω}) := by
            apply measureReal_mono ?_ (measure_ne_top _ _)
            intro ω hbad
            by_contra hnot
            have hall : ∀ i, events i ω := by
              intro i
              by_contra hi
              exact hnot (Set.mem_iUnion.mpr ⟨i, hi⟩)
            exact hbad ⟨ω, rfl, hall⟩
    _ ≤ ∑ i, (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
          {ω | ¬ events i ω} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, error i := Finset.sum_le_sum (fun i _ ↦ herror i)

/-- Two-event form of the common augmentation projection, with the sum of
the failure bounds. Neither independence nor a second resampling is used. -/
theorem original_sample_admits_two_events
    (q η a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1)
    (A B : FullSample G → Prop) (u v : ℝ)
    (hA : (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real {ω | ¬ A ω} ≤ u)
    (hB : (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real {ω | ¬ B ω} ≤ v) :
    (originalMeasure q hq0 hq1).real
      {s : OriginalSample G | ¬ OriginalAdmitsBoth A B s} ≤ u + v := by
  have hp := originalProcess_measurePreserving (G := G)
    q η a b hq0 hq1 hη0 hη1 ha hb hab
  rw [← hp.measureReal_preimage (by measurability)]
  calc
    (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
        (originalProcess ⁻¹' {s : OriginalSample G | ¬ OriginalAdmitsBoth A B s})
      ≤ (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real
          ({ω | ¬ A ω} ∪ {ω | ¬ B ω}) := by
            apply measureReal_mono ?_ (measure_ne_top _ _)
            intro ω hbad
            by_contra hnot
            have hAω : A ω := by
              by_contra h
              exact hnot (Or.inl h)
            have hBω : B ω := by
              by_contra h
              exact hnot (Or.inr h)
            exact hbad ⟨ω, rfl, hAω, hBω⟩
    _ ≤ (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real {ω | ¬ A ω} +
        (fullMeasure q η a b hq0 hq1 hη0 hη1 ha hb hab).real {ω | ¬ B ω} :=
          measureReal_union_le _ _
    _ ≤ u + v := add_le_add hA hB

end
end EndpointFullProduct
