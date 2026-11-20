import CorralFormalization.EndpointProof.Probability.LayeredSample.ExactMatching
import CorralFormalization.EndpointProof.Probability.LayeredSample.PairSupply

/-!
A common categorical sample for the uniform exact-matching theorem, actual pair banks and all raw sizes.
Any further Fourier/router supplier must be established on this same law
(or on an explicitly specified augmentation of it).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

set_option autoImplicit false

namespace EndpointLayeredSample

open EndpointMatching.Fractional.Rounding
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section
universe u

def GoodSample {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (t : ℝ) (s : Sample G m) : Prop :=
  ExactMatchingEvent d s ∧ PairSupplyEvent d s ∧ SizeEvent d t s

def failureBound {m : ℕ} (d : Densities m) (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((xi d.q)^4 / 10^6) * (n : ℝ)) +
  (n : ℝ) * Real.exp (-d.q^4 * (n : ℝ) / 8) +
  (2 * (2 * m + 7 : ℕ) : ℝ) * Real.exp (-t^2 / (2 * ((n : ℝ) / 4)))

/-- A single group-type-uniform threshold pays exact-matching, pair supply and every
raw size on one categorical sample.  Neither independent roles nor
independent good events are assumed. -/
theorem goodSample_failure_probability
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    {m : ℕ} (d : Densities m) (hq0 : 0 < d.q) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      ∀ t : ℝ, 0 ≤ t →
      (sampleMeasure (G := G) d).real {s | ¬ GoodSample d t s} ≤
        failureBound d t (Fintype.card G) := by
  obtain ⟨N, hN⟩ := exactMatchingEvent_failure_probability hAKS d hq0
  refine ⟨max N 4, ?_⟩
  intro G _ _ hodd hn t ht
  let μ := sampleMeasure (G := G) d
  have hE := hN G hodd (by omega)
  have hP := pairSupplyEvent_failure_probability (G := G) d (by omega)
  have hS := sizeEvent_failure_probability (G := G) d t ht
  have heq : {s : Sample G m | ¬ GoodSample d t s} =
      ({s | ¬ ExactMatchingEvent d s} ∪ {s | ¬ PairSupplyEvent d s}) ∪
        {s | ¬ SizeEvent d t s} := by
    ext s; simp only [GoodSample, not_and_or, Set.mem_union, Set.mem_ofPred_eq]; tauto
  rw [heq]
  calc
    μ.real (({s | ¬ ExactMatchingEvent d s} ∪ {s | ¬ PairSupplyEvent d s}) ∪
        {s | ¬ SizeEvent d t s}) ≤
      μ.real ({s | ¬ ExactMatchingEvent d s} ∪ {s | ¬ PairSupplyEvent d s}) +
        μ.real {s | ¬ SizeEvent d t s} := measureReal_union_le _ _
    _ ≤ (μ.real {s | ¬ ExactMatchingEvent d s} + μ.real {s | ¬ PairSupplyEvent d s}) +
        μ.real {s | ¬ SizeEvent d t s} := add_le_add (measureReal_union_le _ _) (le_refl _)
    _ ≤ failureBound d t (Fintype.card G) := add_le_add (add_le_add hE hP) hS

/-- Finite suppliers on the actual sample can be conjoined by their
failure bounds.  Each supplier may itself quantify over all later targets;
those targets are never indices of this union bound. -/
theorem finiteEvents_failure_probability {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) {T : Type*} [Fintype T]
    (events : T → Sample G m → Prop) (error : T → ℝ)
    (herror : ∀ i, (sampleMeasure d).real {s | ¬ events i s} ≤ error i) :
    (sampleMeasure d).real {s | ¬ ∀ i, events i s} ≤ ∑ i, error i := by
  have heq : {s : Sample G m | ¬ ∀ i, events i s} = ⋃ i, {s | ¬ events i s} := by
    ext s; simp only [not_forall, Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [heq]
  exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun i _ => herror i)

/-- The sample witnessing every event is chosen before all target choices
internal to these events.  The premise is only an explicit strict error
budget, so no target or factor-existence assertion is smuggled in. -/
theorem exists_common_sample_of_error_lt_one {G : Type*} [Fintype G] {m : ℕ}
    (d : Densities m) {T : Type*} [Fintype T]
    (events : T → Sample G m → Prop) (error : T → ℝ)
    (herror : ∀ i, (sampleMeasure d).real {s | ¬ events i s} ≤ error i)
    (htotal : ∑ i, error i < 1) :
    ∃ s : Sample G m, ∀ i, events i s := by
  have hp := finiteEvents_failure_probability d events error herror
  by_contra hnone
  have heq : {s : Sample G m | ¬ ∀ i, events i s} = Set.univ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact fun hs => hnone ⟨s, hs⟩
  rw [heq, probReal_univ] at hp
  linarith

/-- An established common event can be combined with any further finite
set of supplied events on the same sample. -/
theorem goodSample_and_finiteEvents_failure_probability
    {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}
    (d : Densities m) (t B : ℝ)
    (hgood : (sampleMeasure (G := G) d).real {s | ¬ GoodSample d t s} ≤ B)
    {T : Type*} [Fintype T] (events : T → Sample G m → Prop) (error : T → ℝ)
    (herror : ∀ i, (sampleMeasure d).real {s | ¬ events i s} ≤ error i) :
    (sampleMeasure d).real {s | ¬ (GoodSample d t s ∧ ∀ i, events i s)} ≤
      B + ∑ i, error i := by
  have heq : {s : Sample G m | ¬ (GoodSample d t s ∧ ∀ i, events i s)} =
      {s | ¬ GoodSample d t s} ∪ {s | ¬ ∀ i, events i s} := by
    ext s; simp only [not_and_or, Set.mem_union, Set.mem_ofPred_eq]
  rw [heq]
  exact (measureReal_union_le _ _).trans
    (add_le_add hgood (finiteEvents_failure_probability d events error herror))

end
end EndpointLayeredSample
