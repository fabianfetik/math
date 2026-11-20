import CorralFormalization.EndpointProof.Probability.SelectorsAndSixRootSupply
import CorralFormalization.EndpointProof.Flow.Cover.Iteration

/-!
Complete selectors, paired-cover six-root supply, and paired covers on one
original sample and one augmentation, with the paper's final error exponent.
The later absorber, uniform matching, factor supply and endpoint theorem are
not asserted here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace EndpointFullProduct

open EndpointSelector EndpointSelector.Assembly
open EndpointFlow EndpointFlow.Cover
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- One sample provides a paired cover for every later paired-cover input and every
later numerical forbidden set within the stated budget. -/
def PairedCoversAvailable (ω : FullSample G) (budget : ℕ) : Prop :=
  ∀ (S : Finset (EndpointSelector.Vertex G)), Balanced S → (∀ v ∈ S, v.2 ≠ 0) →
    (∑ v ∈ S, v.2 = 0) → ∀ U : Finset G,
      2 * U.card + 20 * S.card ≤ budget →
        Nonempty (PairedCoverResult (QVertex ω) S U)

theorem pairedCovers_of_sixRootSupplier
    (hodd : Odd (Fintype.card G)) (ω : FullSample G) (budget : ℕ)
    (hflow : SixRootSupplier (QVertex ω) budget) :
    PairedCoversAvailable ω budget := by
  intro S hb hnz hsum U hbudget
  exact paired_cover_of_sixRootSupplier hodd (QVertex ω) budget hflow S hb hnz hsum U hbudget

/-- The same original sample and augmentation provide selectors, every
six-root query, and every paired cover, before any later choice of targets. -/
def OriginalAdmitsSelectorsSixRootsAndCovers (externalBudget qBudget : ℕ) (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧
    ColouredSelectors ω externalBudget ∧
    SixRootSupplier (QVertex ω) qBudget ∧ PairedCoversAvailable ω qBudget

/-- Literal exact-matching parameters, selector and packing-budget budgets, and the final error exponent.
The finite odd commutative-ring domain includes the cyclic groups of the
corral paper; a general abstract abelian-group formalization is not claimed. -/
theorem original_selectors_sixRoots_and_covers_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [CommRing G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsSelectorsSixRootsAndCovers
          (selectorExternalBudget (p q) (Fintype.card G))
          (flowBudget (tau q) (Fintype.card G)) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_selectors_and_sixRoots_probability q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  have hbound := hN G hodd hn
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbound
  intro s hbad hgood
  obtain ⟨ω,hω,hselectors,hflow⟩ := hgood
  exact hbad ⟨ω,hω,hselectors,hflow,
    pairedCovers_of_sixRootSupplier hodd ω (flowBudget (tau q) (Fintype.card G)) hflow⟩

/-- The written real packing-budget budget is equivalent to the integer floor budget
used by the common availability theorem. -/
theorem pairedCovers_of_real_budget
    (q : ℝ) (ω : FullSample G)
    (hcover : PairedCoversAvailable ω (flowBudget (tau q) (Fintype.card G)))
    (S : Finset (EndpointSelector.Vertex G)) (hb : Balanced S) (hnz : ∀ v ∈ S, v.2 ≠ 0)
    (hsum : ∑ v ∈ S, v.2 = 0) (U : Finset G)
    (hbudget : 2 * (U.card : ℝ) + 20 * (S.card : ℝ) ≤
      (tau q)^9 * (Fintype.card G : ℝ) / 10^6) :
    Nonempty (PairedCoverResult (QVertex ω) S U) := by
  have htau : 0 ≤ tau q := by unfold tau p rho eta; positivity
  have hint : 2 * U.card + 20 * S.card ≤ flowBudget (tau q) (Fintype.card G) := by
    apply (le_flowBudget_iff (tau q) (Fintype.card G) _ htau).2
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hbudget
  exact hcover S hb hnz hsum U hint

/-- Expand the same original-sample witness into the written real-budget
interfaces for both selector and paired-cover. The augmentation is chosen once, before
all selectors, forbidden sets and paired-cover inputs. Every selected P/Q
vertex is also in the original signed sample. -/
theorem original_selectors_sixRoots_and_covers_witness_real
    (q : ℝ) (s : OriginalSample G)
    (hgood : OriginalAdmitsSelectorsSixRootsAndCovers
      (selectorExternalBudget (p q) (Fintype.card G))
      (flowBudget (tau q) (Fintype.card G)) s) :
    ∃ ω : FullSample G, originalProcess ω = s ∧
      (∀ (part : Fin 3) (R : Finset (Finset (EndpointSelector.Vertex G))),
        R.Nonempty → R.card ≤ 100 → (∀ T ∈ R, LegalPair part T) →
        ∀ F : Finset G, (F.card : ℝ) ≤ (p q)^4 * (Fintype.card G : ℝ) / 10^12 →
          ∃ T : SelectorOn (PVertex ω) R,
            T.interior.card ≤ 18 * R.card - 2 ∧
            Disjoint (numericalSupport T.interior) F ∧
            (numericalSupport (T.interior ∪ R.biUnion id)).card ≤ 3996 ∧
            (∀ v ∈ T.interior, originalSigned v.1 s v.2)) ∧
      (∀ (S : Finset (EndpointSelector.Vertex G)), Balanced S →
        (∀ v ∈ S, v.2 ≠ 0) → (∑ v ∈ S, v.2 = 0) → ∀ U : Finset G,
        2 * (U.card : ℝ) + 20 * (S.card : ℝ) ≤
          (tau q)^9 * (Fintype.card G : ℝ) / 10^6 →
        ∃ C : PairedCoverResult (QVertex ω) S U,
          ∀ v ∈ C.added, originalSigned v.1 s v.2) := by
  obtain ⟨ω,hω,hselectors,_,hcovers⟩ := hgood
  refine ⟨ω,hω,?_,?_⟩
  · intro part R hne hk hlegal F hF
    have hf : F.card ≤ selectorExternalBudget (p q) (Fintype.card G) :=
      (le_selectorExternalBudget_iff (p q) (Fintype.card G) F.card).2 hF
    obtain ⟨T,hsize,havoid,hsupport⟩ := hselectors part R hne hk hlegal F hf
    refine ⟨T,hsize,havoid,hsupport,?_⟩
    intro v hv
    rw [← hω]
    exact pVertex_originalSigned ω v (T.inside v hv)
  · intro S hb hnz hsum U hbudget
    obtain ⟨C⟩ := pairedCovers_of_real_budget q ω hcovers S hb hnz hsum U hbudget
    refine ⟨C,?_⟩
    intro v hv
    rw [← hω]
    exact qVertex_originalSigned ω v (C.added_Q v hv)

/-- Literal cyclic-group specialization used in the corral manuscript. -/
theorem cyclic_selectors_sixRoots_and_covers_probability
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n] (hodd : Odd n) (hn : max N 2000 ≤ n),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample (ZMod n) | ¬ OriginalAdmitsSelectorsSixRootsAndCovers
          (selectorExternalBudget (p q) n) (flowBudget (tau q) n) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * n) := by
  obtain ⟨N,hN⟩ := original_selectors_sixRoots_and_covers_probability q hq0 hq1
  refine ⟨N, ?_⟩
  intro n _ hodd hn
  have hodd' : Odd (Fintype.card (ZMod n)) := by simpa only [ZMod.card] using hodd
  have hn' : max N 2000 ≤ Fintype.card (ZMod n) := by simpa only [ZMod.card] using hn
  simpa only [ZMod.card] using hN (ZMod n) hodd' hn'

end
end EndpointFullProduct
