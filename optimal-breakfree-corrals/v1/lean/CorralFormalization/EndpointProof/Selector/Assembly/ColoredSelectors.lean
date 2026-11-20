import CorralFormalization.EndpointProof.Selector.Assembly.TaggedPairs
import CorralFormalization.EndpointProof.Selector.PrimitiveAvailability

/-!
The quantified selector consumer on one sample. The small-selector supplier is
kept explicit until the concrete star/path producer is connected.
-/

open MeasureTheory
open scoped Classical

namespace EndpointSelector.Assembly

open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- All tagged parts, all later legal target families with 1≤k≤100, then all
later external numerical supports. Every target uses one common interior. -/
def ColouredSelectors (ω : FullSample G) (C : ℕ) : Prop :=
  ∀ (part : Fin 3) (R : Finset (Finset (Vertex G))),
    R.Nonempty → R.card ≤ 100 → (∀ T ∈ R, LegalPair part T) →
    ∀ (F : Finset G), F.card ≤ C →
    ∃ S : SelectorOn (PVertex ω) R,
      S.interior.card ≤ 18*R.card-2 ∧
      Disjoint (numericalSupport S.interior) F ∧
      (numericalSupport (S.interior ∪ R.biUnion id)).card ≤ 3996

def OriginalAdmitsColouredSelectors (C : ℕ) (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧ ColouredSelectors ω C

/-- The generic recursion already pays every small-query reserve and proves
the exact numerical support accounting. The same one-star primitive supplies
the P helpers, so no P-count event is invoked. -/
theorem coloured_selectors_of_small_supply
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget C : ℕ) (hmargin : C+3996 ≤ budget) (ω : FullSample G)
    (hprimitive : ∀ i, selectorPrimitiveEvents hodd hn budget i ω)
    (hsmall : ∀ part : Fin 3, SmallSupply (PVertex ω) (LegalPair part) budget) :
    ColouredSelectors ω C := by
  intro part R hne hk hlegal F hF
  have hh : HelperSupply (PVertex ω) (LegalPair part) budget :=
    helperSupply_of_rotated_star_available hodd hn budget ω
      (by simpa [selectorPrimitiveEvents] using hprimitive (1 : Fin 4)) part
  exact colouredSelector_of_primitive_suppliers (PVertex ω) (LegalPair part)
    (legalPair_rootDomain part) budget C (hsmall part) hh hmargin R hne hk hlegal F hF

/-- The existential augmentation is outside every part, root-family, target,
and forbidden-support query. This preserves the essential selector quantifiers. -/
theorem one_augmentation_all_selectors_of_small_supply
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget C : ℕ) (hmargin : C+3996 ≤ budget)
    (hsmall : ∀ (ω : FullSample G),
      (∀ i, selectorPrimitiveEvents hodd hn budget i ω) →
      ∀ part : Fin 3, SmallSupply (PVertex ω) (LegalPair part) budget)
    (s : OriginalSample G)
    (hgood : OriginalAdmitsEvents (selectorPrimitiveEvents hodd hn budget) s) :
    OriginalAdmitsColouredSelectors C s := by
  obtain ⟨ω,hω,hprimitive⟩ := hgood
  exact ⟨ω,hω,coloured_selectors_of_small_supply hodd hn budget C hmargin ω hprimitive
    (hsmall ω hprimitive)⟩

/-- The deterministic implication transfers the probability bound by event
inclusion, with no additional union bound over targets or forbidden sets. -/
theorem original_selector_failure_le_primitive_failure
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2)
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget C : ℕ) (hmargin : C+3996 ≤ budget)
    (hsmall : ∀ (ω : FullSample G),
      (∀ i, selectorPrimitiveEvents hodd hn budget i ω) →
      ∀ part : Fin 3, SmallSupply (PVertex ω) (LegalPair part) budget) :
    (originalMeasure q hq0 hq1).real {s : OriginalSample G |
      ¬ OriginalAdmitsColouredSelectors C s} ≤
    (originalMeasure q hq0 hq1).real {s : OriginalSample G |
      ¬ OriginalAdmitsEvents (selectorPrimitiveEvents hodd hn budget) s} := by
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro s hs hgood
  exact hs (one_augmentation_all_selectors_of_small_supply hodd hn budget C hmargin
    hsmall s hgood)

/-- Reservoir membership supplies the original signed vertices on the same
original sample as the augmentation. Root pairs are not required to lie in P. -/
theorem selector_in_original_model {C : ℕ} {s : OriginalSample G}
    (hgood : OriginalAdmitsColouredSelectors C s) :
    ∃ ω : FullSample G, originalProcess ω = s ∧
      ∀ (part : Fin 3) (R : Finset (Finset (Vertex G))),
        R.Nonempty → R.card ≤ 100 → (∀ T ∈ R, LegalPair part T) →
        ∀ (F : Finset G), F.card ≤ C →
        ∃ S : SelectorOn (PVertex ω) R,
          S.interior.card ≤ 18*R.card-2 ∧
          Disjoint (numericalSupport S.interior) F ∧
          (∀ v ∈ S.interior, originalSigned v.1 s v.2) := by
  obtain ⟨ω,hω,hselectors⟩ := hgood
  refine ⟨ω,hω,?_⟩
  intro part R hne hk hlegal F hF
  obtain ⟨S,hI,hF,hSupp⟩ := hselectors part R hne hk hlegal F hF
  refine ⟨S,hI,hF,?_⟩
  intro v hv
  rw [← hω]
  exact pVertex_originalSigned ω v (S.inside v hv)

end
end EndpointSelector.Assembly
