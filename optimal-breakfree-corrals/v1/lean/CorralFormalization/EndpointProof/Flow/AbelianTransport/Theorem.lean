import CorralFormalization.EndpointProof.Flow.AbelianTransport.CompatibleRing
import CorralFormalization.EndpointProof.Flow.AbelianTransport.AdditiveModel

/-!
Complete selector/paired-cover for the specified finite abelian group and its original
sampling model. A compatible ring is obtained internally before applying
the proved ring theorem; the resulting statement has no ring hypothesis.
-/

open MeasureTheory
open scoped Classical

namespace EndpointFlow.AbelianTransport

open EndpointFullProduct
open CorralFormalization.EndpointProof.RateBudget
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

/-- Equality of the entire additive structure identifies the augmented
sample and all numerical operations. The same witnesses are retained. -/
theorem additive_selectors_sixRoots_and_covers_of_compatible_ring
    (G : Type*) [ft : Fintype G] (A : AddCommGroup G) (ring : CommRing G)
    (hcompat : ring.toAddCommGroup = A) (externalBudget qBudget : ℕ)
    (s : OriginalSample G)
    (hgood : @EndpointFullProduct.OriginalAdmitsSelectorsSixRootsAndCovers G ring ft externalBudget qBudget s) :
    @OriginalAdmitsSelectorsSixRootsAndCovers G ft A externalBudget qBudget s := by
  cases hcompat
  exact additive_selectors_sixRoots_and_covers_of_ring hgood

/-- Literal exact-matching law and parameters on every finite abelian group of odd
order. The AddCommGroup supplied by the caller is the one used by the native
sample, reservoirs, inverse pairs, zero-sum hyperedges and final outputs.
There is no ring choice or existence hypothesis in this statement. -/
theorem original_selectors_sixRoots_and_covers_probability_abelian
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G]
      (hodd : Odd (Fintype.card G)) (hn : max N 2000 ≤ Fintype.card G),
      (originalMeasure q (le_of_lt hq0) hq1).real
        {s : OriginalSample G | ¬ OriginalAdmitsSelectorsSixRootsAndCovers
          (selectorExternalBudget (p q) (Fintype.card G))
          (flowBudget (tau q) (Fintype.card G)) s} ≤
        Real.exp (-((xi q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := EndpointFullProduct.original_selectors_sixRoots_and_covers_probability q hq0 hq1
  refine ⟨N,?_⟩
  intro G A ft hodd hn
  obtain ⟨ring,hcompat⟩ := exists_compatible_commRing G
  have hbase := @hN G ring ft hodd hn
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbase
  intro s hbad hgood
  exact hbad (additive_selectors_sixRoots_and_covers_of_compatible_ring G A ring hcompat _ _ s hgood)

end
end EndpointFlow.AbelianTransport
