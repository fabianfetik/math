import CorralFormalization.EndpointProof.Matching.UniversalCore.SampledCore
import CorralFormalization.EndpointProof.Flow.Tetrahedron.Supplier
import CorralFormalization.EndpointProof.Flow.Tetrahedron.PairedCover
import CorralFormalization.EndpointProof.Flow.Tetrahedron.DeletionAndCounts

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly
open EndpointFullProduct
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- From concrete paired-cover tetrahedron parameter supply, through the actual
4(r-1)-pair cover, to one fixed absorbing core on the same sample. The
graph, buffers, Q counts and numerical budgets remain explicit inputs. -/
theorem sampled_core_of_tetrahedron_parameters {ι : Type*} [DecidableEq ι]
    (hodd : Odd (Fintype.card G)) (ω : FullSample G)
    (pBudget qBudget capacity K : ℕ) (U : Finset G)
    (hlocal : ColouredSelectors ω pBudget)
    (hparameters : EndpointMatching.Tetrahedron.TetrahedronParametersAvailable
      (ReservoirVertex ω true) qBudget)
    (hcoverBudget : 2 * U.card + 20 * capacity ≤ qBudget)
    (hK : 4 * capacity ≤ 3 * K)
    (hquery : ∀ p, let Q := availablePairInventory (ReservoirVertex ω true) U p
      1 ≤ Q.card - K ∧ Q.card - K ≤ Q.card ∧ Q.card ≤ 2 * (Q.card - K) ∧
        Nonempty (ContiguousSelectionGraph (Q.card - K) 16))
    (hbudget :
      let Q := availablePairInventory (ReservoirVertex ω true) U
      2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
        ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
          1724 * ((Q p).card - K)) ≤ pBudget)
    (buffers : Finset ι) (pick : ι → Fin 3 → Finset (Vertex G))
    (hBmem : ∀ i ∈ buffers, ∀ p, pick i p ∈
      availablePairInventory (ReservoirVertex ω true) U p)
    (hBunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hBmatch : ∀ i ∈ buffers, Nonempty (Matching (Finset.univ.biUnion (pick i))))
    (hcount : 3 * K ≤ buffers.card) :
    ∃ A : Finset (Vertex G),
      (∀ v ∈ A, v.2 ≠ 0 ∧ EndpointFullProduct.originalSigned v.1
        (EndpointFullProduct.originalProcess ω) v.2) ∧
      Disjoint (support A) U ∧
      A.card ≤ (∑ p : Fin 3, 862 *
        ((availablePairInventory (ReservoirVertex ω true) U p).card - K)) +
        ∑ p : Fin 3, 2 * (availablePairInventory (ReservoirVertex ω true) U p).card ∧
      AbsorbsUpTo A capacity := by
  have hsupply := EndpointMatching.Tetrahedron.fourPairSupplier_of_parameters
    (ReservoirVertex ω true) qBudget hparameters
  have hcovers := EndpointMatching.Tetrahedron.fourThirdsCovers_of_fourPairSupplier_abelian
    G (inferInstance : AddCommGroup G) hodd (ReservoirVertex ω true) qBudget hsupply
  exact sampled_core_of_fourThirds_covers hodd ω pBudget qBudget capacity K U
    hlocal hcovers hcoverBudget hK hquery hbudget buffers pick hBmem hBunique hBmatch hcount


/-- The same core follows from total and section counts for the actual
Q-labelled tetrahedron candidates. The count estimates remain premises. -/
theorem sampled_core_of_tetrahedron_counts {ι : Type*} [DecidableEq ι]
    (hodd : Odd (Fintype.card G)) (ω : FullSample G)
    (pBudget qBudget capacity K : ℕ) (U : Finset G)
    (hlocal : ColouredSelectors ω pBudget)
    (τ n : ℝ) (hτ : 0 < τ) (hn : 0 < n)
    (hdeletion : (qBudget : ℝ) ≤ τ^2 * n / 192)
    (htotal : ∀ r : CorralFormalization.EndpointProof.Probability.QuadraticDeletion.TetrahedronRoots G,
      EndpointMatching.Tetrahedron.admissibleRoots r →
      τ^12 * n^3 / 2 ≤
        ((EndpointMatching.Tetrahedron.goodCandidates (ReservoirVertex ω true) r).card : ℝ))
    (hsection : ∀ r : CorralFormalization.EndpointProof.Probability.QuadraticDeletion.TetrahedronRoots G,
      EndpointMatching.Tetrahedron.admissibleRoots r → ∀ i g,
      (((EndpointMatching.Tetrahedron.goodCandidates (ReservoirVertex ω true) r).filter
        (fun t => CorralFormalization.EndpointProof.Probability.QuadraticDeletion.tetrahedronDirection i t = g)).card : ℝ) ≤
          2 * τ^10 * n^2)
    (hcoverBudget : 2 * U.card + 20 * capacity ≤ qBudget)
    (hK : 4 * capacity ≤ 3 * K)
    (hquery : ∀ p, let Q := availablePairInventory (ReservoirVertex ω true) U p
      1 ≤ Q.card - K ∧ Q.card - K ≤ Q.card ∧ Q.card ≤ 2 * (Q.card - K) ∧
        Nonempty (ContiguousSelectionGraph (Q.card - K) 16))
    (hbudget :
      let Q := availablePairInventory (ReservoirVertex ω true) U
      2 * (U ∪ support ((Finset.univ.biUnion Q).biUnion id)).card +
        ∑ p : Fin 3, (2 * (2 * (862 * ((Q p).card - K))) +
          1724 * ((Q p).card - K)) ≤ pBudget)
    (buffers : Finset ι) (pick : ι → Fin 3 → Finset (Vertex G))
    (hBmem : ∀ i ∈ buffers, ∀ p, pick i p ∈
      availablePairInventory (ReservoirVertex ω true) U p)
    (hBunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hBmatch : ∀ i ∈ buffers, Nonempty (Matching (Finset.univ.biUnion (pick i))))
    (hcount : 3 * K ≤ buffers.card) :
    ∃ A : Finset (Vertex G),
      (∀ v ∈ A, v.2 ≠ 0 ∧ EndpointFullProduct.originalSigned v.1
        (EndpointFullProduct.originalProcess ω) v.2) ∧
      Disjoint (support A) U ∧
      A.card ≤ (∑ p : Fin 3, 862 *
        ((availablePairInventory (ReservoirVertex ω true) U p).card - K)) +
        ∑ p : Fin 3, 2 * (availablePairInventory (ReservoirVertex ω true) U p).card ∧
      AbsorbsUpTo A capacity := by
  have hparameters := EndpointMatching.Tetrahedron.parameters_available_of_section_counts
    (ReservoirVertex ω true) qBudget τ n hτ hn hdeletion htotal hsection
  exact sampled_core_of_tetrahedron_parameters hodd ω pBudget qBudget capacity K U
    hlocal hparameters hcoverBudget hK hquery hbudget buffers pick hBmem hBunique hBmatch hcount

end
end EndpointMatching.UniversalCore
