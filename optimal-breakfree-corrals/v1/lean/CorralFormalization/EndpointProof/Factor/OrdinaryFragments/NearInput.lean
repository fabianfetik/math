import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Counts

/-!
# ordinary transition lemma's actual near matchings feed the ordinary decomposition

The input is the physical conclusion of the ordinary transition lemma on the actual adjacent layer
and colour-pool triples. Covered tail/head/colour sets and the matching are
chosen from those conclusions; they are not hypotheses of a perfect factor.
-/

open scoped Classical BigOperators
namespace EndpointFactor.OrdinaryFragments
open EndpointMatching.AbsorptionAssembly EndpointLayeredSample
noncomputable section
universe u
variable {G : Type u} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- The paper's ordinary physical triple, with no checksum requirement. -/
def ordinaryTarget {j : ℕ} (L : Fin (j+1) → Finset G)
    (C : Fin j → Finset G) (i : Fin j) :
    EndpointFractionalRawEvent.PhysicalTarget G :=
  ![L i.castSucc, L i.succ, C i]

/-- Every near matching produces its true covered sets, actual matching,
colour disjointness, nonzero colours and true deficit, simultaneously for
all ordinary transitions. -/
theorem exists_layerData_of_near {j ℓ : ℕ}
    (L : Fin (j+1) → Finset G) (C : Fin j → Finset G)
    (hsize : ∀ i, (L i).card = ℓ)
    (hL : ∀ i k, i ≠ k → Disjoint (L i) (L k))
    (hC : ∀ i k, i ≠ k → Disjoint (C i) (C k))
    (hzero : ∀ i, (0 : G) ∉ C i) (loss : ℝ)
    (hnear : ∀ i, PhysicalNearMatching (ordinaryTarget L C i) ((ℓ : ℝ)-loss)) :
    ∃ D : LayerData G j ℓ,
      D.layer = L ∧ (∀ i, D.color i ⊆ C i) ∧
      (∀ i, ((ℓ-(D.tail i).card : ℕ) : ℝ) ≤ loss) ∧
      (D.deficit : ℝ) ≤ (j : ℝ)*loss := by
  simp only [PhysicalNearMatching] at hnear
  choose X Y U hX hY hU hlower hM using hnear
  have hX' : ∀ i, X i ⊆ L i.castSucc := by simpa [ordinaryTarget] using hX
  have hY' : ∀ i, Y i ⊆ L i.succ := by simpa [ordinaryTarget] using hY
  have hU' : ∀ i, U i ⊆ C i := by simpa [ordinaryTarget] using hU
  let D : LayerData G j ℓ := {
    layer := L
    size := hsize
    layer_disjoint := hL
    tail := X
    head := Y
    color := U
    tail_subset := hX'
    head_subset := hY'
    matching := fun i => Classical.choice (hM i)
    color_disjoint := fun i k hik => Finset.disjoint_of_subset_left (hU' i)
      (Finset.disjoint_of_subset_right (hU' k) (hC i k hik))
    color_nonzero := fun i hi => hzero i (hU' i hi) }
  have hdef : ∀ i, ((ℓ-(D.tail i).card : ℕ) : ℝ) ≤ loss := by
    intro i
    have hi := hlower i
    rw [Nat.cast_sub (D.tail_card_le i)]
    change (ℓ : ℝ) - ((X i).card : ℝ) ≤ loss
    linarith
  refine ⟨D, rfl, hU', hdef, ?_⟩
  calc
    (D.deficit : ℝ) = ∑ i, ((ℓ-(D.tail i).card : ℕ) : ℝ) := by
      simp [LayerData.deficit]
    _ ≤ ∑ _i : Fin j, loss := Finset.sum_le_sum (fun i _ => hdef i)
    _ = (j : ℝ)*loss := by simp

end
end EndpointFactor.OrdinaryFragments
