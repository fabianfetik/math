import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Attach
import CorralFormalization.EndpointProof.Factor.InventoryBudget

/-!
# Actual attachment inventories and the remaining closing colour bank

These results pay the physical endpoint change (6.8) and colour-bank change
(6.9). Donors and joining colours are actual finite sets of the indicated
cardinalities, with the required physical subset and disjointness facts.
-/

open scoped Classical BigOperators symmDiff
namespace EndpointFactor.OrdinaryFragments
open EndpointLayeredSample
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

namespace Family

/-- Combine the already-good common pair event with the constructive
component joins. The only budget is the actual endpoint/colour loss in
that same sample and the two earlier-choice inventories. -/
theorem attach_extras_of_pairSupply [Fintype G] {m : ℕ} {d : Densities m}
    {s : Sample G m} (hpair : PairSupplyEvent d s)
    (F : Family G) (B Z Y H₀ : Finset G)
    (hB : B ⊆ F.starts) (hZ : Z ⊆ F.primaryEnds B) (hY : Y ⊆ F.ends)
    (hH : Disjoint H₀ F.colors)
    (hbudget : (((vertexSet s (lastVertex m) \ Z).card + Y.card +
      (colourSet s (specialColour m) \ H₀).card + 2*(F.extras B).card : ℕ) : ℝ) <
        d.q^2*(Fintype.card G : ℝ)/2) :
    ∃ F' : Family G, ∃ A J : Finset G,
      F'.vertices = F.vertices ∧ F'.colors = F.colors ∪ J ∧
      F'.starts = B ∧ F'.ends = F.ends \ A ∧
      A ⊆ Z ∧ Disjoint A Y ∧ J ⊆ H₀ ∧
      A.card = (F.extras B).card ∧ J.card = (F.extras B).card ∧
      Y ⊆ F'.ends ∧ Fintype.card F'.Index = B.card := by
  let g : F.extras B → G := fun e => F.first e.val
  have hb : (((vertexSet s (lastVertex m) \ Z).card + Y.card +
      (colourSet s (specialColour m) \ H₀).card + 2*Fintype.card (F.extras B) : ℕ) : ℝ) <
        d.q^2*(Fintype.card G : ℝ)/2 := by
    simpa only [Fintype.card_coe] using hbudget
  obtain ⟨a, ha, hainj, hcinj⟩ := choose_original_donors_of_pairSupply hpair g Z Y H₀ hb
  obtain ⟨F', hV, hC, hS, hE, hY', hcount, hAcard, hJcard⟩ :=
    F.attach_extras B Z Y H₀ hB hZ hY hH a ha hainj hcinj
  refine ⟨F', Finset.univ.image a, Finset.univ.image (fun e => g e-a e),
    hV, hC, hS, hE, ?_, ?_, ?_, hAcard, hJcard, hY', hcount⟩
  · intro x hx
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
    exact (ha e).1
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
    exact (ha e).2.1 hy
  · intro c hc
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hc
    exact (ha e).2.2

/-- Exact (6.8), using the original last-layer endpoint inclusion and the
actual number of distinct consumed donors. -/
theorem attached_end_symmDiff (F F' : Family G) (E A : Finset G) (ℓ H : ℕ)
    (hE : E ⊆ F.ends) (hA : A ⊆ E) (hsize : E.card = ℓ)
    (hcount : Fintype.card F.Index = ℓ+H) (hAcard : A.card = H)
    (hends : F'.ends = F.ends \ A) :
    (F'.ends ∆ E).card = 2*H := by
  have hO := Finset.card_sdiff_add_card_eq_card hE
  rw [F.ends_card, hcount, hsize] at hO
  have heq : F'.ends = (E \ A) ∪ (F.ends \ E) := by
    rw [hends]
    ext x
    have hEF : x ∈ E → x ∈ F.ends := fun hx => hE hx
    have hAE : x ∈ A → x ∈ E := fun hx => hA hx
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hdis : Disjoint E (F.ends \ E) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 hx
  rw [heq, InventoryBudget.symmDiff_remove_add_card E A (F.ends \ E) hA hdis, hAcard]
  omega

end Family

/-- The closing bank contains the unspent original bank and *all* unused
ordinary colours. Its exact definition uses actual colour sets. -/
def remainingBank (H₀ J P U : Finset G) : Finset G := (H₀ \ J) ∪ (P \ U)

theorem remainingBank_eq_complement (H₀ J P U : Finset G)
    (hHP : Disjoint H₀ P) (hJ : J ⊆ H₀) (hU : U ⊆ P) :
    remainingBank H₀ J P U = (P ∪ H₀) \ (U ∪ J) := by
  ext c
  have hJP : c ∈ J → c ∈ H₀ := fun h => hJ h
  have hUP : c ∈ U → c ∈ P := fun h => hU h
  have hdis : c ∈ H₀ → c ∈ P → False := fun hH hP => Finset.disjoint_left.mp hHP hH hP
  simp only [remainingBank, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- Router colours are already spent and are disjoint from both ordinary
pools and the original bank. The remaining bank is then the literal
complement of every real used colour in the complete target. -/
theorem remainingBank_eq_full_complement (R H₀ J P U : Finset G)
    (hHP : Disjoint H₀ P) (hRP : Disjoint R P) (hRH : Disjoint R H₀)
    (hJ : J ⊆ H₀) (hU : U ⊆ P) :
    remainingBank H₀ J P U = (R ∪ P ∪ H₀) \ (R ∪ U ∪ J) := by
  rw [remainingBank_eq_complement H₀ J P U hHP hJ hU]
  ext c
  have hRP' : c ∈ R → c ∈ P → False := fun hR hP => Finset.disjoint_left.mp hRP hR hP
  have hRH' : c ∈ R → c ∈ H₀ → False := fun hR hH => Finset.disjoint_left.mp hRH hR hH
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- Exact (6.9), including the true remainder `w`. The equations on
cardinalities encode actual set stocks and are separate from set supply. -/
theorem remainingBank_inventory (H₀ J P U : Finset G) (ℓ K h w : ℕ)
    (hHP : Disjoint H₀ P) (hJ : J ⊆ H₀) (hU : U ⊆ P)
    (hHcard : H₀.card+K = ℓ+w) (hJcard : J.card = h+w)
    (hPcard : P.card = U.card+h) :
    (remainingBank H₀ J P U).card+K = ℓ ∧
      ((remainingBank H₀ J P U) ∆ H₀).card = 2*h+w := by
  have hleft := Finset.card_sdiff_add_card_eq_card hJ
  have hright := Finset.card_sdiff_add_card_eq_card hU
  have hdis : Disjoint H₀ (P \ U) := hHP.mono_right (Finset.sdiff_subset)
  have hdis' : Disjoint (H₀ \ J) (P \ U) := hdis.mono_left Finset.sdiff_subset
  constructor
  · rw [remainingBank, Finset.card_union_of_disjoint hdis']
    omega
  · rw [remainingBank, InventoryBudget.symmDiff_remove_add_card H₀ J (P \ U) hJ hdis,
      hJcard]
    omega

theorem remainingBank_subset (H₀ J P U : Finset G) :
    remainingBank H₀ J P U ⊆ H₀ ∪ P := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hc).1
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hc).1

theorem remainingBank_nonzero (H₀ J P U : Finset G)
    (hzeroH : (0 : G) ∉ H₀) (hzeroP : (0 : G) ∉ P) :
    (0 : G) ∉ remainingBank H₀ J P U := by
  intro h
  rcases Finset.mem_union.mp (remainingBank_subset H₀ J P U h) with h | h
  · exact hzeroH h
  · exact hzeroP h

end
end EndpointFactor.OrdinaryFragments
