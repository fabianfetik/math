import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.NearInput
import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Edges
import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Inventories

/-!
# A complete ordinary-layer/attachment outcome

The input `P` is the actual union of allocated ordinary colour pools, and
`L` is the actual physically disjoint remainder set. `D` contains the true
covered inventories selected from the ordinary transition lemma. The result records the pre-attachment
original primary paths as well as the final attached paths and exact bank.
The router splicing and the eventual exact-matching discrepancy estimate are separate.
-/

open scoped Classical BigOperators symmDiff
namespace EndpointFactor.OrdinaryFragments
open EndpointLayeredSample
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

structure Outcome {j ℓ : ℕ} (D : LayerData G j ℓ) (P L H₀ Y : Finset G) where
  before : Family G
  after : Family G
  donors : Finset G
  joins : Finset G
  before_vertices : before.vertices = D.vertices ∪ L
  before_colors : before.colors = D.colors
  before_edges : before.edges = D.edges
  before_starts : D.layer 0 ⊆ before.starts
  before_ends : D.layer (Fin.last j) ⊆ before.ends
  before_count : Fintype.card before.Index = ℓ+D.deficit+L.card
  primary_count : (before.primary (D.layer 0)).card = ℓ
  bad_primary_bound : ((before.primary (D.layer 0)).filter
    (fun i => before.last i ∉ D.layer (Fin.last j))).card ≤ D.deficit
  missing_good_bound : (D.layer (Fin.last j) \
    before.goodPrimaryEnds (D.layer 0) (D.layer (Fin.last j))).card ≤ D.deficit
  donors_original : donors ⊆ before.goodPrimaryEnds (D.layer 0) (D.layer (Fin.last j))
  donors_avoid_Y : Disjoint donors Y
  joins_subset : joins ⊆ H₀
  donor_count : donors.card = D.deficit+L.card
  join_count : joins.card = D.deficit+L.card
  after_vertices : after.vertices = D.vertices ∪ L
  after_colors : after.colors = D.colors ∪ joins
  after_starts : after.starts = D.layer 0
  after_ends : after.ends = before.ends \ donors
  after_count : Fintype.card after.Index = ℓ
  prescribed_ends : Y ⊆ after.ends
  end_discrepancy : (after.ends ∆ D.layer (Fin.last j)).card = 2*(D.deficit+L.card)
  remaining_exact : remainingBank H₀ joins P D.colors = (P ∪ H₀) \ after.colors
  remaining_size : (remainingBank H₀ joins P D.colors).card+Y.card = ℓ
  remaining_discrepancy : ((remainingBank H₀ joins P D.colors) ∆ H₀).card = 2*D.deficit+L.card
  remaining_nonzero : (0 : G) ∉ remainingBank H₀ joins P D.colors

/-- All ordinary paths, original primary donors, joins, protected terminals,
and remaining-bank stocks are constructed from the actual finite data and
the already-good pair event. The strict budget uses actual losses and the
true deficit; its coefficients are no larger than the paper's (6.7). -/
theorem exists_outcome [Fintype G] {m j ℓ : ℕ} {d : Densities m}
    {s : Sample G m} (hpair : PairSupplyEvent d s)
    (D : LayerData G j ℓ) (P L H₀ Y : Finset G)
    (hL : Disjoint L D.vertices) (hUP : D.colors ⊆ P)
    (hPcard : P.card = j*ℓ) (hPzero : (0 : G) ∉ P)
    (hHP : Disjoint H₀ P) (hHcard : H₀.card+Y.card = ℓ+L.card)
    (hH0zero : (0 : G) ∉ H₀) (hY : Y ⊆ D.layer (Fin.last j))
    (hbudget : (((vertexSet s (lastVertex m) \ D.layer (Fin.last j)).card + Y.card +
      (colourSet s (specialColour m) \ H₀).card + 3*D.deficit+2*L.card : ℕ) : ℝ) <
        d.q^2*(Fintype.card G : ℝ)/2) :
    Nonempty (Outcome D P L H₀ Y) := by
  obtain ⟨F₀, F, hV₀, hC₀, hS₀, hE₀, hcount₀, hV, hC, hEdges, hS, hE, hcount,
    hprim, hpends, hmissing⟩ := D.exists_with_leftovers_with_edges L hL
  let Z := F.goodPrimaryEnds (D.layer 0) (D.layer (Fin.last j))
  have hZ : Z ⊆ F.primaryEnds (D.layer 0) := Finset.inter_subset_left
  have hZE : Z ⊆ D.layer (Fin.last j) := Finset.inter_subset_right
  have hYF : Y ⊆ F.ends := hY.trans hE
  have hHF : Disjoint H₀ F.colors := by rw [hC]; exact hHP.mono_right hUP
  have hextras : (F.extras (D.layer 0)).card = D.deficit+L.card := by
    apply F.extras_card _ hS ℓ (D.deficit+L.card) (D.size _)
    omega
  have hRZ := raw_endpoint_loss (vertexSet s (lastVertex m)) (D.layer (Fin.last j)) Z
  have hZmissing : (D.layer (Fin.last j) \ Z).card ≤ D.deficit := hmissing
  have hbudgetZ : (((vertexSet s (lastVertex m) \ Z).card + Y.card +
      (colourSet s (specialColour m) \ H₀).card + 2*(F.extras (D.layer 0)).card : ℕ) : ℝ) <
        d.q^2*(Fintype.card G : ℝ)/2 := by
    have hnat : (vertexSet s (lastVertex m) \ Z).card + Y.card +
        (colourSet s (specialColour m) \ H₀).card + 2*(F.extras (D.layer 0)).card ≤
        (vertexSet s (lastVertex m) \ D.layer (Fin.last j)).card + Y.card +
        (colourSet s (specialColour m) \ H₀).card + 3*D.deficit+2*L.card := by
      rw [hextras]
      omega
    exact lt_of_le_of_lt (by exact_mod_cast hnat) hbudget
  obtain ⟨F', A, J, hV', hC', hS', hE', hAZ, hAY, hJH, hAc, hJc, hY', hcount'⟩ :=
    F.attach_extras_of_pairSupply hpair (D.layer 0) Z Y H₀ hS hZ hYF hHF hbudgetZ
  have hUcard := D.colors_card
  have hPc : P.card = D.colors.card+D.deficit := by omega
  have hbad : ((F.primary (D.layer 0)).filter
      (fun i => F.last i ∉ D.layer (Fin.last j))).card ≤ D.deficit := by
    rw [F.bad_primary_card, hpends, ← F₀.bad_primary_card]
    exact F₀.bad_primary_le _ _ hE₀ ℓ D.deficit (D.size _) hcount₀
  have hbank := remainingBank_inventory H₀ J P D.colors ℓ Y.card D.deficit L.card
    hHP hJH hUP hHcard (hJc.trans hextras) hPc
  refine ⟨{
    before := F
    after := F'
    donors := A
    joins := J
    before_vertices := hV
    before_colors := hC
    before_edges := hEdges
    before_starts := hS
    before_ends := hE
    before_count := hcount
    primary_count := hprim
    bad_primary_bound := hbad
    missing_good_bound := hmissing
    donors_original := hAZ
    donors_avoid_Y := hAY
    joins_subset := hJH
    donor_count := hAc.trans hextras
    join_count := hJc.trans hextras
    after_vertices := hV'.trans hV
    after_colors := by rw [hC', hC]
    after_starts := hS'
    after_ends := hE'
    after_count := hcount'.trans (D.size _)
    prescribed_ends := hY'
    end_discrepancy := F.attached_end_symmDiff F' _ A ℓ (D.deficit+L.card)
      hE (hAZ.trans hZE) (D.size _) (by omega) (hAc.trans hextras) hE'
    remaining_exact := by
      rw [remainingBank_eq_complement H₀ J P D.colors hHP hJH hUP, hC', hC]
    remaining_size := hbank.1
    remaining_discrepancy := hbank.2
    remaining_nonzero := remainingBank_nonzero H₀ J P D.colors hH0zero hPzero }⟩

end
end EndpointFactor.OrdinaryFragments
