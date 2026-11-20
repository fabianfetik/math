import CorralFormalization.EndpointProof.Factor.Allocation.Protected

/-!
# Actual raw layer and colour-pool allocation

The categorical sample gives disjoint raw roles. Once previously occupied
coordinates are blocked, this module protects every remaining raw role
simultaneously and constructs actual filled sets of the prescribed sizes.
The paper-specific bounds on the blocked set remain explicit inputs.
-/

namespace EndpointFactor.Allocation

open scoped BigOperators Classical
open EndpointLayeredSample

noncomputable section
variable {α : Type*} [DecidableEq α]

/-- Simultaneous allocation of any disjoint raw pools. Loss in each pool is
paid only by points outside the target and by the explicitly blocked set. -/
theorem exists_raw_allocation (n : ℕ) (W blocked : Finset α)
    (raw : Fin n → Finset α) (cap : Fin n → ℕ)
    (hraw : ∀ i j, i ≠ j → Disjoint (raw i) (raw j))
    (hcap : ∀ i, (raw i).card ≤ cap i)
    (hroom : (∑ i, cap i) ≤ (W \ blocked).card) :
    ∃ chosen : Fin n → Finset α,
      (∀ i, raw i ∩ (W \ blocked) ⊆ chosen i ∧
        chosen i ⊆ W \ blocked ∧ (chosen i).card = cap i ∧
        (raw i \ chosen i).card ≤ (raw i \ W).card + (raw i ∩ blocked).card) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      ((W \ blocked) \ Finset.univ.biUnion chosen).card + (∑ i, cap i) =
        (W \ blocked).card := by
  let keep (i : Fin n) := raw i ∩ (W \ blocked)
  have hsub : ∀ i, keep i ⊆ W \ blocked := fun i => Finset.inter_subset_right
  have hkeepcap : ∀ i, (keep i).card ≤ cap i := fun i =>
    (Finset.card_le_card Finset.inter_subset_left).trans (hcap i)
  have hkeepdisj : ∀ i j, i ≠ j → Disjoint (keep i) (keep j) := by
    intro i j hij
    exact (hraw i j hij).mono Finset.inter_subset_left Finset.inter_subset_left
  obtain ⟨chosen, hchosen, hpair, hleft⟩ :=
    exists_indexed_protected_allocation_with_remainder n (W \ blocked)
      keep cap hsub hkeepcap hkeepdisj hroom
  refine ⟨chosen, ?_, hpair, hleft⟩
  intro i
  exact ⟨(hchosen i).1, (hchosen i).2.1, (hchosen i).2.2,
    raw_loss_le_missing_and_blocked (raw i) W blocked (chosen i) (hchosen i).1⟩

variable {G : Type*} [Fintype G] [DecidableEq G] {m : ℕ}

/-- Actual vertex roles of the one categorical sample. -/
theorem exists_raw_vertex_layers (s : Sample G m) (n : ℕ) (W blocked : Finset G)
    (roles : Fin n → VertexRole m) (cap : Fin n → ℕ)
    (hroles : Function.Injective roles)
    (hcap : ∀ i, (vertexSet s (roles i)).card ≤ cap i)
    (hroom : (∑ i, cap i) ≤ (W \ blocked).card) :
    ∃ chosen : Fin n → Finset G,
      (∀ i, vertexSet s (roles i) ∩ (W \ blocked) ⊆ chosen i ∧
        chosen i ⊆ W \ blocked ∧ (chosen i).card = cap i ∧
        (vertexSet s (roles i) \ chosen i).card ≤
          (vertexSet s (roles i) \ W).card + (vertexSet s (roles i) ∩ blocked).card) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      ((W \ blocked) \ Finset.univ.biUnion chosen).card + (∑ i, cap i) =
        (W \ blocked).card := by
  apply exists_raw_allocation n W blocked (fun i => vertexSet s (roles i)) cap
  · intro i j hij
    exact vertexSet_disjoint s (fun heq => hij (hroles heq))
  · exact hcap
  · exact hroom

/-- Actual colour roles of the same categorical sample. -/
theorem exists_raw_colour_pools (s : Sample G m) (n : ℕ) (D blocked : Finset G)
    (roles : Fin n → ColourRole m) (cap : Fin n → ℕ)
    (hroles : Function.Injective roles)
    (hcap : ∀ i, (colourSet s (roles i)).card ≤ cap i)
    (hroom : (∑ i, cap i) ≤ (D \ blocked).card) :
    ∃ chosen : Fin n → Finset G,
      (∀ i, colourSet s (roles i) ∩ (D \ blocked) ⊆ chosen i ∧
        chosen i ⊆ D \ blocked ∧ (chosen i).card = cap i ∧
        (colourSet s (roles i) \ chosen i).card ≤
          (colourSet s (roles i) \ D).card + (colourSet s (roles i) ∩ blocked).card) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      ((D \ blocked) \ Finset.univ.biUnion chosen).card + (∑ i, cap i) =
        (D \ blocked).card := by
  apply exists_raw_allocation n D blocked (fun i => colourSet s (roles i)) cap
  · intro i j hij
    exact colourSet_disjoint s (fun heq => hij (hroles heq))
  · exact hcap
  · exact hroom

end
end EndpointFactor.Allocation
