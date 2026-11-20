import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Geometry

/-!
# Rooted collisions and later deletions

Through a fixed surviving root, a deleted tagged partner destroys at most
one actual additive edge.  This pays the candidate losses from target edits,
the reserved inventory, a frozen matching and a later edge ban separately.
The existence and lower count of raw rooted candidates remain explicit raw
event hypotheses, rather than an assumption of a finished near matching.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.ActualRemainder

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The maximum-degree edge-ban convention, at one specified tagged root. -/
def banAt (F : Finset (Finset (Vertex G))) (z : Vertex G) : Finset (Finset (Vertex G)) :=
  F.filter (fun E => z ∈ E)

/-- Collision accounting: distinct additive edges through `z` have no second
common vertex, so a deleted vertex different from `z` is charged only once. -/
theorem rooted_deleted_edges_card_le
    (H : Finset (Finset (Vertex G))) (z : Vertex G) (D : Finset (Vertex G))
    (hvalid : ∀ E ∈ H, Hyperedge E) (hroot : ∀ E ∈ H, z ∈ E)
    (hz : z ∉ D) : (H.filter (fun E => ¬ Disjoint E D)).card ≤ D.card := by
  classical
  let bad := H.filter (fun E => ¬ Disjoint E D)
  have hchoose (e : bad) : ∃ v : Vertex G, v ∈ e.val ∧ v ∈ D :=
    Finset.not_disjoint_iff.mp (Finset.mem_filter.mp e.property).2
  let f : bad → D := fun e =>
    ⟨Classical.choose (hchoose e), (Classical.choose_spec (hchoose e)).2⟩
  have hinj : Function.Injective f := by
    intro e g hef
    apply Subtype.ext
    by_contra hne
    have heH := (Finset.mem_filter.mp e.property).1
    have hgH := (Finset.mem_filter.mp g.property).1
    have hlin := hyperedge_inter_card_le_one (hvalid e.val heH) (hvalid g.val hgH) hne
    have hfvE : (f e).val ∈ e.val := (Classical.choose_spec (hchoose e)).1
    have hfvG : (f e).val ∈ g.val := by
      have hfg : (f e).val = (f g).val := congrArg Subtype.val hef
      rw [hfg]
      exact (Classical.choose_spec (hchoose g)).1
    have hzv : z = (f e).val := Finset.card_le_one.mp hlin z
      (Finset.mem_inter.mpr ⟨hroot e.val heH, hroot g.val hgH⟩) (f e).val
      (Finset.mem_inter.mpr ⟨hfvE, hfvG⟩)
    exact hz (hzv ▸ (f e).property)
  exact Finset.card_le_card_of_injective hinj

/-- A positive paid candidate margin yields an actual surviving allowed
edge.  The ban is paid only at the specified root. -/
theorem rooted_allowed_edge_after_deletions
    (H : Finset (Finset (Vertex G))) (z : Vertex G)
    (R W D : Finset (Vertex G)) (F : Finset (Finset (Vertex G)))
    (hvalid : ∀ E ∈ H, Hyperedge E) (hroot : ∀ E ∈ H, z ∈ E)
    (hraw : ∀ E ∈ H, E ⊆ insert z R) (hzW : z ∈ W) (hzD : z ∉ D)
    (hmissing : R \ W ⊆ D)
    (hmargin : D.card + (banAt F z).card < H.card) :
    ∃ E : Finset (Vertex G), E ∈ H ∧ Hyperedge E ∧ E ⊆ W ∧ z ∈ E ∧ E ∉ F := by
  classical
  let deleted := H.filter (fun E => ¬ Disjoint E D)
  let banned := H.filter (fun E => E ∈ F)
  have hdel : deleted.card ≤ D.card :=
    rooted_deleted_edges_card_le H z D hvalid hroot hzD
  have hban : banned.card ≤ (banAt F z).card := by
    apply Finset.card_le_card
    intro E hE
    have he := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr ⟨he.2, hroot E he.1⟩
  have hlt : (deleted ∪ banned).card < H.card :=
    (Finset.card_union_le _ _).trans_lt ((Nat.add_le_add hdel hban).trans_lt hmargin)
  obtain ⟨E, hEH, hEbad⟩ : ∃ E ∈ H, E ∉ deleted ∪ banned := by
    by_contra h
    push Not at h
    have hsub : H ⊆ deleted ∪ banned := by intro E hE; exact h E hE
    exact (not_le_of_gt hlt) (Finset.card_le_card hsub)
  have hdis : Disjoint E D := by
    by_contra hd
    exact hEbad (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hEH, hd⟩))
  have hnotban : E ∉ F := by
    intro hEF
    exact hEbad (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hEH, hEF⟩))
  refine ⟨E, hEH, hvalid E hEH, ?_, hroot E hEH, hnotban⟩
  intro v hv
  rcases Finset.mem_insert.mp (hraw E hEH hv) with rfl | hvR
  · exact hzW
  · by_contra hvW
    exact Finset.disjoint_left.mp hdis hv (hmissing (Finset.mem_sdiff.mpr ⟨hvR, hvW⟩))

/-- Concrete accounting for the zero-edge request after a reserved core and
an arbitrary preselected matching.  In particular no vertex collision with
either previously fixed inventory is left to the fractional supplier. -/
theorem zero_edge_from_raw_candidates_of_margin
    {R T A P : Finset (Vertex G)} (M : Matching P)
    (F : Finset (Finset (Vertex G)))
    (candidates : Vertex G → Finset (Finset (Vertex G)))
    (hvalid : ∀ z E, E ∈ candidates z → Hyperedge E)
    (hroot : ∀ z E, E ∈ candidates z → z ∈ E)
    (hraw : ∀ z E, E ∈ candidates z → E ⊆ insert z R)
    (hbudget : ∀ z ∈ residual T A P, z.2 = 0 →
      (R \ T).card + A.card + 3 * M.edges.card + (banAt F z).card < (candidates z).card) :
    ∀ z ∈ residual T A P, z.2 = 0 →
      ∃ E : Finset (Vertex G), Hyperedge E ∧ E ⊆ residual T A P ∧ z ∈ E ∧ E ∉ F := by
  classical
  intro z hz hz0
  let D := (R \ T) ∪ A ∪ P
  have hzT := (Finset.mem_sdiff.mp hz).1
  have hzAP := (Finset.mem_sdiff.mp hz).2
  have hzD : z ∉ D := by
    simp only [D, Finset.mem_union, Finset.mem_sdiff]
    intro h
    rcases h with (h | h) | h
    · exact h.2 hzT
    · exact hzAP (Finset.mem_union_left _ h)
    · exact hzAP (Finset.mem_union_right _ h)
  have hmissing : R \ residual T A P ⊆ D := by
    intro v hv
    have hvR := (Finset.mem_sdiff.mp hv).1
    have hvW := (Finset.mem_sdiff.mp hv).2
    by_cases hvT : v ∈ T
    · have hvAP : v ∈ A ∪ P := by
        by_contra hvAP
        exact hvW (Finset.mem_sdiff.mpr ⟨hvT, hvAP⟩)
      rcases Finset.mem_union.mp hvAP with hvA | hvP
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvA)
      · exact Finset.mem_union_right _ hvP
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvR, hvT⟩))
  have hD : D.card ≤ (R \ T).card + A.card + 3 * M.edges.card := by
    calc
      D.card ≤ ((R \ T) ∪ A).card + P.card := Finset.card_union_le _ _
      _ ≤ (R \ T).card + A.card + P.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by rw [matching_card M]
  have hmargin : D.card + (banAt F z).card < (candidates z).card :=
    (Nat.add_le_add_right hD _).trans_lt (hbudget z hz hz0)
  obtain ⟨E, _, hE, hEW, hzE, hEF⟩ := rooted_allowed_edge_after_deletions
    (candidates z) z R (residual T A P) D F (hvalid z) (hroot z) (hraw z)
      hz hzD hmissing hmargin
  exact ⟨E, hE, hEW, hzE, hEF⟩

/-- Uniform natural degree and ban bounds supply the paid zero-edge margin. -/
theorem zero_edge_from_raw_candidates
    {R T A P : Finset (Vertex G)} (M : Matching P)
    (F : Finset (Finset (Vertex G))) (L B : ℕ)
    (candidates : Vertex G → Finset (Finset (Vertex G)))
    (hvalid : ∀ z E, E ∈ candidates z → Hyperedge E)
    (hroot : ∀ z E, E ∈ candidates z → z ∈ E)
    (hraw : ∀ z E, E ∈ candidates z → E ⊆ insert z R)
    (hdegree : ∀ z ∈ residual T A P, z.2 = 0 → L ≤ (candidates z).card)
    (hban : ∀ z, (banAt F z).card ≤ B)
    (hbudget : (R \ T).card + A.card + 3 * M.edges.card + B < L) :
    ∀ z ∈ residual T A P, z.2 = 0 →
      ∃ E : Finset (Vertex G), Hyperedge E ∧ E ⊆ residual T A P ∧ z ∈ E ∧ E ∉ F := by
  apply zero_edge_from_raw_candidates_of_margin M F candidates hvalid hroot hraw
  intro z hz hz0
  exact (Nat.add_le_add_left (hban z) _).trans_lt (hbudget.trans_le (hdegree z hz hz0))

/-- Real raw-degree and ban estimates can be used directly; no hidden
integer-rounding margin is introduced by the deterministic zero step. -/
theorem zero_edge_from_raw_real_bounds
    {R T A P : Finset (Vertex G)} (M : Matching P)
    (F : Finset (Finset (Vertex G))) (lower banBound : ℝ)
    (candidates : Vertex G → Finset (Finset (Vertex G)))
    (hvalid : ∀ z E, E ∈ candidates z → Hyperedge E)
    (hroot : ∀ z E, E ∈ candidates z → z ∈ E)
    (hraw : ∀ z E, E ∈ candidates z → E ⊆ insert z R)
    (hdegree : ∀ z ∈ residual T A P, z.2 = 0 → lower ≤ ((candidates z).card : ℝ))
    (hban : ∀ z, ((banAt F z).card : ℝ) ≤ banBound)
    (hbudget : ((R \ T).card : ℝ) + (A.card : ℝ) +
      3 * (M.edges.card : ℝ) + banBound < lower) :
    ∀ z ∈ residual T A P, z.2 = 0 →
      ∃ E : Finset (Vertex G), Hyperedge E ∧ E ⊆ residual T A P ∧ z ∈ E ∧ E ∉ F := by
  apply zero_edge_from_raw_candidates_of_margin M F candidates hvalid hroot hraw
  intro z hz hz0
  have h : ((R \ T).card : ℝ) + (A.card : ℝ) +
      3 * (M.edges.card : ℝ) + ((banAt F z).card : ℝ) < ((candidates z).card : ℝ) := by
    linarith [hban z, hdegree z hz hz0]
  exact_mod_cast h

end
end EndpointMatching.Fractional.ActualRemainder
