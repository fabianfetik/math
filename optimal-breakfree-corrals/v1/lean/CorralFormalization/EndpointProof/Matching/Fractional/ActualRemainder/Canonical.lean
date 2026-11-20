import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Geometry
import CorralFormalization.EndpointProof.Matching.Fractional.RoundingAKSSource

/-!
# Canonical actual allowed edges and the proved fractional-to-matching adapter

Vertices are the subtype of one actual remaining tagged inventory `W`.
Edges are precisely its zero-sum additive triples avoiding the specified
later ban.  The fractional-perfect certificate remains an explicit premise;
the integral matching is obtained through the proved bounded-error rounding
bridge and the separately named external AKS proposition.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.ActualRemainder

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.Rounding

noncomputable section

universe u

variable {G : Type u} [AddCommGroup G]

/-- Every allowed edge is an actual finite subset of `W`, with an actual
zero-sum additive image and with the later ban checked on that image. -/
abbrev AllowedEdge (W : Finset (Vertex G)) (F : Finset (Finset (Vertex G))) :=
  {e : Finset W // Hyperedge (e.image (fun v : W => v.val)) ∧
    e.image (fun v : W => v.val) ∉ F}

def localEdge {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (e : AllowedEdge W F) : Finset W := e.val

def actualEdge {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (e : AllowedEdge W F) : Finset (Vertex G) :=
  (localEdge e).image (fun v : W => v.val)

theorem actualEdge_valid {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (e : AllowedEdge W F) : Hyperedge (actualEdge e) := e.property.1

theorem actualEdge_allowed {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (e : AllowedEdge W F) : actualEdge e ∉ F := e.property.2

theorem actualEdge_inside {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (e : AllowedEdge W F) : actualEdge e ⊆ W := by
  intro v hv
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact w.property

theorem actualEdge_injective (W : Finset (Vertex G))
    (F : Finset (Finset (Vertex G))) :
    Function.Injective (actualEdge (W := W) (F := F)) := by
  intro e f hef
  apply Subtype.ext
  exact Finset.image_injective Subtype.val_injective hef

theorem localEdge_uniform {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (e : AllowedEdge W F) : (localEdge e).card = 3 := by
  have h := hyperedge_card_eq_three (actualEdge_valid e)
  simpa only [actualEdge, Finset.card_image_of_injective _ Subtype.val_injective] using h

theorem localEdge_linear (W : Finset (Vertex G))
    (F : Finset (Finset (Vertex G))) : IsLinear (localEdge (W := W) (F := F)) := by
  classical
  intro e f hne
  have hne' : actualEdge e ≠ actualEdge f := fun h => hne (actualEdge_injective W F h)
  have h := hyperedge_inter_card_le_one (actualEdge_valid e) (actualEdge_valid f) hne'
  apply Finset.card_le_one.mpr
  intro v hv w hw
  simp only [Finset.mem_inter] at hv hw
  apply Subtype.ext
  apply Finset.card_le_one.mp h v.val
    (Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨v, hv.1, rfl⟩,
      Finset.mem_image.mpr ⟨v, hv.2, rfl⟩⟩) w.val
    (Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨w, hw.1, rfl⟩,
      Finset.mem_image.mpr ⟨w, hw.2, rfl⟩⟩)

/-- Unit load is required at every actual remaining vertex.  Positive total
mass, or a fractional submatching with a deficit, is insufficient here. -/
def FractionalPerfect (W : Finset (Vertex G)) (F : Finset (Finset (Vertex G)))
    (D : ℕ) : Prop :=
  ∃ w : AllowedEdge W F → ℝ,
    (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) ∧
    ∀ v : W, (∑ e, if v ∈ localEdge e then w e else 0) = 1

/-- The paper's interval certificate supplies the exact reciprocal cap
needed by bounded-error rounding.  Only `D ≤ 2d/3` is used here. -/
theorem fractionalPerfect_of_interval {W : Finset (Vertex G)}
    {F : Finset (Finset (Vertex G))} (d : ℝ) (D : ℕ)
    (hd : 0 < d) (hD : 0 < D) (hscale : (D : ℝ) ≤ 2 * d / 3)
    (w : AllowedEdge W F → ℝ)
    (hw : ∀ e, 1 / (2 * d) ≤ w e ∧ w e ≤ 3 / (2 * d))
    (hperfect : ∀ v : W, (∑ e, if v ∈ localEdge e then w e else 0) = 1) :
    FractionalPerfect W F D := by
  have hD' : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hcap : 3 / (2 * d) ≤ 1 / (D : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * d) hD').mpr
    linarith
  refine ⟨w, fun e => ⟨?_, (hw e).2.trans hcap⟩, hperfect⟩
  exact (by positivity : (0 : ℝ) ≤ 1 / (2 * d)).trans (hw e).1

/-- The actual covered inventory, with no newly introduced vertices. -/
def actualCovered {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (M : Finset (AllowedEdge W F)) : Finset (Vertex G) := M.biUnion actualEdge

theorem actualCovered_inside {W : Finset (Vertex G)}
    {F : Finset (Finset (Vertex G))} (M : Finset (AllowedEdge W F)) :
    actualCovered M ⊆ W := by
  intro v hv
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hv
  exact actualEdge_inside e he

/-- Transfer the matching, its exact covered inventory and every edge-ban
condition from the finite subtype back to the unchanged tagged universe. -/
def actualMatching {W : Finset (Vertex G)} {F : Finset (Finset (Vertex G))}
    (M : Finset (AllowedEdge W F)) (hM : IsMatching localEdge M) :
    Matching (actualCovered M) where
  edges := M.image actualEdge
  valid := by
    intro E hE
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hE
    exact actualEdge_valid e
  disjoint := by
    intro E hE H hH hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hH
    exact (Finset.disjoint_image Subtype.val_injective).mpr
      (hM he hf (fun hef => hne (congrArg actualEdge hef)))
  cover := by rw [Finset.image_biUnion]; rfl

theorem actualMatching_allowed {W : Finset (Vertex G)}
    {F : Finset (Finset (Vertex G))} (M : Finset (AllowedEdge W F))
    (hM : IsMatching localEdge M) :
    ∀ E ∈ (actualMatching M hM).edges, E ∉ F := by
  intro E hE
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hE
  exact actualEdge_allowed e

/-- The source theorem's uncovered set maps to precisely the actual set
difference, not to a padded or replaced inventory. -/
theorem uncovered_image_eq {W : Finset (Vertex G)}
    {F : Finset (Finset (Vertex G))} (M : Finset (AllowedEdge W F)) :
    (uncovered localEdge M).image (fun v : W => v.val) = W \ actualCovered M := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_sdiff.mpr ⟨w.property, ?_⟩
    intro hcover
    obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hcover
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hv
    have hxw : x = w := Subtype.ext hxeq
    simp only [uncovered, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_biUnion] at hw
    exact hw ⟨e, he, hxw ▸ hx⟩
  · intro hv
    have hvW := (Finset.mem_sdiff.mp hv).1
    refine Finset.mem_image.mpr ⟨⟨v, hvW⟩, ?_, rfl⟩
    simp only [uncovered, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    intro hcover
    obtain ⟨e, he, hvE⟩ := hcover
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr
      ⟨e, he, Finset.mem_image.mpr ⟨⟨v, hvW⟩, hvE, rfl⟩⟩)

theorem uncovered_card_eq_actual {W : Finset (Vertex G)}
    {F : Finset (Finset (Vertex G))} (M : Finset (AllowedEdge W F)) :
    (uncovered localEdge M).card = (W \ actualCovered M).card := by
  rw [← uncovered_image_eq M, Finset.card_image_of_injective _ Subtype.val_injective]

/-- One pair of absolute constants and one threshold work for every actual
inventory and every later ban.  The only matching-theorem premise is the
precisely named finite-set near-regular AKS consequence; the fractional
supplier is visibly required separately at each actual `W` and `F`. -/
theorem actual_matching_from_fractional_uniform
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (H : Type u) [AddCommGroup H]
        (W : Finset (Vertex H)) (F : Finset (Finset (Vertex H)))
        (D : ℕ), Dstar ≤ D → FractionalPerfect W F D →
        ∃ (P : Finset (Vertex H)) (M : Matching P), P ⊆ W ∧
          (∀ E ∈ M.edges, E ∉ F) ∧
          ((W \ P).card : ℝ) ≤ Cstar * (W.card : ℝ) * diffuseRate D := by
  obtain ⟨K, D₀, C, hK, hC, hsource⟩ := hAKS
  obtain ⟨Dstar, hstar, hthreshold⟩ := exists_aks_rounding_threshold K D₀ hK
  refine ⟨Dstar, C, hstar, hC, ?_⟩
  intro H _ W F D hD hfrac
  obtain ⟨w, hw, hperfect⟩ := hfrac
  have hperfect' : ∀ v : W,
      (∑ e, if v ∈ localEdge e then w e else 0) = 1 := hperfect
  obtain ⟨hmin, hexp, hwindow⟩ := hthreshold D hD
  obtain ⟨M, hM, _, hrest⟩ := diffuse_perfect_matching_of_AKS_at
    (localEdge (W := W) (F := F)) localEdge_uniform (localEdge_linear W F)
    K D₀ C hC.le ((hsource W).toIndexed K D₀ C localEdge)
    D (hstar.trans hD) hmin hexp hwindow w hw (fun v => by
      calc
        _ = ∑ e, if v ∈ localEdge e then w e else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases hm : v ∈ localEdge e <;> simp only [hm, if_true, if_false]
        _ = 1 := hperfect' v)
  refine ⟨actualCovered M, actualMatching M hM, actualCovered_inside M,
    actualMatching_allowed M hM, ?_⟩
  simpa only [uncovered_card_eq_actual M, Fintype.card_coe] using hrest

/-- Fixed-group specialization of the genuinely group-uniform adapter. -/
theorem actual_matching_from_fractional
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (W : Finset (Vertex G)) (F : Finset (Finset (Vertex G)))
        (D : ℕ), Dstar ≤ D → FractionalPerfect W F D →
        ∃ (P : Finset (Vertex G)) (M : Matching P), P ⊆ W ∧
          (∀ E ∈ M.edges, E ∉ F) ∧
          ((W \ P).card : ℝ) ≤ Cstar * (W.card : ℝ) * diffuseRate D := by
  obtain ⟨Dstar, Cstar, hstar, hCstar, hmatching⟩ := actual_matching_from_fractional_uniform hAKS
  exact ⟨Dstar, Cstar, hstar, hCstar, hmatching G⟩

end
end EndpointMatching.Fractional.ActualRemainder
