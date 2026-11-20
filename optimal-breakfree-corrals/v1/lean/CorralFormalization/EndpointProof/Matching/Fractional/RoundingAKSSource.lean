import CorralFormalization.EndpointProof.Matching.Fractional.RoundingAKSBridge

/-!
# Literal finite-set formulation of the external AKS input

This file expresses the external result on a finite set of actual edge sets,
matching the source hypergraph convention. The adapter to indexed edges is
proved, including injectivity, equality of degrees, matching transfer and
equality of the actual uncovered sets.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.Rounding

noncomputable section

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/-- The external near-regular consequence of AKS, in the paper's finite set
of edge sets convention. Its constants and degree window are explicit. -/
def AKSSetFamilyInput (V : Type u) [Fintype V] (K D₀ C : ℝ) : Prop :=
  ∀ (H : Finset (Finset V)), (∀ a ∈ H, a.card = 3) →
    ((H : Set (Finset V)).Pairwise (fun a b => (a ∩ b).card ≤ 1)) →
    ∀ Δ : ℝ, D₀ ≤ Δ → Real.exp 1 ≤ Δ →
      (∀ v, Δ - K * Real.sqrt Δ * Real.sqrt (Real.log Δ) ≤ degree id H v ∧
        (degree id H v : ℝ) ≤ Δ) →
      ∃ P : Finset (Finset V), P ⊆ H ∧ IsMatching id P ∧
        (uncovered id P).card ≤ C * (Fintype.card V : ℝ) * aksRate Δ

/-- Uniform source constants for all finite vertex types in this universe. -/
def AKSSetFamilyTheorem (K D₀ C : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V], AKSSetFamilyInput V K D₀ C

omit [Fintype V] [Fintype E] in
/-- Three-uniform linear families cannot give different labels to the same
actual edge. This pays for the finite-set source translation. -/
theorem linear_three_uniform_injOn (edges : E → Finset V) (S : Finset E)
    (huniform : ∀ e ∈ S, (edges e).card = 3)
    (hlinear : (S : Set E).Pairwise (fun e f => ((edges e) ∩ (edges f)).card ≤ 1)) :
    Set.InjOn edges (S : Set E) := by
  intro e he f hf hef
  by_contra hne
  have h := hlinear he hf hne
  dsimp only at h
  rw [hef, Finset.inter_self, huniform f hf] at h
  omega

omit [Fintype E] in
/-- Reindex the exact finite-set source conclusion to an indexed family.
All degree counts and the actual uncovered inventory are preserved. -/
theorem AKSSetFamilyInput.toIndexed (K D₀ C : ℝ)
    (hsource : AKSSetFamilyInput V K D₀ C) (edges : E → Finset V) :
    AKSNearRegularInput edges K D₀ C := by
  intro S huniform hlinear Δ hmin hexp hrange
  let H : Finset (Finset V) := S.image edges
  have hinj := linear_three_uniform_injOn edges S huniform hlinear
  have huniformH : ∀ a ∈ H, a.card = 3 := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    exact huniform e he
  have hlinearH : (H : Set (Finset V)).Pairwise (fun a b => (a ∩ b).card ≤ 1) := by
    intro a ha b hb hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
    exact hlinear he hf (fun hef => hne (congrArg edges hef))
  have hdegree (v : V) : degree id H v = degree edges S v := by
    unfold degree H
    rw [Finset.filter_image]
    exact Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
  obtain ⟨P, hPH, hP, hrest⟩ := hsource H huniformH hlinearH Δ hmin hexp
    (fun v => by simpa only [hdegree] using hrange v)
  let M : Finset E := S.filter (fun e => edges e ∈ P)
  have hMS : M ⊆ S := Finset.filter_subset _ _
  have himage : M.image edges = P := by
    ext a
    constructor
    · intro ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp he).2
    · intro ha
      obtain ⟨e, he, hef⟩ := Finset.mem_image.mp (hPH ha)
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, by simpa [hef] using ha⟩, hef⟩
  have hM : IsMatching edges M := by
    intro e he f hf hne
    exact hP (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
      (fun hef => hne (hinj (hMS he) (hMS hf) hef))
  have hcover : M.biUnion edges = P.biUnion id := by
    rw [← himage, Finset.image_biUnion]
    rfl
  have huncovered : uncovered edges M = uncovered id P := by
    unfold uncovered
    rw [hcover]
  exact ⟨M, hMS, hM, by simpa only [huncovered] using hrest⟩

/-- The exact finite-set external theorem supplies the indexed external
premise used by the proved fractional-perfect bridge. -/
theorem AKSSetFamilyTheorem.toIndexed (K D₀ C : ℝ)
    (hsource : AKSSetFamilyTheorem.{u} K D₀ C) :
    AKSNearRegularTheorem.{u, v} K D₀ C := by
  intro V E _ _ edges
  exact (hsource V).toIndexed K D₀ C edges

/-- Direct bridge from the finite-set AKS external input to the manuscript's
literal near-perfect matching bound. The entire fractional and rounding part
is proved; the only source premise is the precise near-regular matching input. -/
theorem diffuse_perfect_matching_of_AKS_set_family (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (K D₀ C : ℝ) (hK : 0 < K) (hC : 0 ≤ C)
    (hsource : AKSSetFamilyInput V K D₀ C) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧ ∀ D : ℕ, Dstar ≤ D →
      ∀ w : E → ℝ, (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) →
        (∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) →
        ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
          (uncovered edges M).card ≤ C * (Fintype.card V : ℝ) *
            ((D : ℝ) ^ (-1 / 2 : ℝ) *
              (Real.log (Real.exp 1 * (D : ℝ))) ^ (3 / 2 : ℝ)) := by
  exact diffuse_perfect_matching_rpow_of_AKS edges huniform hlinear K D₀ C hK hC
    (hsource.toIndexed K D₀ C edges)


/-- The full absolute-constant diffuse-perfect corollary, conditional only on
the precisely stated finite-set near-regular AKS result. Its threshold and
constant are simultaneous for all finite hypergraphs and perfect weights. -/
theorem diffuse_perfect_matching_from_AKS_set_family
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        (edges : E → Finset V), (∀ e, (edges e).card = 3) → IsLinear edges →
        ∀ D : ℕ, Dstar ≤ D → ∀ w : E → ℝ,
          (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) →
          (∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) →
          ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
            (uncovered edges M).card ≤ Cstar * (Fintype.card V : ℝ) *
              ((D : ℝ) ^ (-1 / 2 : ℝ) *
                (Real.log (Real.exp 1 * (D : ℝ))) ^ (3 / 2 : ℝ)) := by
  have hindexed : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSNearRegularTheorem.{u, v} K D₀ C := by
    obtain ⟨K, D₀, C, hK, hC, hsource⟩ := hAKS
    exact ⟨K, D₀, C, hK, hC, hsource.toIndexed K D₀ C⟩
  obtain ⟨Dstar, Cstar, hstar, hCstar, hmatching⟩ :=
    diffuse_perfect_matching_from_external_AKS hindexed
  refine ⟨Dstar, Cstar, hstar, hCstar, ?_⟩
  intro V E _ _ edges huniform hlinear D hD w hw hperfect
  obtain ⟨M, hM, hsupp, hrest⟩ := hmatching V E edges huniform hlinear D hD w hw hperfect
  refine ⟨M, hM, hsupp, ?_⟩
  rw [diffuseRate_eq_rpow D (by exact_mod_cast (show 1 ≤ D by omega))] at hrest
  exact hrest

/-- The matching-edge deficit conclusion for `3m` actual vertices, including
three-partite hypergraphs with `m` vertices in each role, in literal manuscript
notation and conditional only on the exact finite-set AKS input. -/
theorem diffuse_perfect_edge_deficit_of_AKS_set_family (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (m : ℕ) (hvertices : Fintype.card V = 3 * m)
    (K D₀ C : ℝ) (hK : 0 < K) (hC : 0 ≤ C)
    (hsource : AKSSetFamilyInput V K D₀ C) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧ ∀ D : ℕ, Dstar ≤ D →
      ∀ w : E → ℝ, (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) →
        (∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) →
        ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
          M.card ≤ m ∧ ((m - M.card : ℕ) : ℝ) ≤ C * (m : ℝ) *
            ((D : ℝ) ^ (-1 / 2 : ℝ) *
              (Real.log (Real.exp 1 * (D : ℝ))) ^ (3 / 2 : ℝ)) := by
  obtain ⟨Dstar, hstar, hmatching⟩ := diffuse_perfect_matching_edge_deficit_of_AKS
    edges huniform hlinear m hvertices K D₀ C hK hC (hsource.toIndexed K D₀ C edges)
  refine ⟨Dstar, hstar, ?_⟩
  intro D hD w hw hperfect
  obtain ⟨M, hM, hsupp, hMle, hrest⟩ := hmatching D hD w hw hperfect
  refine ⟨M, hM, hsupp, hMle, ?_⟩
  rw [diffuseRate_eq_rpow D (by exact_mod_cast (show 1 ≤ D by omega))] at hrest
  exact hrest

end
end EndpointMatching.Fractional.Rounding
