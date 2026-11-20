import CorralFormalization.EndpointProof.Matching.Fractional.RoundingAKSBounds

/-!
# Fractional perfection to an actual near-perfect matching, conditional on AKS

`AKSNearRegularInput` states precisely the external near-regular matching
consequence used here. It is an ordinary proposition passed as a theorem
argument, not a Lean axiom and not the desired fractional-perfect conclusion.
It is the k = 3 consequence of Alon--Kim--Spencer, Theorem 2.1 and its
iteration (author-hosted `aks7.pdf`, printed pp. 4--5 and 9--10).

The complete reduction from that input to diffuse fractional-perfect
matchings, including the eventual degree and rate comparisons, is proved.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.Rounding

noncomputable section

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/-- An actual matching is a family of pairwise disjoint actual edges. -/
def IsMatching (edges : E → Finset V) (M : Finset E) : Prop :=
  (M : Set E).Pairwise (fun e f => Disjoint (edges e) (edges f))

/-- The actual uncovered vertices, inside the unchanged original vertex type. -/
def uncovered (edges : E → Finset V) (M : Finset E) : Finset V :=
  Finset.univ \ M.biUnion edges

/-- Exact external near-regular AKS input, specialized to three-uniform linear
hypergraphs and with its constants made explicit. `Δ ≥ e` only restricts the
large-degree domain. The conclusion uses the actual uncovered set. No
fractional weights, rounding property, or target remainder occurs as a premise. -/
def AKSNearRegularInput (edges : E → Finset V) (K D₀ C : ℝ) : Prop :=
  ∀ (S : Finset E), (∀ e ∈ S, (edges e).card = 3) →
    ((S : Set E).Pairwise (fun e f => ((edges e) ∩ (edges f)).card ≤ 1)) →
    ∀ Δ : ℝ, D₀ ≤ Δ → Real.exp 1 ≤ Δ →
      (∀ v, Δ - K * Real.sqrt Δ * Real.sqrt (Real.log Δ) ≤ degree edges S v ∧
        (degree edges S v : ℝ) ≤ Δ) →
      ∃ M : Finset E, M ⊆ S ∧ IsMatching edges M ∧
        (uncovered edges M).card ≤ C * (Fintype.card V : ℝ) * aksRate Δ

/-- The source assertion with constants uniform over all finite hypergraphs
in the chosen universes. This proposition is only an explicit external input. -/
def AKSNearRegularTheorem (K D₀ C : ℝ) : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
    (edges : E → Finset V), AKSNearRegularInput edges K D₀ C

/-- At any degree in the proved explicit domain, fractional perfection plus
the external near-regular input gives an actual matching on positive-weight
supported edges, with the manuscript's rate at the original `D`. -/
theorem diffuse_perfect_matching_of_AKS_at (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (K D₀ C : ℝ) (hC : 0 ≤ C) (hAKS : AKSNearRegularInput edges K D₀ C)
    (D : ℕ) (hD : 3 ≤ D) (hmin : D₀ ≤ (D : ℝ) + 3)
    (hexp : Real.exp 1 ≤ (D : ℝ) + 3)
    (hwindow : 6 ≤ K * Real.sqrt ((D : ℝ) + 3) * Real.sqrt (Real.log ((D : ℝ) + 3)))
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ))
    (hperfect : ∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) :
    ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
      (uncovered edges M).card ≤ C * (Fintype.card V : ℝ) * diffuseRate D := by
  obtain ⟨S, hsupp, _, _, _, hdegrees⟩ := linear_three_uniform_near_regular edges
    huniform hlinear D (by omega) w hw hperfect
  have hlinS : (S : Set E).Pairwise
      (fun e f => ((edges e) ∩ (edges f)).card ≤ 1) := by
    intro e _ f _ hne
    exact hlinear e f hne
  have hrange : ∀ v, ((D : ℝ) + 3) -
      K * Real.sqrt ((D : ℝ) + 3) * Real.sqrt (Real.log ((D : ℝ) + 3)) ≤
      degree edges S v ∧ (degree edges S v : ℝ) ≤ (D : ℝ) + 3 := by
    intro v
    constructor
    · linarith [(hdegrees v).1]
    · exact (hdegrees v).2
  obtain ⟨M, hMS, hM, hrest⟩ :=
    hAKS S (fun e _ => huniform e) hlinS ((D : ℝ) + 3) hmin hexp hrange
  refine ⟨M, hM, fun e he => hsupp e (hMS he), ?_⟩
  exact hrest.trans (mul_le_mul_of_nonneg_left
    (aksRate_add_three_le_diffuseRate D (by exact_mod_cast hD))
    (mul_nonneg hC (Nat.cast_nonneg _)))

/-- Eventual diffuse-perfect matching corollary for a fixed finite hypergraph.
All eventual inequalities are proved; the only external premise is the
separately stated near-regular AKS matching theorem. -/
theorem diffuse_perfect_matching_of_AKS (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (K D₀ C : ℝ) (hK : 0 < K) (hC : 0 ≤ C)
    (hAKS : AKSNearRegularInput edges K D₀ C) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧ ∀ D : ℕ, Dstar ≤ D →
      ∀ w : E → ℝ, (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) →
        (∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) →
        ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
          (uncovered edges M).card ≤ C * (Fintype.card V : ℝ) * diffuseRate D := by
  obtain ⟨Dstar, hstar, hthreshold⟩ := exists_aks_rounding_threshold K D₀ hK
  refine ⟨Dstar, hstar, ?_⟩
  intro D hD w hw hperfect
  obtain ⟨hmin, hexp, hwindow⟩ := hthreshold D hD
  exact diffuse_perfect_matching_of_AKS_at edges huniform hlinear K D₀ C hC hAKS
    D (hstar.trans hD) hmin hexp hwindow w hw hperfect

/-- Constants remain absolute: a uniform external AKS theorem supplies one
threshold and one remainder constant simultaneously for all finite linear
three-uniform hypergraphs in the chosen universes. -/
theorem diffuse_perfect_matching_from_external_AKS
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSNearRegularTheorem.{u, v} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        (edges : E → Finset V), (∀ e, (edges e).card = 3) → IsLinear edges →
        ∀ D : ℕ, Dstar ≤ D → ∀ w : E → ℝ,
          (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) →
          (∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) →
          ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
            (uncovered edges M).card ≤ Cstar * (Fintype.card V : ℝ) * diffuseRate D := by
  obtain ⟨K, D₀, C, hK, hC, hsource⟩ := hAKS
  obtain ⟨Dstar, hstar, hthreshold⟩ := exists_aks_rounding_threshold K D₀ hK
  refine ⟨Dstar, C, hstar, hC, ?_⟩
  intro V E _ _ edges huniform hlinear D hD w hw hperfect
  obtain ⟨hmin, hexp, hwindow⟩ := hthreshold D hD
  exact diffuse_perfect_matching_of_AKS_at edges huniform hlinear K D₀ C hC.le
    (hsource V E edges) D (hstar.trans hD) hmin hexp hwindow w hw hperfect


omit [Fintype E] in
/-- The uncovered set counts actual vertices: each disjoint three-edge covers
exactly three, with no virtual vertices or padded remainder. -/
theorem uncovered_card_add_three_mul_card (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (M : Finset E) (hM : IsMatching edges M) :
    (uncovered edges M).card + 3 * M.card = Fintype.card V := by
  have hcovered : (M.biUnion edges).card = 3 * M.card := by
    rw [Finset.card_biUnion hM]
    calc
      ∑ e ∈ M, (edges e).card = ∑ _e ∈ M, (3 : ℕ) :=
        Finset.sum_congr rfl (fun e _ => huniform e)
      _ = 3 * M.card := by simp [Nat.mul_comm]
  have hpartition := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (M.biUnion edges))
  simpa only [uncovered, hcovered, Finset.card_univ] using hpartition

omit [Fintype E] in
/-- For `3m` actual vertices, the matching-edge deficit is exactly one third
of the uncovered-vertex count. This only needs uniformity and disjointness. -/
theorem uncovered_card_eq_three_mul_deficit (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (M : Finset E) (hM : IsMatching edges M)
    (m : ℕ) (hvertices : Fintype.card V = 3 * m) :
    M.card ≤ m ∧ (uncovered edges M).card = 3 * (m - M.card) := by
  have hcard := uncovered_card_add_three_mul_card edges huniform M hM
  rw [hvertices] at hcard
  omega

/-- Balanced-size form of the diffuse-perfect corollary. In particular this
applies to a three-partite vertex set with `m` vertices in every role, giving
the required matching-edge deficit bound with the same constant `C`. -/
theorem diffuse_perfect_matching_edge_deficit_of_AKS (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (m : ℕ) (hvertices : Fintype.card V = 3 * m)
    (K D₀ C : ℝ) (hK : 0 < K) (hC : 0 ≤ C)
    (hAKS : AKSNearRegularInput edges K D₀ C) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧ ∀ D : ℕ, Dstar ≤ D →
      ∀ w : E → ℝ, (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) →
        (∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) →
        ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
          M.card ≤ m ∧ ((m - M.card : ℕ) : ℝ) ≤ C * (m : ℝ) * diffuseRate D := by
  obtain ⟨Dstar, hstar, hmatching⟩ :=
    diffuse_perfect_matching_of_AKS edges huniform hlinear K D₀ C hK hC hAKS
  refine ⟨Dstar, hstar, ?_⟩
  intro D hD w hw hperfect
  obtain ⟨M, hM, hsupp, hrest⟩ := hmatching D hD w hw hperfect
  obtain ⟨hMle, hcount⟩ := uncovered_card_eq_three_mul_deficit edges huniform M hM m hvertices
  refine ⟨M, hM, hsupp, hMle, ?_⟩
  rw [hcount, hvertices] at hrest
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hrest
  nlinarith

/-- The actual-matching conclusion in the manuscript's literal fractional-
power notation, with every eventual comparison proved. -/
theorem diffuse_perfect_matching_rpow_of_AKS (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (K D₀ C : ℝ) (hK : 0 < K) (hC : 0 ≤ C)
    (hAKS : AKSNearRegularInput edges K D₀ C) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧ ∀ D : ℕ, Dstar ≤ D →
      ∀ w : E → ℝ, (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) →
        (∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) →
        ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
          (uncovered edges M).card ≤ C * (Fintype.card V : ℝ) *
            ((D : ℝ) ^ (-1 / 2 : ℝ) *
              (Real.log (Real.exp 1 * (D : ℝ))) ^ (3 / 2 : ℝ)) := by
  obtain ⟨Dstar, hstar, hmatching⟩ :=
    diffuse_perfect_matching_of_AKS edges huniform hlinear K D₀ C hK hC hAKS
  refine ⟨Dstar, hstar, ?_⟩
  intro D hD w hw hperfect
  obtain ⟨M, hM, hsupp, hrest⟩ := hmatching D hD w hw hperfect
  refine ⟨M, hM, hsupp, ?_⟩
  rw [diffuseRate_eq_rpow D (by exact_mod_cast (show 1 ≤ D by omega))] at hrest
  exact hrest

end
end EndpointMatching.Fractional.Rounding
