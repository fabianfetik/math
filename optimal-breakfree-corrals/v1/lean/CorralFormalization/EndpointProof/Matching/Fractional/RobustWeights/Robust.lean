import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.Perturbation

/-!
# A quantified deterministic robust fractional-perfect theorem

The full conclusion, including positive lower and upper bounds, is proved for
every later edge ban of the displayed rooted degree.  The unbanned Gram
decomposition and three normalized matrix estimates are explicit hypotheses.
Deriving these estimates from the original-sample Fourier event is separate.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace EndpointMatching.Fractional.RobustWeights

noncomputable section

variable {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype E] [DecidableEq E]

/-- Robust weights from a proved inverse bound on the unbanned actual target.
The ban `F` is arbitrary and chosen only after the original target is fixed. -/
theorem exists_robust_weights_of_inverse (edge : E → Fin 3 → I)
    (d : ℝ) (hd : 0 < d) (A : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hA : (gram edge + d • roleKernelProjection) * A = 1)
    (hnA : ‖A‖ ≤ 32 / d)
    (hdegree : ∀ v, |(familyDegree edge Finset.univ v : ℝ) - d| ≤ 3 * d / 5000) :
    ∀ F : Finset E, (∀ v, (familyDegree edge F v : ℝ) ≤ d / 1000) →
      ∃ w : ↥((Finset.univ : Finset E) \ F) → ℝ,
        (∀ e, 1 / (2 * d) ≤ w e ∧ w e ≤ 3 / (2 * d)) ∧
        ∀ v, (∑ e, if v ∈ edgeSet (fun e : ↥((Finset.univ : Finset E) \ F) => edge e) e
          then w e else 0) = 1 := by
  intro F hF
  let S := Finset.univ \ F
  let edgeS : S → Fin 3 → I := fun e => edge e
  have hMF : ‖familyGram edge F‖ ≤ 3 * d / 1000 := by
    calc
      ‖familyGram edge F‖ ≤ 3 * (d / 1000) :=
        familyGram_norm_le edge F (d / 1000) (by positivity) hF
      _ = 3 * d / 1000 := by ring
  obtain ⟨A', hA', hnA'⟩ := inverse_sub_bound
    (gram edge + d • roleKernelProjection) A (familyGram edge F) d hd hA hnA hMF
  have hgram : gram edgeS + d • roleKernelProjection =
      (gram edge + d • roleKernelProjection) - familyGram edge F := by
    rw [← familyGram_eq_gram_subtype edge S]
    change familyGram edge (Finset.univ \ F) + d • roleKernelProjection = _
    rw [familyGram_compl]
    abel
  have hA'S : (gram edgeS + d • roleKernelProjection) * A' = 1 := by
    rw [hgram]
    exact hA'
  have hdegS : ∀ v, |(familyDegree edgeS Finset.univ v : ℝ) - d| ≤ (1 / 216) * d := by
    intro v
    rw [familyDegree_subtype edge S v]
    change |(familyDegree edge (Finset.univ \ F) v : ℝ) - d| ≤ _
    rw [familyDegree_compl]
    calc
      |(familyDegree edge Finset.univ v : ℝ) - (familyDegree edge F v : ℝ) - d| =
          |((familyDegree edge Finset.univ v : ℝ) - d) - (familyDegree edge F v : ℝ)| := by
        congr 1
        ring
      _ ≤ |(familyDegree edge Finset.univ v : ℝ) - d| + |(familyDegree edge F v : ℝ)| :=
        abs_sub _ _
      _ ≤ 3 * d / 5000 + d / 1000 := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ (familyDegree edge F v : ℝ) from Nat.cast_nonneg _)]
        exact add_le_add (hdegree v) (hF v)
      _ ≤ (1 / 216) * d := by linarith
  exact exists_positive_perfect_weights edgeS d hd A' hA'S hnA'
    (uniform_deficit_norm_le edgeS d (1 / 216) hd (by norm_num) hdegS)

/-- No inverse or weights are assumed here.  The explicit raw/edit matrix
split is inverted, then every admissible later ban is handled.  The output
contains actual perfect weights on actual allowed edges. -/
theorem exists_robust_weights_of_error_split (edge : E → Fin 3 → I)
    (d : ℝ) (hd : 0 < d)
    (D Ed N : Matrix (Fin 3 × I) (Fin 3 × I) ℝ)
    (hdecomp : gram edge = idealGram d + (D + Ed) + N)
    (hU : ‖normalizeError d (D + Ed)‖ ≤ 1 / 750)
    (hV : ‖normalizeError d N‖ ≤ 50 / 3)
    (hV2 : ‖normalizeError d N * normalizeError d N‖ ≤ 33 / 100000)
    (hdegree : ∀ v, |(familyDegree edge Finset.univ v : ℝ) - d| ≤ 3 * d / 5000) :
    ∀ F : Finset E, (∀ v, (familyDegree edge F v : ℝ) ≤ d / 1000) →
      ∃ w : ↥((Finset.univ : Finset E) \ F) → ℝ,
        (∀ e, 1 / (2 * d) ≤ w e ∧ w e ≤ 3 / (2 * d)) ∧
        ∀ v, (∑ e, if v ∈ edgeSet (fun e : ↥((Finset.univ : Finset E) \ F) => edge e) e
          then w e else 0) = 1 := by
  obtain ⟨A, hA, hnA⟩ := exists_inverse_of_error_split edge d hd D Ed N hdecomp hU hV hV2
  exact exists_robust_weights_of_inverse edge d hd A hA hnA hdegree

end
end EndpointMatching.Fractional.RobustWeights
