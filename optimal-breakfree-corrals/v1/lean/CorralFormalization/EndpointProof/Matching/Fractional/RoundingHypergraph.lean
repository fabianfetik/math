import CorralFormalization.EndpointProof.Matching.Fractional.RoundingTheorem

/-!
# The three-uniform fractional-perfect application

Only actual supported edges are selected. The selected spanning subhypergraph
has degrees strictly between `D - 3` and `D + 3`, and it inherits uniformity and
linearity. This is the elementary input to a separately assumed near-regular
matching theorem; no Alon--Kim--Spencer theorem is asserted in this file.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.Rounding

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Finite-set version of rounding, selecting only positive input coordinates. -/
theorem exists_selection (A : V → E → Prop) (r : ℕ) (hr : 0 < r)
    (hcol : ∀ e, (columnSupport A e).card ≤ r)
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) :
    ∃ S : Finset E, (∀ e ∈ S, 0 < x e) ∧
      ∀ v, |((rowSupport A S v).card : ℝ) - rowSum A x v| < r := by
  obtain ⟨z, hz, hfrozen, herr⟩ := exists_rounding A r hr hcol x hx
  let S := Finset.univ.filter (fun e => z e = 1)
  have hdegree (v : V) : rowSum A z v = ((rowSupport A S v).card : ℝ) := by
    simp only [rowSum, rowSupport, S, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    rcases hz e with h | h <;> simp [h]
  refine ⟨S, ?_, ?_⟩
  · intro e he
    have hze : z e = 1 := (Finset.mem_filter.mp he).2
    by_contra hn
    have hxe : x e = 0 := le_antisymm (le_of_not_gt hn) (hx e).1
    have hnot : e ∉ fractional x := by simp [mem_fractional, hxe]
    have hf := hfrozen e hnot
    simp [hze, hxe] at hf
  · intro v
    simpa only [hdegree] using herr v

/-- The (spanning) degree in the subfamily `S` of an indexed finite hypergraph. -/
def degree (edges : E → Finset V) (S : Finset E) (v : V) : ℕ :=
  (S.filter (fun e => v ∈ edges e)).card

/-- Distinct indexed edges meet in at most one vertex. -/
def IsLinear (edges : E → Finset V) : Prop :=
  ∀ e f, e ≠ f → ((edges e) ∩ (edges f)).card ≤ 1

/-- A fractional perfect certificate is rounded to an actual edge subfamily
whose degree at every actual vertex differs from `D` by strictly less than
three. The linearity hypothesis is unnecessary for this elementary step. -/
theorem diffuse_perfect_degree_selection (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card ≤ 3) (D : ℕ) (hD : 0 < D)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ))
    (hperfect : ∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) :
    ∃ S : Finset E, (∀ e ∈ S, 0 < w e) ∧
      ∀ v, |(degree edges S v : ℝ) - (D : ℝ)| < 3 := by
  let A : V → E → Prop := fun v e => v ∈ edges e
  let x : E → ℝ := fun e => (D : ℝ) * w e
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hcol : ∀ e, (columnSupport A e).card ≤ 3 := by
    intro e
    simpa [A, columnSupport] using huniform e
  have hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1 := by
    intro e
    constructor
    · exact mul_nonneg hDreal.le (hw e).1
    · calc
        x e ≤ (D : ℝ) * (1 / (D : ℝ)) := mul_le_mul_of_nonneg_left (hw e).2 hDreal.le
        _ = 1 := by field_simp
  have hload (v : V) : rowSum A x v = (D : ℝ) := by
    calc
      rowSum A x v = (D : ℝ) * (∑ e, if v ∈ edges e then w e else 0) := by
        unfold rowSum x A
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> simp
      _ = (D : ℝ) := by rw [hperfect, mul_one]
  obtain ⟨S, hsupp, herror⟩ := exists_selection A 3 (by decide) hcol x hx
  refine ⟨S, ?_, ?_⟩
  · intro e he
    have hpos := hsupp e he
    have hwne : w e ≠ 0 := by
      intro hzero
      simp [x, hzero] at hpos
    exact lt_of_le_of_ne (hw e).1 (Ne.symm hwne)
  · intro v
    simpa only [rowSupport, A, degree, hload, Nat.cast_ofNat] using herror v

/-- Integer degrees improve the displayed real interval to
`D ≤ degree + 2` and `degree ≤ D + 2`. -/
theorem diffuse_perfect_degree_selection_nat (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card ≤ 3) (D : ℕ) (hD : 0 < D)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ))
    (hperfect : ∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) :
    ∃ S : Finset E, (∀ e ∈ S, 0 < w e) ∧
      ∀ v, D ≤ degree edges S v + 2 ∧ degree edges S v ≤ D + 2 := by
  obtain ⟨S, hsupp, herr⟩ := diffuse_perfect_degree_selection edges huniform D hD w hw hperfect
  refine ⟨S, hsupp, ?_⟩
  intro v
  have hv := abs_lt.mp (herr v)
  have hlo : D < degree edges S v + 3 := by
    exact_mod_cast (show (D : ℝ) < (degree edges S v : ℝ) + 3 by linarith [hv.1])
  have hhi : degree edges S v < D + 3 := by
    exact_mod_cast (show (degree edges S v : ℝ) < (D : ℝ) + 3 by linarith [hv.2])
  omega

/-- The paper's actual linear three-uniform application. At `Δ = D + 3`,
the selected spanning subhypergraph lies in `[Δ - 6, Δ]` and inherits both
structural hypotheses needed by the separate external matching input. -/
theorem linear_three_uniform_near_regular (edges : E → Finset V)
    (huniform : ∀ e, (edges e).card = 3) (hlinear : IsLinear edges)
    (D : ℕ) (hD : 0 < D)
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ))
    (hperfect : ∀ v, (∑ e, if v ∈ edges e then w e else 0) = 1) :
    ∃ S : Finset E, (∀ e ∈ S, 0 < w e) ∧
      (∀ e : S, (edges e).card = 3) ∧ IsLinear (fun e : S => edges e) ∧
      (∀ v, |(degree edges S v : ℝ) - (D : ℝ)| < 3) ∧
      ∀ v, ((D : ℝ) + 3) - 6 ≤ degree edges S v ∧
        (degree edges S v : ℝ) ≤ (D : ℝ) + 3 := by
  obtain ⟨S, hsupp, herr⟩ := diffuse_perfect_degree_selection edges
    (fun e => (huniform e).le) D hD w hw hperfect
  refine ⟨S, hsupp, (fun e => huniform e), ?_, herr, ?_⟩
  · intro e f hne
    exact hlinear e f (fun hef => hne (Subtype.ext hef))
  · intro v
    have hv := abs_lt.mp (herr v)
    constructor <;> linarith

end
end EndpointMatching.Fractional.Rounding
