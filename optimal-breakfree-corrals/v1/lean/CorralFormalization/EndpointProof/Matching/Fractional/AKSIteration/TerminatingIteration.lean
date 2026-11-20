import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.GraphStep
import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.TraceRate
/-!
# A terminating source-bite run

Assuming the explicit source-shaped one-bite theorem, repeatedly choose an
actual bite until the common threshold is crossed or the graph is empty.
All later states are padded by empty steps. The final matching rate still
depends on that explicit external source assumption.
-/

open scoped Classical BigOperators
open EndpointMatching.Fractional.Rounding AKSSourceBite

namespace AKSSourceIteration
noncomputable section
universe u

variable (E : Environment.{u}) {V : Type u} [Fintype V]

def run (s0 : State E (V := V)) (i : ℕ) : State E (V := V) :=
  (advance E)^[i] s0

theorem run_succ (s0 : State E (V := V)) (i : ℕ) :
    run E s0 (i+1) = advance E (run E s0 i) := by
  exact Function.iterate_succ_apply' (advance E) i s0

def verticesAt (s0 : State E (V := V)) (i : ℕ) : Finset V := (run E s0 i).vertices
def edgesAt (s0 : State E (V := V)) (i : ℕ) : Finset (Finset V) := (run E s0 i).edges
def degreeAtRun (s0 : State E (V := V)) (i : ℕ) : ℝ := (run E s0 i).degree
def matchingAt (s0 : State E (V := V)) (i : ℕ) : Finset (Finset V) := stepMatching E (run E s0 i)
def wasteAt (s0 : State E (V := V)) (i : ℕ) : Finset V := stepWaste E (run E s0 i)
def errorAt (s0 : State E (V := V)) (i : ℕ) : ℝ := stepError E (run E s0 i)
def errorAllowanceAt (s0 : State E (V := V)) (i : ℕ) : ℝ := E.C/(degreeAtRun E s0 i)^exponent

theorem vertices_step (s0 : State E (V := V)) (i : ℕ) :
    verticesAt E s0 (i+1) = remaining (verticesAt E s0 i) (matchingAt E s0 i) (wasteAt E s0 i) := by
  simp [verticesAt,matchingAt,wasteAt,run_succ,advance_vertices]

theorem edges_step (s0 : State E (V := V)) (i : ℕ) :
    edgesAt E s0 (i+1) = induced (edgesAt E s0 i) (verticesAt E s0 (i+1)) := by
  simp [edgesAt,verticesAt,run_succ,advance_edges]

theorem matching_subset (s0 : State E (V := V)) (i : ℕ) :
    matchingAt E s0 i ⊆ edgesAt E s0 i := step_matching_subset E _

theorem matching_inside (s0 : State E (V := V)) (i : ℕ) :
    ∀ e ∈ matchingAt E s0 i, e ⊆ verticesAt E s0 i := step_matching_inside E _

theorem matching_isMatching (s0 : State E (V := V)) (i : ℕ) :
    IsMatching id (matchingAt E s0 i) := step_is_matching E _

/-- An infinite active run would produce an impossible infinite descending
sequence of natural vertex cardinalities. -/
theorem exists_inactive (s0 : State E (V := V)) :
    ∃ m, ¬ Active E (run E s0 m) := by
  by_contra hn
  have hall : ∀ i, Active E (run E s0 i) := by
    intro i
    by_contra hi
    exact hn ⟨i,hi⟩
  have hcard : ∀ i, (run E s0 i).vertices.card + i ≤ s0.vertices.card := by
    intro i
    induction i with
    | zero => simp [run]
    | succ i ih =>
      have hdrop := advance_strict_card E (run E s0 i) (hall i)
      have hdrop' : (run E s0 (i+1)).vertices.card < (run E s0 i).vertices.card := by
        simpa [run_succ] using hdrop
      omega
  have h := hcard (s0.vertices.card+1)
  omega

def stopIndex (s0 : State E (V := V)) : ℕ := Nat.find (exists_inactive E s0)

theorem inactive_at_stop (s0 : State E (V := V)) :
    ¬ Active E (run E s0 (stopIndex E s0)) := Nat.find_spec (exists_inactive E s0)

theorem active_before_stop (s0 : State E (V := V)) {i : ℕ} (hi : i < stopIndex E s0) :
    Active E (run E s0 i) := by
  exact Classical.not_not.mp (Nat.find_min (exists_inactive E s0) hi)

theorem stop_degree_le (s0 : State E (V := V)) :
    degreeAtRun E s0 (stopIndex E s0) ≤ E.L := by
  let s := run E s0 (stopIndex E s0)
  have hstop : ¬ Active E s := inactive_at_stop E s0
  by_cases hne : s.vertices.Nonempty
  · have hnot : ¬ E.L ≤ s.degree := by
      intro hl
      exact hstop ⟨hne,hl⟩
    exact (lt_of_not_ge hnot).le
  · have hempty : s.vertices = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hz := s.empty_degree hempty
    change s.degree ≤ E.L
    rw [hz]
    linarith [E.L_one]

theorem stop_degree_nonneg (s0 : State E (V := V)) :
    0 ≤ degreeAtRun E s0 (stopIndex E s0) := (run E s0 _).degree_nonneg

theorem active_before_degree (s0 : State E (V := V)) {i : ℕ} (hi : i < stopIndex E s0) :
    E.L ≤ degreeAtRun E s0 i := (active_before_stop E s0 hi).2

theorem active_before_contract (s0 : State E (V := V)) {i : ℕ} (hi : i < stopIndex E s0) :
    degreeAtRun E s0 (i+1) ≤ theta*degreeAtRun E s0 i := by
  simpa [degreeAtRun,run_succ] using
    active_degree_contraction E (run E s0 i) (active_before_stop E s0 hi)

theorem active_before_relation (s0 : State E (V := V)) {i : ℕ} (hi : i < stopIndex E s0) :
    degreeAtRun E s0 (i+1)*(verticesAt E s0 i).card^2 =
      degreeAtRun E s0 i*(verticesAt E s0 (i+1)).card^2*(1+errorAt E s0 i) := by
  simpa [degreeAtRun,verticesAt,errorAt,run_succ] using
    active_degree_relation E (run E s0 i) (active_before_stop E s0 hi)

theorem active_before_error (s0 : State E (V := V)) {i : ℕ} (hi : i < stopIndex E s0) :
    |errorAt E s0 i| ≤ errorAllowanceAt E s0 i := by
  simpa [errorAt,errorAllowanceAt,degreeAtRun] using
    active_error_bound E (run E s0 i) (active_before_stop E s0 hi)

theorem active_before_waste (s0 : State E (V := V)) {i : ℕ} (hi : i < stopIndex E s0) :
    ((wasteAt E s0 i).card : ℝ) ≤ E.Cw*((verticesAt E s0 i).card / Real.sqrt (degreeAtRun E s0 i)) *
      Real.sqrt (Real.log (degreeAtRun E s0 i)) := by
  simpa [wasteAt,verticesAt,degreeAtRun] using
    active_waste_bound E (run E s0 i) (active_before_stop E s0 hi)

/-- A constructed finite run, not an assumed trace, yields the actual
near-perfect matching at the source rate. -/
theorem matching_of_run (s0 : State E (V := V))
    (hvertices : s0.vertices = Finset.univ) (hdegree : Real.exp 1 ≤ s0.degree) :
    ∃ P : Finset (Finset V), P ⊆ s0.edges ∧ IsMatching id P ∧
      ((uncovered id P).card : ℝ) ≤
        (2*(E.Cw*(1+1/(-Real.log theta))+Real.sqrt E.L)) *
          (Fintype.card V : ℝ) * aksRate s0.degree := by
  have hθ := theta_bounds
  have ha : 0 < exponent := by norm_num [exponent]
  have hallow : ∀ i < stopIndex E s0, 0 ≤ errorAllowanceAt E s0 i := by
    intro i hi
    have hD : 0 < degreeAtRun E s0 i := by
      have hL : 0 < E.L := lt_of_lt_of_le (by norm_num) E.L_one
      exact lt_of_lt_of_le hL (active_before_degree E s0 hi)
    exact div_nonneg E.C_nonneg (Real.rpow_pos_of_pos hD exponent).le
  have hresult := AKSBiteTraceRate.matching_with_source_trace_rate
    (verticesAt E s0) (edgesAt E s0) (matchingAt E s0) (wasteAt E s0)
    (degreeAtRun E s0) (errorAt E s0) (errorAllowanceAt E s0)
    (stopIndex E s0) theta exponent E.C E.L E.Cw
    (by simpa [verticesAt,run] using hvertices)
    (vertices_step E s0) (edges_step E s0) (matching_subset E s0)
    (matching_inside E s0) (matching_isMatching E s0)
    hθ.1 hθ.2 ha E.C_nonneg E.L_one E.Cw_nonneg
    (by simpa [degreeAtRun,run] using hdegree)
    (stop_degree_nonneg E s0) (stop_degree_le E s0) hallow
    (fun i hi => active_before_contract E s0 hi)
    (fun i hi => active_before_degree E s0 hi)
    (fun i hi => le_refl _)
    E.budget (fun i hi => active_before_relation E s0 hi)
    (fun i hi => active_before_error E s0 hi)
    (fun i hi => active_before_waste E s0 hi)
  simpa [edgesAt,degreeAtRun,run] using hresult

end
end AKSSourceIteration
