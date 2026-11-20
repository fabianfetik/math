import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.CommonThreshold
import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.SourceBite
import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.BiteTrace
/-!
# Constructing source-bite iterations

The AKS one-step statement remains an explicit external argument. This file
constructs actual graph states from it, with one threshold fixed in advance.
-/

open scoped Classical BigOperators
open EndpointMatching.Fractional.Rounding AKSSourceBite

namespace AKSSourceIteration
noncomputable section
universe u

/-- The only nonstandard mathematical input is the explicit source-shaped
one-bite theorem. All numerical choices precede the finite graph. -/
structure Environment where
  K : ℝ
  Dmin : ℝ
  C : ℝ
  Cw : ℝ
  L : ℝ
  C_nonneg : 0 ≤ C
  Cw_nonneg : 0 ≤ Cw
  L_one : 1 ≤ L
  L_min : Dmin ≤ L
  L_exp : Real.exp 1 ≤ L
  budget : (C/L^exponent)/(1-theta^exponent) ≤ 1/2
  contract : ∀ (D Dnext N Nnext eV eD : ℝ), L ≤ D → 0 < N → 0 ≤ Nnext →
    |eV| ≤ C / D^exponent → |eD| ≤ C / D^exponent →
    Nnext ≤ (1-Real.exp (-3))*N*(1+eV) →
    Dnext*N^2 = D*Nnext^2*(1+eD) →
    0 ≤ Dnext ∧ Dnext ≤ theta*D ∧ Nnext ≤ theta*N
  source : SourceBiteTheorem.{u} K Dmin C Cw

variable (E : Environment.{u}) {V : Type u} [Fintype V]

/-- The graph remains simple and 3-uniform. Its degree window is required
whenever the next bite is eligible, and the empty graph has degree zero. -/
structure State where
  vertices : Finset V
  edges : Finset (Finset V)
  degree : ℝ
  degree_nonneg : 0 ≤ degree
  edges_valid : ∀ e ∈ edges, e ⊆ vertices ∧ e.card = 3
  linear : (edges : Set (Finset V)).Pairwise (fun e f => (e ∩ f).card ≤ 1)
  window : E.L ≤ degree → Window vertices edges degree E.K
  empty_degree : vertices = ∅ → degree = 0

def Active (s : State E (V := V)) : Prop := s.vertices.Nonempty ∧ E.L ≤ s.degree

/-- One selected source witness; the source theorem is applied only to
nonempty states still above the common threshold. -/
def chooseBite (s : State E (V := V)) (h : Active E s) :
    Witness s.vertices s.edges s.degree E.K E.Dmin E.C E.Cw :=
  Classical.choice (E.source V s.vertices s.edges s.degree h.1
    (E.L_min.trans h.2) (E.L_exp.trans h.2) (s.window h.2))

theorem chosen_contraction (s : State E (V := V)) (h : Active E s) :
    let b := chooseBite E s h
    let next := remaining s.vertices (isolated b.selected) b.waste
    0 ≤ b.nextDegree ∧ b.nextDegree ≤ theta*s.degree ∧
      (next.card : ℝ) ≤ theta*(s.vertices.card : ℝ) := by
  let b := chooseBite E s h
  have hN : 0 < (s.vertices.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h.1
  have hnext : 0 ≤ ((remaining s.vertices (isolated b.selected) b.waste).card : ℝ) := by positivity
  exact E.contract s.degree b.nextDegree (s.vertices.card : ℝ)
    ((remaining s.vertices (isolated b.selected) b.waste).card : ℝ)
    b.vertexError b.degreeError h.2 hN hnext
    (by simpa [exponent] using b.vertex_error_bound)
    (by simpa [exponent] using b.degree_error_bound) b.vertex_bound b.degree_relation

def stepMatching (s : State E (V := V)) : Finset (Finset V) :=
  if h : Active E s then isolated (chooseBite E s h).selected else ∅

def stepWaste (s : State E (V := V)) : Finset V :=
  if h : Active E s then (chooseBite E s h).waste else ∅

def stepError (s : State E (V := V)) : ℝ :=
  if h : Active E s then (chooseBite E s h).degreeError else 0

/-- A stopped state is left unchanged. An active state is replaced by its
actual induced remaining graph and the source's new degree parameter. -/
def advance (s : State E (V := V)) : State E (V := V) := by
  classical
  by_cases h : Active E s
  · let b := chooseBite E s h
    let U' := remaining s.vertices (isolated b.selected) b.waste
    let H' := induced s.edges U'
    have hshape := induced_uniform_and_linear U' s.edges
      (fun e he => (s.edges_valid e he).2) s.linear
    have hc := chosen_contraction E s h
    exact
      { vertices := U'
        edges := H'
        degree := b.nextDegree
        degree_nonneg := hc.1
        edges_valid := hshape.1
        linear := hshape.2
        window := by
          intro hL
          refine ⟨hshape.1,hshape.2,?_⟩
          exact b.next_window (E.L_min.trans hL) (E.L_one.trans hL)
        empty_degree := by
          intro hempty
          exact empty_next_forces_zero_degree b h.1 hempty }
  · exact s

omit [Fintype V] in
/-- The induced subgraph on a vertex set containing every edge is unchanged. -/
theorem induced_current (s : State E (V := V)) : induced s.edges s.vertices = s.edges := by
  ext e
  simp only [induced, Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h,(s.edges_valid e h).1⟩

theorem advance_vertices (s : State E (V := V)) :
    (advance E s).vertices = remaining s.vertices (stepMatching E s) (stepWaste E s) := by
  classical
  by_cases h : Active E s
  · simp [advance,stepMatching,stepWaste,h]
  · simp [advance,stepMatching,stepWaste,h,remaining,covered]

theorem advance_edges (s : State E (V := V)) :
    (advance E s).edges = induced s.edges (advance E s).vertices := by
  classical
  by_cases h : Active E s
  · simp [advance,h]
  · simp [advance,h,induced_current E s]

theorem step_matching_subset (s : State E (V := V)) : stepMatching E s ⊆ s.edges := by
  classical
  by_cases h : Active E s
  · simpa [stepMatching,h] using
      (isolated_subset (chooseBite E s h).selected).trans (chooseBite E s h).selected_subset
  · simp [stepMatching,h]

theorem step_matching_inside (s : State E (V := V)) :
    ∀ e ∈ stepMatching E s, e ⊆ s.vertices := by
  intro e he
  exact (s.edges_valid e (step_matching_subset E s he)).1

theorem step_is_matching (s : State E (V := V)) : IsMatching id (stepMatching E s) := by
  classical
  by_cases h : Active E s
  · simpa [stepMatching,h] using isolated_isMatching (chooseBite E s h).selected
  · simp [stepMatching,h,IsMatching]

theorem advance_strict_card (s : State E (V := V)) (h : Active E s) :
    (advance E s).vertices.card < s.vertices.card := by
  have hc := chosen_contraction E s h
  have hN : 0 < (s.vertices.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h.1
  have he : 0 < Real.exp (-3) := Real.exp_pos _
  have hlt :
      ((remaining s.vertices (isolated (chooseBite E s h).selected)
        (chooseBite E s h).waste).card : ℝ) < s.vertices.card := by
    have hp := mul_pos he hN
    dsimp [theta] at hc
    nlinarith [hc.2.2]
  have hc' : (remaining s.vertices (isolated (chooseBite E s h).selected)
        (chooseBite E s h).waste).card < s.vertices.card := by exact_mod_cast hlt
  simpa [advance,h] using hc'

theorem active_advance_degree (s : State E (V := V)) (h : Active E s) :
    (advance E s).degree = (chooseBite E s h).nextDegree := by
  simp [advance,h]

theorem active_advance_vertices (s : State E (V := V)) (h : Active E s) :
    (advance E s).vertices =
      remaining s.vertices (isolated (chooseBite E s h).selected) (chooseBite E s h).waste := by
  simp [advance,h]

theorem active_degree_contraction (s : State E (V := V)) (h : Active E s) :
    (advance E s).degree ≤ theta*s.degree := by
  simpa [active_advance_degree E s h] using (chosen_contraction E s h).2.1

theorem active_degree_relation (s : State E (V := V)) (h : Active E s) :
    (advance E s).degree*(s.vertices.card : ℝ)^2 =
      s.degree*((advance E s).vertices.card : ℝ)^2*(1+stepError E s) := by
  simpa [advance,stepError,h] using (chooseBite E s h).degree_relation

theorem active_error_bound (s : State E (V := V)) (h : Active E s) :
    |stepError E s| ≤ E.C/s.degree^exponent := by
  simpa [stepError,h,exponent] using (chooseBite E s h).degree_error_bound

theorem active_waste_bound (s : State E (V := V)) (h : Active E s) :
    ((stepWaste E s).card : ℝ) ≤
      E.Cw*((s.vertices.card : ℝ)/Real.sqrt s.degree)*Real.sqrt (Real.log s.degree) := by
  calc
    ((stepWaste E s).card : ℝ) ≤
        E.Cw*(s.vertices.card : ℝ)/Real.sqrt s.degree*Real.sqrt (Real.log s.degree) := by
      simpa [stepWaste,h] using (chooseBite E s h).waste_bound
    _ = _ := by ring

end
end AKSSourceIteration
