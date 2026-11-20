import CorralFormalization.EndpointProof.Matching.Fractional.RoundingAKSSource
import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.Contraction
/-!
# The three-uniform AKS bite as an explicit external contract

This file unpacks the source's one-step statement into actual finite vertex
and edge sets. It assumes that statement; no random-bite existence proof is
asserted. In particular the source's vertex estimate is only one-sided and
the next vertex set is allowed to be empty.
-/

open scoped Classical BigOperators
open EndpointMatching.Fractional.Rounding

namespace AKSSourceBite
noncomputable section
universe u

variable {V : Type u} [Fintype V]

/-- Isolated selected edges are the matching used in the source's bite. -/
def isolated (X : Finset (Finset V)) : Finset (Finset V) :=
  X.filter (fun e => ∀ f ∈ X, f ≠ e → Disjoint e f)

def covered (M : Finset (Finset V)) : Finset V := M.biUnion id

/-- Wasted vertices may overlap matched vertices, as in the source. -/
def remaining (U : Finset V) (M : Finset (Finset V)) (W : Finset V) : Finset V :=
  U \ (covered M ∪ W)

def induced (H : Finset (Finset V)) (U : Finset V) : Finset (Finset V) :=
  H.filter (fun e => e ⊆ U)

def degreeAt (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

/-- One actual finite simple 3-graph with its near-regular degree window. -/
def Window (U : Finset V) (H : Finset (Finset V)) (D K : ℝ) : Prop :=
  (∀ e ∈ H, e ⊆ U ∧ e.card = 3) ∧
  ((H : Set (Finset V)).Pairwise (fun e f => (e ∩ f).card ≤ 1)) ∧
  ∀ v ∈ U, D - K*Real.sqrt D*Real.sqrt (Real.log D) ≤ (degreeAt H v : ℝ) ∧
    (degreeAt H v : ℝ) ≤ D

/-- At the initial full vertex set, the source window is supplied by
exactly the uniformity, linearity and degree hypotheses of the maintained
finite-set AKS input. -/
theorem window_univ_of_project_hypotheses (H : Finset (Finset V)) (D K : ℝ)
    (huniform : ∀ e ∈ H, e.card = 3)
    (hlinear : (H : Set (Finset V)).Pairwise (fun e f => (e ∩ f).card ≤ 1))
    (hdegree : ∀ v, D - K*Real.sqrt D*Real.sqrt (Real.log D) ≤ (degree id H v : ℝ) ∧
      (degree id H v : ℝ) ≤ D) : Window Finset.univ H D K := by
  refine ⟨?_,hlinear,?_⟩
  · intro e he
    exact ⟨Finset.subset_univ e, huniform e he⟩
  · intro v hv
    simpa [degreeAt,degree] using hdegree v

/-- Explicit outputs of a single source-shaped bite. `C` uniformly bounds
the two relative errors; `Cw` bounds the wasted vertices. The output degree
window is required when it can be needed for another large-degree step. -/
structure Witness (U : Finset V) (H : Finset (Finset V))
    (D K Dmin C Cw : ℝ) where
  selected : Finset (Finset V)
  waste : Finset V
  nextDegree : ℝ
  vertexError : ℝ
  degreeError : ℝ
  selected_subset : selected ⊆ H
  waste_subset : waste ⊆ U
  waste_bound : (waste.card : ℝ) ≤
    Cw * (U.card : ℝ) / Real.sqrt D * Real.sqrt (Real.log D)
  vertex_error_bound : |vertexError| ≤ C / D^((2:ℝ)/5)
  degree_error_bound : |degreeError| ≤ C / D^((2:ℝ)/5)
  vertex_bound :
    ((remaining U (isolated selected) waste).card : ℝ) ≤
      (1-Real.exp (-3)) * (U.card : ℝ) * (1+vertexError)
  degree_relation : nextDegree * (U.card : ℝ)^2 =
    D * ((remaining U (isolated selected) waste).card : ℝ)^2 * (1+degreeError)
  next_window : Dmin ≤ nextDegree → 1 ≤ nextDegree →
    ∀ v ∈ remaining U (isolated selected) waste,
      nextDegree - K*Real.sqrt nextDegree*Real.sqrt (Real.log nextDegree) ≤
          (degreeAt (induced H (remaining U (isolated selected) waste)) v : ℝ) ∧
      (degreeAt (induced H (remaining U (isolated selected) waste)) v : ℝ) ≤ nextDegree

/-- Explicit external input: one nonempty large-degree bite. The source's
hidden constants are fixed before the finite graph. The `exp 1` condition
and the restriction to nonempty graphs weaken the input used here. -/
def SourceBiteTheorem (K Dmin C Cw : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] (U : Finset V) (H : Finset (Finset V)) (D : ℝ),
    U.Nonempty → Dmin ≤ D → Real.exp 1 ≤ D → Window U H D K →
    Nonempty (Witness U H D K Dmin C Cw)

/-- If a bite empties a nonempty vertex set, the source's exact
degree/vertex relation forces its next degree parameter to be zero. -/
theorem empty_next_forces_zero_degree {U : Finset V} {H : Finset (Finset V)}
    {D K Dmin C Cw : ℝ} (b : Witness U H D K Dmin C Cw)
    (hU : U.Nonempty) (hempty : remaining U (isolated b.selected) b.waste = ∅) :
    b.nextDegree = 0 := by
  have hN : 0 < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU
  have hp : (U.card : ℝ)^2 ≠ 0 := pow_ne_zero _ (ne_of_gt hN)
  have hprod : b.nextDegree * (U.card : ℝ)^2 = 0 := by
    simpa [hempty] using b.degree_relation
  exact (mul_eq_zero.mp hprod).resolve_right hp

/-- At positive input degree, a zero next degree implies an empty next
vertex set whenever the source's relative error is greater than -1. -/
theorem zero_next_degree_forces_empty {U : Finset V} {H : Finset (Finset V)}
    {D K Dmin C Cw : ℝ} (b : Witness U H D K Dmin C Cw)
    (hD : 0 < D) (herr : -1 < b.degreeError) (hzero : b.nextDegree = 0) :
    remaining U (isolated b.selected) b.waste = ∅ := by
  have hsum : 0 < 1+b.degreeError := by linarith
  have hprod : D * ((remaining U (isolated b.selected) b.waste).card : ℝ)^2 *
      (1+b.degreeError) = 0 := by
    simpa [hzero] using b.degree_relation.symm
  have hsquare : ((remaining U (isolated b.selected) b.waste).card : ℝ)^2 = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hD)
    · exact False.elim ((ne_of_gt hsum) h)
  have hcard : (remaining U (isolated b.selected) b.waste).card = 0 := by
    have hr : ((remaining U (isolated b.selected) b.waste).card : ℝ) = 0 :=
      (sq_eq_zero_iff).mp hsquare
    exact_mod_cast hr
  exact Finset.card_eq_zero.mp hcard

theorem isolated_subset (X : Finset (Finset V)) : isolated X ⊆ X :=
  Finset.filter_subset _ _

theorem isolated_isMatching (X : Finset (Finset V)) :
    IsMatching id (isolated X) := by
  intro e he f hf hne
  exact (Finset.mem_filter.mp he).2 f (Finset.mem_filter.mp hf).1 hne.symm

omit [Fintype V] in
theorem remaining_subset (U : Finset V) (M : Finset (Finset V)) (W : Finset V) :
    remaining U M W ⊆ U := Finset.sdiff_subset

omit [Fintype V] in
/-- Every vertex not covered by the bite matching is either in the actual
new vertex set or is among the wasted vertices. No disjointness of waste
from the matching is assumed. -/
theorem uncovered_subset_remaining_or_waste
    (U : Finset V) (M : Finset (Finset V)) (W : Finset V) :
    U \ covered M ⊆ remaining U M W ∪ W := by
  intro v hv
  have hvU := (Finset.mem_sdiff.mp hv).1
  have hvM := (Finset.mem_sdiff.mp hv).2
  by_cases hvW : v ∈ W
  · exact Finset.mem_union_right _ hvW
  · apply Finset.mem_union_left
    exact Finset.mem_sdiff.mpr ⟨hvU, by
      simp only [Finset.mem_union, not_or]
      exact ⟨hvM,hvW⟩⟩

omit [Fintype V] in
theorem uncovered_card_le (U : Finset V) (M : Finset (Finset V)) (W : Finset V) :
    (U \ covered M).card ≤ (remaining U M W).card + W.card := by
  exact (Finset.card_le_card (uncovered_subset_remaining_or_waste U M W)).trans
    (Finset.card_union_le _ _)

omit [Fintype V] in
theorem induced_uniform_and_linear (U : Finset V) (H : Finset (Finset V))
    (huniform : ∀ e ∈ H, e.card = 3)
    (hlinear : (H : Set (Finset V)).Pairwise (fun e f => (e ∩ f).card ≤ 1)) :
    (∀ e ∈ induced H U, e ⊆ U ∧ e.card = 3) ∧
      ((induced H U : Set (Finset V)).Pairwise (fun e f => (e ∩ f).card ≤ 1)) := by
  constructor
  · intro e he
    have he' := Finset.mem_filter.mp he
    exact ⟨he'.2, huniform e he'.1⟩
  · exact hlinear.mono (Finset.filter_subset _ _)

/-- One actual matching step from the external bite contract. Its fixed
contraction factor is derived from the source-shaped numerical outputs,
and the unmatched-set estimate permits waste/matching overlap. -/
theorem one_actual_bite (K Dmin C Cw : ℝ) (hC : 0 ≤ C)
    (hsource : SourceBiteTheorem.{u} K Dmin C Cw) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (V : Type u) [Fintype V]
      (U : Finset V) (H : Finset (Finset V)) (D : ℝ),
      U.Nonempty → L ≤ D → Dmin ≤ D → Real.exp 1 ≤ D → Window U H D K →
      ∃ b : Witness U H D K Dmin C Cw,
        isolated b.selected ⊆ H ∧ IsMatching id (isolated b.selected) ∧
        0 ≤ b.nextDegree ∧
        b.nextDegree ≤ ((2-Real.exp (-3))/2)*D ∧
        ((remaining U (isolated b.selected) b.waste).card : ℝ) ≤
          ((2-Real.exp (-3))/2)*(U.card : ℝ) ∧
        (U \ covered (isolated b.selected)).card ≤
          (remaining U (isolated b.selected) b.waste).card + b.waste.card := by
  obtain ⟨L,hL,hcontr⟩ := AKSSourceContraction.three_uniform_source_step C hC
  refine ⟨L,hL,?_⟩
  intro V _ U H D hU hLD hmin hexp hwindow
  obtain ⟨b⟩ := hsource V U H D hU hmin hexp hwindow
  have hN : 0 < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU
  have hNnext : 0 ≤ ((remaining U (isolated b.selected) b.waste).card : ℝ) := by positivity
  have hc := hcontr D b.nextDegree (U.card : ℝ)
    ((remaining U (isolated b.selected) b.waste).card : ℝ)
    b.vertexError b.degreeError hLD hN hNnext b.vertex_error_bound
    b.degree_error_bound b.vertex_bound b.degree_relation
  refine ⟨b, (isolated_subset b.selected).trans b.selected_subset,
    isolated_isMatching b.selected, hc.1, hc.2.1, hc.2.2, ?_⟩
  exact uncovered_card_le U (isolated b.selected) b.waste

/-- Each nonempty admissible bite strictly reduces the number of actual
remaining vertices. Thus vertex cardinality is available as a termination
measure for the finite construction of a complete trace in
`TerminatingIteration`. -/
theorem one_actual_bite_strict_card_drop (K Dmin C Cw : ℝ) (hC : 0 ≤ C)
    (hsource : SourceBiteTheorem.{u} K Dmin C Cw) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (V : Type u) [Fintype V]
      (U : Finset V) (H : Finset (Finset V)) (D : ℝ),
      U.Nonempty → L ≤ D → Dmin ≤ D → Real.exp 1 ≤ D → Window U H D K →
      ∃ b : Witness U H D K Dmin C Cw,
        (remaining U (isolated b.selected) b.waste).card < U.card ∧
        isolated b.selected ⊆ H ∧ IsMatching id (isolated b.selected) ∧
        0 ≤ b.nextDegree ∧ b.nextDegree ≤ ((2-Real.exp (-3))/2)*D := by
  obtain ⟨L,hL,hbite⟩ := one_actual_bite K Dmin C Cw hC hsource
  refine ⟨L,hL,?_⟩
  intro V _ U H D hU hLD hmin hexp hwindow
  obtain ⟨b,hsub,hmatch,hpos,hD,hN,_⟩ := hbite V U H D hU hLD hmin hexp hwindow
  have hNpos : 0 < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU
  have he : 0 < Real.exp (-3) := Real.exp_pos _
  have hdrop : ((remaining U (isolated b.selected) b.waste).card : ℝ) < U.card := by
    have hp := mul_pos he hNpos
    nlinarith
  refine ⟨b,?_,hsub,hmatch,hpos,hD⟩
  exact_mod_cast hdrop

end
end AKSSourceBite
