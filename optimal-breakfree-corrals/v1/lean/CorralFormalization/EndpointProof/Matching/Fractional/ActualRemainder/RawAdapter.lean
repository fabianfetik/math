import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Physical
import CorralFormalization.EndpointProof.Matching.Fractional.RawEvent.Candidates

/-!
# Deterministic remainder on the same fractional raw event

The raw event supplies the rooted zero-edge degree and actual-size collar.
This adapter takes the bounded interval fractional-perfect certificate on
every actual allowed complement as an explicit input.  Later modules supply
that input from the same raw event, under the appropriate ban budget.  A
finished near matching is nowhere assumed here.
-/

open scoped Classical BigOperators

namespace EndpointMatching.Fractional.ActualRemainder

open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open EndpointMatching.Fractional.Rounding
open EndpointFullProduct EndpointFractionalRawEvent

noncomputable section

universe u

variable {G : Type u} [Fintype G] [AddCommGroup G]

/-- The fractional-weight supplier interface on the canonical actual edges.
The ban is already part of the edge type, and every actual vertex has unit
load.  This source asserts fractional weights only. -/
def ActualFractionalWeights (R : Finset (Vertex G))
    (F : Finset (Finset (Vertex G))) (q radius : ℝ) : Prop :=
  ∀ W : Finset (Vertex G), Balanced W → (∀ v ∈ W, v.2 ≠ 0) →
    (taggedDistance R W : ℝ) ≤ radius →
    ∃ w : AllowedEdge W F → ℝ,
      (∀ e, 1 / (2 * (q * ((slice W 0).card : ℝ))) ≤ w e ∧
        w e ≤ 3 / (2 * (q * ((slice W 0).card : ℝ)))) ∧
      ∀ v : W, (∑ e, if v ∈ localEdge e then w e else 0) = 1

/-- The original common raw event already pays the collar on every later
actual tagged inventory; target Fourier accuracy is not assumed. -/
theorem fractionalRawEvent_tagged_size_bounds {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    {s : OriginalSample G} (hraw : fractionalRawEvent q s)
    (W : Finset (Vertex G))
    (hdist : (taggedDistance (signedRawTarget s) W : ℝ) ≤
      rho q * (Fintype.card G : ℝ)) :
    q * (Fintype.card G : ℝ) / 2 ≤ ((slice W 0).card : ℝ) ∧
      ((slice W 0).card : ℝ) ≤ 2 * q * (Fintype.card G : ℝ) := by
  have hcard : (slice (signedRawTarget s) 0).card = (rawSet s 0).card := by
    rw [signedRawTarget, signedTarget_slice_tail, Finset.card_image_of_injective]
    exact fun a b h => neg_injective (congrArg Prod.snd h)
  have hsize := hraw.1.rawSize (0 : Fin 3)
  have hchange := taggedDistance_slice_size_bound (signedRawTarget s) W (0 : Fin 3)
  rw [hcard] at hchange
  have herror : |((slice W 0).card : ℝ) - q * (Fintype.card G : ℝ)| ≤
      (epsilon q + rho q) * (Fintype.card G : ℝ) := by
    calc
      _ ≤ |((slice W 0).card : ℝ) - ((rawSet s 0).card : ℝ)| +
          |((rawSet s 0).card : ℝ) - q * (Fintype.card G : ℝ)| := abs_sub_le _ _ _
      _ ≤ (taggedDistance (signedRawTarget s) W : ℝ) +
          epsilon q * (Fintype.card G : ℝ) := add_le_add hchange hsize
      _ ≤ _ := by linarith
  have hsmall := mul_le_mul_of_nonneg_right (epsilon_add_rho_le_half_q q hq.le hqhalf)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  have herr := abs_le.mp herror
  have hqn : 0 ≤ q * (Fintype.card G : ℝ) := by positivity
  constructor <;> nlinarith

/-- From the same raw event, the analytic fractional-only supplier yields
the full interval source; no new event or probability union is introduced. -/
theorem intervalFractionalSupply_of_raw_event {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    {s : OriginalSample G} (hraw : fractionalRawEvent q s)
    {F : Finset (Finset (Vertex G))}
    (hweights : ActualFractionalWeights (signedRawTarget s) F q
      (rho q * (Fintype.card G : ℝ))) :
    IntervalFractionalSupply (signedRawTarget s) F q (Fintype.card G)
      (rho q * (Fintype.card G : ℝ)) := by
  intro W hW hnz hdist
  obtain ⟨hlower, hupper⟩ := fractionalRawEvent_tagged_size_bounds hq hqhalf hraw W hdist
  exact ⟨hlower, hupper, hweights W hW hnz hdist⟩

/-- The explicit raw degree event pays every zero-endpoint request after
arbitrary target edits, a reserved inventory, a frozen matching and an
allowed later ban.  All actual collisions were charged by RootedCounting. -/
theorem zero_edge_of_fractionalRawEvent {q : ℝ} (hq : 0 < q)
    {s : OriginalSample G} (hraw : fractionalRawEvent q s)
    {X Y C : Finset G} {A P : Finset (Vertex G)} (M₀ : Matching P)
    (F : Finset (Finset (Vertex G))) (hC : (0 : G) ∉ C)
    (hban : ∀ z, ((banAt F z).card : ℝ) ≤ beta q * (Fintype.card G : ℝ))
    (hbudget : (taggedDistance (signedRawTarget s) (signedTarget X Y C) : ℝ) +
      (A.card : ℝ) + 3 * (M₀.edges.card : ℝ) +
      (zeroCharge (residual (signedTarget X Y C) A P) : ℝ) ≤
        rho q * (Fintype.card G : ℝ)) :
    ∀ z ∈ residual (signedTarget X Y C) A P, z.2 = 0 →
      ∃ E : Finset (Vertex G), Hyperedge E ∧
        E ⊆ residual (signedTarget X Y C) A P ∧ z ∈ E ∧ E ∉ F := by
  apply zero_edge_from_raw_real_bounds M₀ F
    ((q ^ 2 - rho q) * (Fintype.card G : ℝ)) (beta q * (Fintype.card G : ℝ))
    (vertexCandidates s) (vertexCandidates_valid s) (vertexCandidates_root s)
      (vertexCandidates_inside s) ?_ hban ?_
  · intro z hz _
    apply hraw.2.vertexCandidates_lower z
    intro hp hz0
    have hzT := (Finset.mem_sdiff.mp hz).1
    have hzeq : z = (2, 0) := Prod.ext hp hz0
    have hmem : (2, -(0 : G)) ∈ signedTarget X Y C := by simpa using hzeq ▸ hzT
    exact hC ((signedTarget_color_mem X Y C 0).mp hmem)
  · have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hpositive : rho q + beta q < q ^ 2 - rho q := by
      unfold rho beta
      nlinarith [sq_pos_of_pos hq]
    have hmargin := mul_lt_mul_of_pos_right hpositive hn
    have hmissing : ((signedRawTarget s \ signedTarget X Y C).card : ℝ) ≤
        (taggedDistance (signedRawTarget s) (signedTarget X Y C) : ℝ) := by
      unfold taggedDistance
      simp only [Nat.cast_add]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    have hcharge : (0 : ℝ) ≤ zeroCharge (residual (signedTarget X Y C) A P) :=
      Nat.cast_nonneg _
    linarith

/-- The deterministic actual-remainder lemma on the proved common raw
event.  Constants precede the group type and every later choice.  The sole
remaining supplier premise is fractional-perfect interval weights on the
actual allowed complements; a near matching is constructed, not assumed.

The exact external matching premise is `AKSSetFamilyTheorem`.  The explicit
order threshold pays the floor degree and AKS scale.  Numerical zero is
covered separately before calling the fractional supplier, and every
deleted vertex and banned rooted edge is paid in the displayed budget. -/
theorem physical_actual_remainder_on_raw_event
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C) :
    ∃ (Dstar : ℕ) (Cstar : ℝ), 3 ≤ Dstar ∧ 0 < Cstar ∧
      ∀ (H : Type u) [Fintype H] [AddCommGroup H]
        (q : ℝ) (s : OriginalSample H) (X Y C : Finset H)
        (A P : Finset (Vertex H)) (M₀ : Matching P) (F : Finset (Finset (Vertex H))),
        0 < q → q ≤ 1 / 2 → fractionalRawEvent q s →
        Disjoint X Y → (0 : H) ∉ C → X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        Balanced A → (∑ v ∈ A, v.2 = 0) → A ⊆ signedTarget X Y C →
        P ⊆ signedTarget X Y C \ A → (∀ E ∈ M₀.edges, E ∉ F) →
        (∀ z, ((banAt F z).card : ℝ) ≤ beta q * (Fintype.card H : ℝ)) →
        (taggedDistance (signedRawTarget s) (signedTarget X Y C) : ℝ) + (A.card : ℝ) +
          3 * (M₀.edges.card : ℝ) + (zeroCharge (residual (signedTarget X Y C) A P) : ℝ)
            ≤ rho q * (Fintype.card H : ℝ) →
        6 * (Dstar : ℝ) ≤ q ^ 2 * (Fintype.card H : ℝ) →
        ActualFractionalWeights (signedRawTarget s) F q (rho q * (Fintype.card H : ℝ)) →
        ∃ M : ActualRemainderMatching (signedTarget X Y C) A P M₀ F,
          (∀ p : Fin 3, ((slice (residual (signedTarget X Y C) A M.covered) p).card : ℝ)
            ≤ Real.sqrt 6 * Cstar * remainderProfile (Fintype.card H)) ∧
          ((residual (signedTarget X Y C) A M.covered).card : ℝ) ≤
            3 * (Real.sqrt 6 * Cstar) * remainderProfile (Fintype.card H) := by
  obtain ⟨Dstar, Cstar, hstar, hCstar, hphysical⟩ :=
    physical_actual_remainder_of_fractional_uniform hAKS
  refine ⟨Dstar, Cstar, hstar, hCstar, ?_⟩
  intro H _ _ q s X Y C A P M₀ F hq hqhalf hraw hXY hC hsizeXY hsizeXC hsum
    hA hAsum hAT hP hallowed hban hbudget hlarge hweights
  have hinterval := intervalFractionalSupply_of_raw_event hq hqhalf hraw hweights
  have hquant := quantitativeFractionalSupply_of_interval q (Fintype.card H)
    (rho q * (Fintype.card H : ℝ)) Dstar hq hqhalf hstar hlarge hinterval
  have hzero := zero_edge_of_fractionalRawEvent hq hraw M₀ F hC hban hbudget
  exact hphysical H q (Fintype.card H) (rho q * (Fintype.card H : ℝ)) (signedRawTarget s)
    X Y C A P M₀ F hq hXY hC hsizeXY hsizeXC hsum hA hAsum hAT hP hallowed
    hzero hbudget hquant

end
end EndpointMatching.Fractional.ActualRemainder
