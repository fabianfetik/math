import CorralFormalization.EndpointProof.Transitions.PippengerRounding
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Adapter
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.Physical
import CorralFormalization.EndpointProof.Matching.Fractional.ActualRemainder.RawAdapter
import CorralFormalization.EndpointProof.Matching.UniformExactMatching
import CorralFormalization.EndpointProof.Probability.LayeredSample.Joint
import CorralFormalization.EndpointProof.Probability.LayeredSample.RouterReservoir

/-!
# Qualitative fractional matching from Pippenger

Pippenger remains an explicit theorem argument. The quantitative AKS rate
is not asserted by this qualitative route. The raw-event and common-sample
results connect it to the existing exact receiver and router.
-/

open scoped Classical BigOperators
open MeasureTheory Filter Topology
open EndpointTransitions EndpointMatching.Fractional.Rounding
open EndpointMatching.Fractional.ActualRemainder
open EndpointFlow.AbelianTransport
open EndpointMatching.AbsorptionAssembly
open EndpointFullProduct EndpointFractionalRawEvent
open EndpointMatching.UniversalCore EndpointMatching.Fractional.RobustWeights
open EndpointMatching.Fractional.Fourier
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
open EndpointLayeredSample

namespace EndpointPippenger

noncomputable section

universe u v

/-- Fractional perfect weights capped by `1/D` give a near-perfect matching
    with arbitrary fixed relative error, using only Pippenger's input. -/
theorem fractional_near_perfect_from_pippenger
    (hPippenger : PippengerTheorem.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Dstar : ℕ, 1 ≤ Dstar ∧
      ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        (edges : E → Finset V), (∀ e, (edges e).card = 3) → IsLinear edges →
        ∀ D : ℕ, Dstar ≤ D → ∀ w : E → ℝ,
          (∀ e, 0 ≤ w e ∧ w e ≤ 1 / (D : ℝ)) →
          (∀ x, (∑ e, if x ∈ edges e then w e else 0) = 1) →
          ∃ M : Finset E, IsMatching edges M ∧ (∀ e ∈ M, 0 < w e) ∧
            (uncovered edges M).card ≤ ε * (Fintype.card V : ℝ) := by
  classical
  obtain ⟨μ, hμ, hμhalf, hsource⟩ := hPippenger.choose_mu ε hε
  obtain ⟨Dstar, hDstar⟩ := exists_nat_ge (max (1 : ℝ) (3 + 8/μ))
  have hstar : 1 ≤ Dstar := by
    have hh : (1 : ℝ) ≤ Dstar := (le_max_left _ _).trans hDstar
    exact_mod_cast hh
  refine ⟨Dstar, hstar, ?_⟩
  intro V E _ _ edges huniform hlinear D hD w hw hload
  have hDreal : (Dstar : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by
    have hn : 1 ≤ D := hstar.trans hD
    exact_mod_cast hn
  have hbig : 3 + 8/μ ≤ (D : ℝ) := (le_max_right _ _).trans (hDstar.trans hDreal)
  have hmul : 8 ≤ μ * ((D : ℝ) - 3) := by
    have hh : 8/μ ≤ (D : ℝ) - 3 := by linarith
    simpa only [mul_comm] using (div_le_iff₀ hμ).mp hh
  have hwindow : 2*((0 : ℝ)+3) ≤ μ*((D : ℝ)-((0 : ℝ)+3)) := by linarith
  have hcodegree : 1 < μ*((D : ℝ)-((0 : ℝ)+3)) := by linarith
  have hscaled : ∀ e, 0 ≤ (D : ℝ)*w e ∧ (D : ℝ)*w e ≤ 1 := by
    intro e
    refine ⟨mul_nonneg hDpos.le (hw e).1, ?_⟩
    have hupper := mul_le_mul_of_nonneg_left (hw e).2 hDpos.le
    have hunit : (D : ℝ) * (1 / (D : ℝ)) = 1 := by field_simp
    simpa only [hunit] using hupper
  have hscaledload : ∀ x,
      |(∑ e, if x ∈ edges e then (D : ℝ)*w e else 0)-(D : ℝ)| ≤ 0 := by
    intro x
    have hsum : (∑ e, if x ∈ edges e then (D : ℝ)*w e else 0) =
        (D : ℝ) * (∑ e, if x ∈ edges e then w e else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    rw [hsum, hload x]
    simp
  obtain ⟨M, hM, hsupp, hrest⟩ := weighted_near_perfect_matching
    edges huniform hlinear (fun e => (D : ℝ)*w e) hscaled
    μ ε (D : ℝ) 0 hμ (by linarith) (by norm_num) hwindow hcodegree
    hscaledload (hsource V)
  refine ⟨M, hM, ?_, hrest⟩
  intro e he
  exact (mul_pos_iff_of_pos_left hDpos).mp (hsupp e he)

/-- The same qualitative bound on the actual tagged inventory and the
    actual allowed edges, with no padding or extra forbidden-edge premise. -/
theorem actual_matching_from_fractional_pippenger
    (hPippenger : PippengerTheorem.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Dstar : ℕ, 1 ≤ Dstar ∧
      ∀ (H : Type u) [AddCommGroup H]
        (W : Finset (Vertex H)) (F : Finset (Finset (Vertex H)))
        (D : ℕ), Dstar ≤ D → FractionalPerfect W F D →
        ∃ (P : Finset (Vertex H)) (M : Matching P), P ⊆ W ∧
          (∀ edge ∈ M.edges, edge ∉ F) ∧
          ((W \ P).card : ℝ) ≤ ε * (W.card : ℝ) := by
  classical
  obtain ⟨Dstar, hstar, hmatch⟩ :=
    fractional_near_perfect_from_pippenger hPippenger ε hε
  refine ⟨Dstar, hstar, ?_⟩
  intro H _ W F D hD hfrac
  obtain ⟨w, hw, hperfect⟩ := hfrac
  obtain ⟨M, hM, _, hrest⟩ := hmatch W (AllowedEdge W F)
    (localEdge (W := W) (F := F)) localEdge_uniform (localEdge_linear W F)
    D hD w hw (fun v => by
      calc
        _ = ∑ e, if v ∈ localEdge e then w e else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases hm : v ∈ localEdge e <;> simp only [hm, if_true, if_false]
        _ = 1 := hperfect v)
  refine ⟨actualCovered M, actualMatching M hM, actualCovered_inside M,
    actualMatching_allowed M hM, ?_⟩
  simpa only [uncovered_card_eq_actual M, Fintype.card_coe] using hrest

/-- The actual later remainder after a reserved core, frozen matching and
    zero step. Its size is qualitative: at most the chosen fixed fraction. -/
theorem actual_remainder_after_zero_step_pippenger
    (hPippenger : PippengerTheorem.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧
      ∀ (H : Type u) [AddCommGroup H]
        (T A P : Finset (Vertex H)) (M₀ : Matching P)
        (F : Finset (Finset (Vertex H))),
        Balanced T → (∑ v ∈ T, v.2 = 0) → Balanced A →
        (∑ v ∈ A, v.2 = 0) → A ⊆ T → P ⊆ T \ A →
        (∀ edge ∈ M₀.edges, edge ∉ F) →
        ∀ (Z : ZeroStep (residual T A P) F) (D : ℕ), Dstar ≤ D →
          FractionalPerfect ((residual T A P) \ Z.covered) F D →
          ∃ M : ActualRemainderMatching T A P M₀ F,
            ((residual T A M.covered).card : ℝ) ≤
              ε * (((residual T A P) \ Z.covered).card : ℝ) ∧
            ∀ p : Fin 3, ((slice (residual T A M.covered) p).card : ℝ) ≤
              ε * ((slice ((residual T A P) \ Z.covered) 0).card : ℝ) := by
  classical
  obtain ⟨Dstar, hstar, hmatching⟩ :=
    actual_matching_from_fractional_pippenger hPippenger ε hε
  refine ⟨max 3 Dstar, le_max_left _ _, ?_⟩
  intro H _ T A P M₀ F hT hsum hA hAsum hAT hP hallowed Z D hD hfrac
  have hD' : Dstar ≤ D := (le_max_right 3 Dstar).trans hD
  have hPT : P ⊆ T := fun _ hv => (Finset.mem_sdiff.mp (hP hv)).1
  have hAP : Disjoint A P := Finset.disjoint_left.mpr (by
    intro v hvA hvP
    exact (Finset.mem_sdiff.mp (hP hvP)).2 hvA)
  have hPZ : Disjoint P Z.covered := Finset.disjoint_left.mpr (by
    intro v hvP hvZ
    exact (Finset.mem_sdiff.mp (Z.inside hvZ)).2 (Finset.mem_union_right _ hvP))
  let MPZ := unionMatching M₀ Z.matching hPZ
  have hPZT : P ∪ Z.covered ⊆ T := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hPT hv
    · exact (Finset.mem_sdiff.mp (Z.inside hv)).1
  have hAPZ : Disjoint A (P ∪ Z.covered) := Finset.disjoint_left.mpr (by
    intro v hvA hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.disjoint_left.mp hAP hvA hv
    · exact (Finset.mem_sdiff.mp (Z.inside hv)).2 (Finset.mem_union_left _ hvA))
  have hW : residual T A (P ∪ Z.covered) = (residual T A P) \ Z.covered := by
    ext v
    simp only [EndpointMatching.AbsorptionAssembly.residual, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hWb : Balanced ((residual T A P) \ Z.covered) := by
    rw [← hW]
    exact residual_balanced hT hA MPZ hAT hPZT hAPZ
  obtain ⟨Q, MQ, hQ, hQallowed, hrest⟩ := hmatching H _ F D hD' hfrac
  have hQW : Q ⊆ residual T A (P ∪ Z.covered) := by simpa only [hW] using hQ
  have hPQ : Disjoint (P ∪ Z.covered) Q := Finset.disjoint_left.mpr (by
    intro v hvP hvQ
    exact (Finset.mem_sdiff.mp (hQW hvQ)).2 (Finset.mem_union_right _ hvP))
  let MM := unionMatching MPZ MQ hPQ
  have hfinal : (P ∪ Z.covered) ∪ Q ⊆ T \ A := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · refine Finset.mem_sdiff.mpr ⟨hPZT hv, ?_⟩
      intro hvA
      exact Finset.disjoint_left.mp hAPZ hvA hv
    · refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (hQW hv)).1, ?_⟩
      intro hvA
      exact (Finset.mem_sdiff.mp (hQW hv)).2 (Finset.mem_union_left _ hvA)
  have hfinalT : (P ∪ Z.covered) ∪ Q ⊆ T := fun _ hv => (Finset.mem_sdiff.mp (hfinal hv)).1
  have hAfinal : Disjoint A ((P ∪ Z.covered) ∪ Q) := Finset.disjoint_left.mpr (by
    intro v hvA hv
    exact (Finset.mem_sdiff.mp (hfinal hv)).2 hvA)
  have hS : residual T A ((P ∪ Z.covered) ∪ Q) =
      ((residual T A P) \ Z.covered) \ Q := by
    ext v
    simp only [EndpointMatching.AbsorptionAssembly.residual, Finset.mem_sdiff, Finset.mem_union]
    tauto
  let result : ActualRemainderMatching T A P M₀ F := {
    covered := (P ∪ Z.covered) ∪ Q
    matching := MM
    inside := hfinal
    contains := by
      intro E hE
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hE)
    allowed := by
      intro E hE
      rcases Finset.mem_union.mp hE with hE | hE
      · rcases Finset.mem_union.mp hE with hE | hE
        · exact hallowed E hE
        · exact Z.allowed E hE
      · exact hQallowed E hE
    nonzero := by
      intro v hv
      rw [hS] at hv
      exact Z.nonzero v (Finset.mem_sdiff.mp hv).1
    balanced := residual_balanced hT hA MM hAT hfinalT hAfinal
    checksum := residual_sum_eq_zero hsum hAsum MM hAT hfinalT hAfinal
    disjoint := (residual_disjoint_reserved T A _).symm.mono
      Finset.subset_union_left (Finset.Subset.refl _) }
  have hsize : ((residual T A result.covered).card : ℝ) ≤
      ε * (((residual T A P) \ Z.covered).card : ℝ) := by
    simpa only [result, hS] using hrest
  refine ⟨result, hsize, ?_⟩
  intro p
  have hS3 := balanced_card result.balanced
  have hW3 := balanced_card hWb
  have hp := result.balanced p
  rw [hS3, hW3] at hsize
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsize
  rw [hp]
  nlinarith

/-- Once the qualitative actual remainder fits an already selected absorbing
    core, the whole actual target has an exact matching. -/
theorem exact_from_core_and_fractional_after_zero_pippenger
    (hPippenger : PippengerTheorem.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧
      ∀ (H : Type u) [AddCommGroup H]
        (T A P : Finset (Vertex H)) (M₀ : Matching P)
        (F : Finset (Finset (Vertex H))),
        Balanced T → (∑ v ∈ T, v.2 = 0) → Balanced A →
        (∑ v ∈ A, v.2 = 0) → A ⊆ T → P ⊆ T \ A →
        (∀ edge ∈ M₀.edges, edge ∉ F) →
        ∀ (Z : ZeroStep (residual T A P) F) (D : ℕ), Dstar ≤ D →
          FractionalPerfect ((residual T A P) \ Z.covered) F D →
          ∀ capacity : ℕ, AbsorbsUpTo A capacity →
            ε * (((residual T A P) \ Z.covered).card : ℝ) ≤ capacity →
            Nonempty (Matching T) := by
  classical
  obtain ⟨Dstar, hstar, hrem⟩ :=
    actual_remainder_after_zero_step_pippenger hPippenger ε hε
  refine ⟨Dstar, hstar, ?_⟩
  intro H _ T A P M₀ F hT hsum hA hAsum hAT hP hallowed Z D hD hfrac capacity habs hfits
  obtain ⟨M, hsize, _⟩ := hrem H T A P M₀ F hT hsum hA hAsum hAT hP hallowed Z D hD hfrac
  have hbound : (residual T A M.covered).card ≤ capacity := by
    exact_mod_cast hsize.trans hfits
  exact exact_of_absorber_and_nearMatching hT hsum hAT habs
    (M.toCompatibleNearMatching capacity hbound)

/-- Physical signed targets, the actual zero step and the established
    fractional-supplier interface, with a qualitative Pippenger remainder. -/
theorem physical_actual_remainder_from_fractional_pippenger
    (hPippenger : PippengerTheorem.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧
      ∀ (H : Type u) [AddCommGroup H] (q : ℝ) (n : ℕ) (radius : ℝ)
        (R : Finset (Vertex H)) (X Y C : Finset H)
        (A P : Finset (Vertex H)) (M₀ : Matching P) (F : Finset (Finset (Vertex H))),
        0 < q → Disjoint X Y → (0 : H) ∉ C →
        X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        Balanced A → (∑ v ∈ A, v.2 = 0) → A ⊆ signedTarget X Y C →
        P ⊆ signedTarget X Y C \ A → (∀ edge ∈ M₀.edges, edge ∉ F) →
        (∀ z ∈ residual (signedTarget X Y C) A P, z.2 = 0 →
          ∃ edge : Finset (Vertex H), Hyperedge edge ∧
            edge ⊆ residual (signedTarget X Y C) A P ∧ z ∈ edge ∧ edge ∉ F) →
        (taggedDistance R (signedTarget X Y C) : ℝ) + (A.card : ℝ) +
          3 * (M₀.edges.card : ℝ) + (zeroCharge (residual (signedTarget X Y C) A P) : ℝ)
            ≤ radius →
        QuantitativeFractionalSupply R F q n radius Dstar →
        ∃ M : ActualRemainderMatching (signedTarget X Y C) A P M₀ F,
          (∀ p : Fin 3, ((slice (residual (signedTarget X Y C) A M.covered) p).card : ℝ)
            ≤ ε * (2*q*n)) ∧
          ((residual (signedTarget X Y C) A M.covered).card : ℝ) ≤ ε * (6*q*n) := by
  classical
  obtain ⟨Dstar, hstar, hadapter⟩ :=
    actual_remainder_after_zero_step_pippenger hPippenger ε hε
  refine ⟨Dstar, hstar, ?_⟩
  intro H _ q n radius R X Y C A P M₀ F hq hXY hC hsizeXY hsizeXC hsum
    hA hAsum hAT hP hallowed hzero hbudget hfrac
  let T := signedTarget X Y C
  have hT : Balanced T := signedTarget_balanced hsizeXY hsizeXC
  have hTsum : ∑ v ∈ T, v.2 = 0 := signedTarget_zeroSum hsum
  have hPT : P ⊆ T := fun _ hv => (Finset.mem_sdiff.mp (hP hv)).1
  have hAP : Disjoint A P := Finset.disjoint_left.mpr (by
    intro v hvA hvP
    exact (Finset.mem_sdiff.mp (hP hvP)).2 hvA)
  obtain ⟨Z⟩ := zeroStep_exists hXY hC (show residual T A P ⊆ signedTarget X Y C from
    fun _ hv => (Finset.mem_sdiff.mp hv).1) hzero
  have hWb : Balanced ((residual T A P) \ Z.covered) :=
    balanced_sdiff_matching (residual_balanced hT hA M₀ hAT hPT hAP) Z.matching Z.inside
  have hpaid : (taggedDistance R ((residual T A P) \ Z.covered) : ℝ) ≤ radius := by
    calc
      _ ≤ (taggedDistance R T : ℝ) + (A.card : ℝ) + 3 * (M₀.edges.card : ℝ) +
          (zeroCharge (residual T A P) : ℝ) := by
        exact_mod_cast preprocessed_distance_le (R := R) M₀ Z
      _ ≤ radius := hbudget
  obtain ⟨D, hD, hperfect, hm, hdegree, hDn⟩ := hfrac _ hWb Z.nonzero hpaid
  obtain ⟨M, htotal, hrole⟩ := hadapter H T A P M₀ F hT hTsum hA hAsum hAT hP
    hallowed Z D hD hperfect
  have hrole' : ∀ p : Fin 3, ((slice (residual T A M.covered) p).card : ℝ) ≤ ε*(2*q*n) :=
    fun p => (hrole p).trans (mul_le_mul_of_nonneg_left hm hε.le)
  refine ⟨M, hrole', ?_⟩
  have hcard := balanced_card M.balanced
  have hzero' := hrole' 0
  rw [hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-- The original raw event supplies the zero-edge condition and size collar;
    the remaining explicit input supplies actual fractional weights. -/
theorem physical_remainder_on_raw_event_pippenger
    (hPippenger : PippengerTheorem.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧
      ∀ (H : Type u) [Fintype H] [AddCommGroup H]
        (q : ℝ) (s : OriginalSample H) (X Y C : Finset H)
        (A P : Finset (Vertex H)) (M₀ : Matching P) (F : Finset (Finset (Vertex H))),
        0 < q → q ≤ 1/2 → fractionalRawEvent q s →
        Disjoint X Y → (0 : H) ∉ C → X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        Balanced A → (∑ v ∈ A, v.2 = 0) → A ⊆ signedTarget X Y C →
        P ⊆ signedTarget X Y C \ A → (∀ edge ∈ M₀.edges, edge ∉ F) →
        (∀ z, ((banAt F z).card : ℝ) ≤ beta q * (Fintype.card H : ℝ)) →
        (taggedDistance (signedRawTarget s) (signedTarget X Y C) : ℝ) + (A.card : ℝ) +
          3 * (M₀.edges.card : ℝ) + (zeroCharge (residual (signedTarget X Y C) A P) : ℝ)
            ≤ EndpointFractionalRawEvent.rho q * (Fintype.card H : ℝ) →
        6 * (Dstar : ℝ) ≤ q^2 * (Fintype.card H : ℝ) →
        ActualFractionalWeights (signedRawTarget s) F q
          (EndpointFractionalRawEvent.rho q * (Fintype.card H : ℝ)) →
        ∃ M : ActualRemainderMatching (signedTarget X Y C) A P M₀ F,
          (∀ p : Fin 3, ((slice (residual (signedTarget X Y C) A M.covered) p).card : ℝ)
            ≤ ε*(2*q*(Fintype.card H : ℝ))) ∧
          ((residual (signedTarget X Y C) A M.covered).card : ℝ) ≤
            ε*(6*q*(Fintype.card H : ℝ)) := by
  classical
  obtain ⟨Dstar, hstar, hphysical⟩ :=
    physical_actual_remainder_from_fractional_pippenger hPippenger ε hε
  refine ⟨Dstar, hstar, ?_⟩
  intro H _ _ q s X Y C A P M₀ F hq hqhalf hraw hXY hC hsizeXY hsizeXC hsum
    hA hAsum hAT hP hallowed hban hbudget hlarge hweights
  have hinterval := intervalFractionalSupply_of_raw_event hq hqhalf hraw hweights
  have hquant := quantitativeFractionalSupply_of_interval q (Fintype.card H)
    (EndpointFractionalRawEvent.rho q * (Fintype.card H : ℝ)) Dstar
    hq hqhalf hstar hlarge hinterval
  have hzero := zero_edge_of_fractionalRawEvent hq hraw M₀ F hC hban hbudget
  exact hphysical H q (Fintype.card H)
    (EndpointFractionalRawEvent.rho q * (Fintype.card H : ℝ)) (signedRawTarget s)
    X Y C A P M₀ F hq hXY hC hsizeXY hsizeXC hsum hA hAsum hAT hP hallowed
    hzero hbudget hquant

/-- The existing raw-event spectral proof supplies the actual fractional
    weights for every later admissible target and bounded rooted-edge ban. -/
theorem physical_remainder_on_raw_event_without_weight_input
    (hPippenger : PippengerTheorem.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Dstar : ℕ, 3 ≤ Dstar ∧
      ∀ (H : Type u) [Fintype H] [AddCommGroup H]
        (q : ℝ) (s : OriginalSample H) (X Y C : Finset H)
        (A P : Finset (Vertex H)) (M₀ : Matching P) (F : Finset (Finset (Vertex H))),
        0 < q → q ≤ 1/2 → fractionalRawEvent q s →
        Disjoint X Y → (0 : H) ∉ C → X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        Balanced A → (∑ v ∈ A, v.2 = 0) → A ⊆ signedTarget X Y C →
        P ⊆ signedTarget X Y C \ A → (∀ edge ∈ M₀.edges, edge ∉ F) →
        (∀ z, ((banAt F z).card : ℝ) ≤ beta q * (Fintype.card H : ℝ)) →
        (taggedDistance (signedRawTarget s) (signedTarget X Y C) : ℝ) + (A.card : ℝ) +
          3 * (M₀.edges.card : ℝ) + (zeroCharge (residual (signedTarget X Y C) A P) : ℝ)
            ≤ EndpointFractionalRawEvent.rho q * (Fintype.card H : ℝ) →
        6 * (Dstar : ℝ) ≤ q^2 * (Fintype.card H : ℝ) →
        ∃ M : ActualRemainderMatching (signedTarget X Y C) A P M₀ F,
          (∀ p : Fin 3, ((slice (residual (signedTarget X Y C) A M.covered) p).card : ℝ)
            ≤ ε*(2*q*(Fintype.card H : ℝ))) ∧
          ((residual (signedTarget X Y C) A M.covered).card : ℝ) ≤
            ε*(6*q*(Fintype.card H : ℝ)) := by
  classical
  obtain ⟨Dstar, hstar, hrem⟩ := physical_remainder_on_raw_event_pippenger hPippenger ε hε
  refine ⟨Dstar, hstar, ?_⟩
  intro H _ _ q s X Y C A P M₀ F hq hqhalf hraw hXY hC hsizeXY hsizeXC hsum
    hA hAsum hAT hP hallowed hban hbudget hlarge
  have hsmall := actualRawSmallSquare_of_l2 hq hqhalf hraw
    (fractionalRawEvent_actualRawMatrix_L2_le hraw)
  have hweights := actualFractionalWeights_of_raw_and_smallSquare
    q hq hqhalf s hraw hsmall F hban
  exact hrem H q s X Y C A P M₀ F hq hqhalf hraw hXY hC hsizeXY hsizeXC hsum
    hA hAsum hAT hP hallowed hban hbudget hlarge hweights

/-- On the same universal-core and fractional raw events, Pippenger alone
    supplies the complete physical exact matching for every later target. -/
theorem physical_exact_on_shared_events_pippenger
    (hPippenger : PippengerTheorem.{u}) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      N ≤ Fintype.card G →
      ∀ ω : FullSample G,
        UniversalCoreEvent (tau q) ω →
        fractionalRawEvent q (originalProcess ω) →
      ∀ X Y C : Finset G,
        Disjoint X Y → (0 : G) ∉ C → X.card = Y.card → X.card = C.card →
        (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x →
        (physicalEditDistance (originalTailSet (originalProcess ω))
          (originalHeadSet (originalProcess ω)) (originalColourSet (originalProcess ω)) X Y C : ℝ) ≤
          (1 / 10^6 : ℝ) * kappa q * (Fintype.card G : ℝ) →
        Nonempty (PhysicalDifferenceMatching X Y C) := by
  classical
  have hκpos : 0 < kappa q := by
    unfold kappa tau p CorralFormalization.EndpointProof.RateBudget.SamplingConstants.rho eta
    positivity
  let ε : ℝ := kappa q / 12
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Dstar, hDstar, hrem⟩ :=
    physical_remainder_on_raw_event_without_weight_input hPippenger ε hε
  obtain ⟨N,hN⟩ := exact_receiver_thresholds q 0 Dstar hq0 (by norm_num)
  refine ⟨N, ?_⟩
  intro G _ _ hn ω hcore hraw X Y C hdisjoint hzero hXY hXC hchecksum hdistance
  obtain ⟨hκ,hbudget,hdegree,_⟩ := hN (Fintype.card G) hn
  apply physical_exact_from_universalCore q hq0 hq1 ω hcore X Y C hdistance hκ hXY hXC hchecksum
  intro A hAin hAnonzero hAbal hAsum hAsize
  have hAr : (A.card : ℝ) ≤ 16200 * tau q * (Fintype.card G : ℝ) := by
    have hcast : (A.card : ℝ) ≤ (⌊16200 * tau q * (Fintype.card G : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast hAsize
    have hnonneg : 0 ≤ 16200 * tau q * (Fintype.card G : ℝ) := by
      unfold tau p CorralFormalization.EndpointProof.RateBudget.SamplingConstants.rho eta
      positivity
    exact hcast.trans (Nat.floor_le hnonneg)
  have hbr := core_and_edit_budget_for_fractional_supplier q hq0 hq1 (Fintype.card G)
    (physicalEditDistance (originalTailSet (originalProcess ω))
      (originalHeadSet (originalProcess ω)) (originalColourSet (originalProcess ω)) X Y C)
    A.card hdistance hAr hbudget
  have hban : ∀ z : Vertex G, ((banAt (∅ : Finset (Finset (Vertex G))) z).card : ℝ) ≤
      beta q * (Fintype.card G : ℝ) := by
    intro z
    simp [banAt, beta]
    positivity
  have hbudget' :
      (taggedDistance (signedRawTarget (originalProcess ω)) (signedTarget X Y C) : ℝ) +
      (A.card : ℝ) + 3 * ((emptyMatching (G := G)).edges.card : ℝ) +
      (zeroCharge (residual (signedTarget X Y C) A ∅) : ℝ) ≤
        EndpointFractionalRawEvent.rho q * (Fintype.card G : ℝ) := by
    rw [raw_taggedDistance_eq_physical]
    simp only [emptyMatching, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
    have hz : (zeroCharge (residual (signedTarget X Y C) A ∅) : ℝ) ≤ 3 := by
      exact_mod_cast zeroCharge_le_three (residual (signedTarget X Y C) A ∅)
    unfold EndpointFractionalRawEvent.rho
    linarith
  obtain ⟨M, _, htotal⟩ := hrem G q (originalProcess ω) X Y C A ∅
    (emptyMatching (G := G)) ∅ hq0 hq1 hraw hdisjoint hzero hXY hXC hchecksum
    hAbal hAsum hAin (by simp) (by simp [emptyMatching]) hban hbudget' hdegree
  have hsmall : ε * (6*q*(Fintype.card G : ℝ)) ≤
      kappa q * (Fintype.card G : ℝ) := by
    have hn : (0 : ℝ) ≤ Fintype.card G := by positivity
    have hq6 : 6*q ≤ 3 := by linarith
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq6 hε.le) hn
    have hkn : 0 ≤ kappa q * (Fintype.card G : ℝ) := mul_nonneg hκpos.le hn
    dsimp [ε] at hh ⊢
    nlinarith
  have hres : (residual (signedTarget X Y C) A M.covered).card ≤
      ⌊kappa q * (Fintype.card G : ℝ)⌋₊ := by
    apply Nat.le_floor
    exact htotal.trans hsmall
  exact ⟨M.toCompatibleNearMatching _ hres⟩

/-- The full original-law exact-matching event, with its existing exponential failure
    rate and all later-target quantifiers, from Pippenger alone. -/
theorem original_exact_matching_probability_pippenger
    (hPippenger : PippengerTheorem.{u})
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ PhysicalExactEvent q s} ≤
        Real.exp (-((xi q)^4/10^6) * (Fintype.card G : ℝ)) := by
  classical
  obtain ⟨Nexact,hNexact⟩ := physical_exact_on_shared_events_pippenger hPippenger q hq0 hq1
  obtain ⟨Nj,hNj⟩ := originalCore_and_fractionalRawEvent_final_rate q hq0 hq1
  refine ⟨max Nexact Nj, ?_⟩
  intro G _ _ hodd hn
  have hnexact : Nexact ≤ Fintype.card G := by omega
  have hnj : Nj ≤ Fintype.card G := by omega
  have hsub : {s : OriginalSample G | ¬ PhysicalExactEvent q s} ⊆
      {s | ¬ OriginalCoreAndEvent q (fractionalRawEvent q) s} := by
    intro s hbad hgood
    obtain ⟨ω,hω,hcore,hraw⟩ := hgood
    have hraw' : fractionalRawEvent q (originalProcess ω) := by simpa [hω] using hraw
    apply hbad
    intro X Y C hdisjoint hzero hXY hXC hsum hd
    have hd' : (physicalEditDistance (originalTailSet (originalProcess ω))
        (originalHeadSet (originalProcess ω)) (originalColourSet (originalProcess ω)) X Y C : ℝ) ≤
        (1 / 10^6 : ℝ) * kappa q * (Fintype.card G : ℝ) := by simpa only [hω] using hd
    exact hNexact G hnexact ω hcore hraw' X Y C hdisjoint hzero hXY hXC hsum hd'
  have hprob := measureReal_mono hsub
    (measure_ne_top (originalMeasure (G := G) q (le_of_lt hq0) hq1) _)
  exact hprob.trans (hNj G hodd hnj)

/-- The same conclusion at any paper rate `lam⁴/10⁶` with `0 ≤ lam ≤ xi`. -/
theorem original_exact_matching_probability_pippenger_at_smaller_rate
    (hPippenger : PippengerTheorem.{u})
    (q lam : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (hLam0 : 0 ≤ lam) (hLam : lam ≤ xi q) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (originalMeasure (G := G) q (le_of_lt hq0) hq1).real
        {s | ¬ PhysicalExactEvent q s} ≤
        Real.exp (-(lam^4/10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N,hN⟩ := original_exact_matching_probability_pippenger hPippenger q hq0 hq1
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  apply (hN G hodd hn).trans
  apply Real.exp_le_exp.mpr
  have hpow : lam^4 ≤ (xi q)^4 := pow_le_pow_left₀ hLam0 hLam 4
  have hn0 : 0 ≤ (Fintype.card G : ℝ) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hn0]

/-- Transport uniform exact-matching theorem's Pippenger-only bound to the actual layered sample. -/
theorem layered_exact_event_failure_probability_pippenger
    (hPippenger : PippengerTheorem.{u})
    {m : ℕ} (d : Densities m) (hq0 : 0 < d.q) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (sampleMeasure (G := G) d).real {s | ¬ ExactMatchingEvent d s} ≤
        Real.exp (-((xi d.q)^4 / 10^6) * (Fintype.card G : ℝ)) := by
  obtain ⟨N, hN⟩ := original_exact_matching_probability_pippenger hPippenger d.q hq0 d.q_le_half
  refine ⟨N, ?_⟩
  intro G _ _ hodd hn
  have hp := project_measurePreserving (G := G) d
  have heq := hp.measureReal_preimage
    (s := {s : OriginalSample G | ¬ PhysicalExactEvent d.q s}) (by measurability)
  change (sampleMeasure d).real
    (project ⁻¹' {s : OriginalSample G | ¬ PhysicalExactEvent d.q s}) ≤ _
  rw [heq]
  exact hN G hodd hn

/-- One layered sample simultaneously supplies exact-matching, the pair banks and all
    size bounds, with the original joint failure bound and only Pippenger. -/
theorem layered_good_sample_failure_probability_pippenger
    (hPippenger : PippengerTheorem.{u})
    {m : ℕ} (d : Densities m) (hq0 : 0 < d.q) :
    ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      ∀ t : ℝ, 0 ≤ t →
      (sampleMeasure (G := G) d).real {s | ¬ GoodSample d t s} ≤
        failureBound d t (Fintype.card G) := by
  obtain ⟨N, hN⟩ := layered_exact_event_failure_probability_pippenger hPippenger d hq0
  refine ⟨max N 4, ?_⟩
  intro G _ _ hodd hn t ht
  let μ := sampleMeasure (G := G) d
  have hE := hN G hodd (by omega)
  have hP := pairSupplyEvent_failure_probability (G := G) d (by omega)
  have hS := sizeEvent_failure_probability (G := G) d t ht
  have heq : {s : Sample G m | ¬ GoodSample d t s} =
      ({s | ¬ ExactMatchingEvent d s} ∪ {s | ¬ PairSupplyEvent d s}) ∪
        {s | ¬ SizeEvent d t s} := by
    ext s; simp only [GoodSample, not_and_or, Set.mem_union, Set.mem_ofPred_eq]; tauto
  rw [heq]
  calc
    μ.real (({s | ¬ ExactMatchingEvent d s} ∪ {s | ¬ PairSupplyEvent d s}) ∪
        {s | ¬ SizeEvent d t s}) ≤
      μ.real ({s | ¬ ExactMatchingEvent d s} ∪ {s | ¬ PairSupplyEvent d s}) +
        μ.real {s | ¬ SizeEvent d t s} := measureReal_union_le _ _
    _ ≤ (μ.real {s | ¬ ExactMatchingEvent d s} + μ.real {s | ¬ PairSupplyEvent d s}) +
        μ.real {s | ¬ SizeEvent d t s} := add_le_add (measureReal_union_le _ _) (le_refl _)
    _ ≤ failureBound d t (Fintype.card G) := add_le_add (add_le_add hE hP) hS

/-- The same augmented sample supplies exact-matching, all later ordinary transitions,
    and any router event with the stated uniform vanishing failure bound. -/
theorem exists_goodAugmented_and_layeredTransitions_pippenger
    (hPippenger : PippengerTheorem.{u}) {m : ℕ} (d : Densities m) (t coin : ℝ)
    (hq : 0 < d.q) (hqthird : d.q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10)
    (hcoin0 : 0 ≤ coin) (hcoin1 : coin ≤ 1)
    (router : ∀ (G : Type u) [Fintype G] [AddCommGroup G], AugmentedSample G m → Prop)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hrouter : ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (augmentedMeasure (G := G) d coin hcoin0 hcoin1).real
        {s | ¬ router G s} ≤ error (Fintype.card G)) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∀ η : ℝ,
      0 < η → η ≤ d.q/1000 → η ≤ t/100 → η ≤ d.q^2*μ/1000 →
      ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
        Odd (Fintype.card G) → N ≤ Fintype.card G →
        ∃ s : AugmentedSample G m,
          GoodSample d (explicitSizeTolerance (Fintype.card G)) (forgetAugmented s) ∧
          LayerTransitionEvent d t η (forgetAugmented s) ∧ router G s := by
  obtain ⟨μ, hμ, hμhalf, htransition⟩ :=
    layeredTransitions_of_transitionFourier hPippenger d t hq hqthird ht httenth
  obtain ⟨Nr, hr⟩ := hrouter
  obtain ⟨Ng, hg⟩ := layered_good_sample_failure_probability_pippenger hPippenger d hq
  refine ⟨μ, hμ, hμhalf, ?_⟩
  intro η hη hηq hηt hημ
  obtain ⟨Nt, ht'⟩ := htransition η hη hηq hηt hημ
  have hsum : Tendsto (fun n : ℕ =>
      (explicitFailureBound d n + fourierFailureBound m (η^2) n) + error n) atTop (𝓝 0) := by
    simpa only [add_zero] using
      ((explicitFailureBound_tendsto_zero d hq).add
        (fourierFailureBound_tendsto_zero m (η^2) (sq_pos_of_pos hη))).add herror
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (explicitFailureBound d n + fourierFailureBound m (η^2) n) + error n < 1 :=
    (tendsto_order.1 hsum).2 1 (by norm_num)
  obtain ⟨Ns, hs⟩ := eventually_atTop.1 hsmall
  refine ⟨max Nt (max Ng (max Nr (max Ns 1))), ?_⟩
  intro G _ _ hodd hn
  let n := Fintype.card G
  have hnpos : 0 < n := by dsimp [n]; omega
  have hgood0 := hg G hodd (by omega) (explicitSizeTolerance n) (explicitSizeTolerance_nonneg n)
  rw [failureBound_explicitSizeTolerance d n hnpos] at hgood0
  have hgood := goodSample_and_fourier_explicitBound d (η^2) (sq_nonneg η) hgood0
  have hrouter' := hr G hodd (by omega)
  obtain ⟨s, hs0, hsF, hsR⟩ := exists_goodFourierAugmented_and_event_of_error_lt_one
    d coin hcoin0 hcoin1 (explicitSizeTolerance n) (η^2)
    (explicitFailureBound d n + fourierFailureBound m (η^2) n) (error n)
    hgood (router G) hrouter' (hs n (by dsimp [n]; omega))
  refine ⟨s, hs0, ?_, hsR⟩
  exact ht' G (by omega) (forgetAugmented s) (transitionFourierEvent_of_fourierEvent hsF)

/-- The actual router reservoir, its primitives, and all ordinary transitions
    are available on one sample with only the Pippenger theorem input. -/
theorem exists_goodAugmented_layeredTransitions_and_routerReservoir_pippenger
    (hPippenger : PippengerTheorem.{u})
    {m : ℕ} (d : Densities m) (t u₀ : ℝ)
    (hq : 0 < d.q) (hqthird : d.q ≤ 1/3) (ht : 0 < t) (httenth : t ≤ 1/10)
    (hr : 0 < d.r) (hu : 0 < u₀) (hur : u₀ ≤ d.r) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∀ η : ℝ,
      0 < η → η ≤ d.q/1000 → η ≤ t/100 → η ≤ d.q^2*μ/1000 →
      ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
        Odd (Fintype.card G) → N ≤ Fintype.card G →
        ∃ s : AugmentedSample G m,
          GoodSample d (explicitSizeTolerance (Fintype.card G)) (forgetAugmented s) ∧
          LayerTransitionEvent d t η (forgetAugmented s) ∧
          AugmentedRouterReservoirEvent u₀ s := by
  let event : ∀ (G : Type u) [Fintype G] [AddCommGroup G], AugmentedSample G m → Prop :=
    fun G _ _ => AugmentedRouterReservoirEvent u₀
  have hrouter : ∃ N : ℕ, ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → N ≤ Fintype.card G →
      (augmentedMeasure (G := G) d (u₀ / d.r) (div_nonneg hu.le hr.le)
        ((div_le_one hr).mpr hur)).real {s | ¬ event G s} ≤
          reservoirFailureBound u₀ (Fintype.card G) := by
    refine ⟨4000, ?_⟩
    intro G _ _ hodd hn
    exact augmentedRouterReservoirEvent_failure_probability d hr u₀ hu.le hur hodd hn
  exact exists_goodAugmented_and_layeredTransitions_pippenger hPippenger d t (u₀ / d.r)
    hq hqthird ht httenth (div_nonneg hu.le hr.le) ((div_le_one hr).mpr hur)
    event (reservoirFailureBound u₀) (reservoirFailureBound_tendsto_zero u₀ hu) hrouter

end
end EndpointPippenger
