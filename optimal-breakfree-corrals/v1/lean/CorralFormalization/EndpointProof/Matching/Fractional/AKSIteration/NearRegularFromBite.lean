import CorralFormalization.EndpointProof.Matching.Fractional.AKSIteration.TerminatingIteration
/-!
# The project's near-regular AKS input from an explicit source bite

This proves the deterministic iteration from `SourceBiteTheorem` to the
maintained finite-set near-regular matching statement. The source-shaped
bite theorem is still an explicit mathematical argument; the probabilistic
proof of that theorem is not part of this file.
-/

open scoped Classical BigOperators
open EndpointMatching.Fractional.Rounding AKSSourceBite

namespace AKSSourceIteration
noncomputable section
universe u

/-- From a source-shaped one-bite theorem with fixed constants, derive the
actual finite-set near-regular AKS matching theorem with fixed constants.
The empty vertex type is handled separately. -/
theorem AKSSetFamily_from_source_bite (K Dmin C Cw : ℝ)
    (hC : 0 ≤ C) (hCw : 0 ≤ Cw)
    (hsource : SourceBiteTheorem.{u} K Dmin C Cw) :
    ∃ D0 Cstar : ℝ, 0 < Cstar ∧ AKSSetFamilyTheorem.{u} K D0 Cstar := by
  obtain ⟨L,hLone,hLmin,hLexp,hbudget,hcontract⟩ := exists_common_threshold C Dmin hC
  let E : Environment.{u} :=
    { K := K
      Dmin := Dmin
      C := C
      Cw := Cw
      L := L
      C_nonneg := hC
      Cw_nonneg := hCw
      L_one := hLone
      L_min := hLmin
      L_exp := hLexp
      budget := hbudget
      contract := hcontract
      source := hsource }
  let Cstar : ℝ := 2*(Cw*(1+1/(-Real.log theta))+Real.sqrt L)
  have htheta := theta_bounds
  have hden : 0 < -Real.log theta := neg_pos.mpr (Real.log_neg htheta.1 htheta.2)
  have hinv : 0 ≤ 1/(-Real.log theta) := div_nonneg (by norm_num) hden.le
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) hLone)
  have hCstar : 0 < Cstar := by
    have hprod : 0 ≤ Cw*(1+1/(-Real.log theta)) := mul_nonneg hCw (by linarith)
    dsimp [Cstar]
    linarith
  refine ⟨L,Cstar,hCstar,?_⟩
  intro V _ H huniform hlinear D hD hDexp hdegree
  by_cases hne : (Finset.univ : Finset V).Nonempty
  · have hwindow : Window (Finset.univ : Finset V) H D K :=
      window_univ_of_project_hypotheses H D K huniform hlinear hdegree
    have hDnonneg : 0 ≤ D := (Real.exp_pos 1).le.trans hDexp
    let s : State E (V := V) :=
      { vertices := Finset.univ
        edges := H
        degree := D
        degree_nonneg := hDnonneg
        edges_valid := hwindow.1
        linear := hlinear
        window := by intro _; exact hwindow
        empty_degree := by
          intro hempty
          exact False.elim (hne.ne_empty hempty) }
    have hmatch := matching_of_run E s rfl (by simpa [s] using hDexp)
    simpa [s,E,Cstar] using hmatch
  · have hempty : (Finset.univ : Finset V) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hcard : Fintype.card V = 0 := by
      have h := congrArg Finset.card hempty
      simpa using h
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · simp [IsMatching]
    · simp [uncovered,hempty,hcard]

/-- Existence of source constants supplies exactly the explicit external
near-regular premise used by the maintained quantitative remainder chain. -/
theorem absolute_AKS_input_from_source_bite
    (hsource : ∃ K Dmin C Cw : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 ≤ Cw ∧
      SourceBiteTheorem.{u} K Dmin C Cw) :
    ∃ K D0 Cstar : ℝ, 0 < K ∧ 0 < Cstar ∧ AKSSetFamilyTheorem.{u} K D0 Cstar := by
  obtain ⟨K,Dmin,C,Cw,hK,hC,hCw,hbite⟩ := hsource
  obtain ⟨D0,Cstar,hCstar,hAKS⟩ := AKSSetFamily_from_source_bite K Dmin C Cw hC hCw hbite
  exact ⟨K,D0,Cstar,hK,hCstar,hAKS⟩

end
end AKSSourceIteration
