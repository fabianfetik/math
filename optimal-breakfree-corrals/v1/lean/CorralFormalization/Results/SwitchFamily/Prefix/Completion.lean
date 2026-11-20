import CorralFormalization.Results.SwitchFamily.Prefix.Arithmetic
import CorralFormalization.Results.SwitchFamily.Asymptotic

/-!
# Appendix A.1: completing the actual switch prefix

The endpoint tolerance is retained as a named witness.  The final supplier
has only the cited external matching theorems as mathematical premises.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding

noncomputable section

namespace CorralFormalization.Results.SwitchFamily.Prefix

open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.PathTerraceCompletion

@[simp] theorem count_eq_switchMultiplicity (n : ℕ) :
    count n=switchMultiplicity n := rfl

theorem count_eq_explicit_floor {n : ℕ} (hn : 64 ≤ n) :
    (count n : ℤ)=⌊(((⌊Real.sqrt (n : ℝ)⌋ : ℤ) : ℝ)-8)/5⌋ :=
  switchMultiplicity_eq_explicit_floor hn

@[simp] theorem colors_length (n m : ℕ) : (colors n m).length=5*m+7 := by
  simp [colors,explicitGapPrefix,blockColors,List.length_flatMap]
  omega

/-- Reading the first eight vertices of the completed exact path supplies
the literal input expected by the general 2/3-tile lemma. -/
theorem hasSpecifiedPrefix_of_vertices_prefix {n m : ℕ} (D : DirectedTerrace n)
    (hp : vertices n m <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val)) :
    HasSpecifiedPrefix D := by
  obtain ⟨rest,hrest⟩ := hp
  unfold HasSpecifiedPrefix
  rw [← hrest,vertices_initial,List.append_assoc]
  simp [explicitPrefix]

/-- The continuation is the actual completed calendar suffix, with every A4
block left in place. The remainder is also the actual suffix of D.word. -/
theorem body_calendar_of_colors_prefix {n m : ℕ} (D : DirectedTerrace n)
    (hp : colors n m <+: D.word) :
    D.word.drop 7=(List.range m).flatMap (blockColors n) ++ D.word.drop (5*m+7) := by
  obtain ⟨rest,hrest⟩ := hp
  have hdrop : D.word.drop (5*m+7)=rest := by
    rw [← hrest,← colors_length n m]
    simp
  rw [hdrop,← hrest]
  simp [colors,explicitGapPrefix]

/-- All data needed downstream come from a terrace containing the literal
constructed vertex list and its computed consecutive-gap calendar. -/
def PrescribedTerrace {n : ℕ} (m : ℕ) (D : DirectedTerrace n) : Prop :=
  HasSpecifiedPrefix D ∧
  vertices n m <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
  colors n m <+: D.word ∧
  D.word.drop 7=(List.range m).flatMap (blockColors n) ++ D.word.drop (5*m+7)

/-- Fixed-tolerance completion of A1--A4 at every sufficiently large odd
modulus. No desired prefix or precompleted terrace is an input. -/
theorem eventual_terrace_of_endpointAt {ε0 : ℝ} {n0 : ℕ}
    (hε0 : 0 < ε0) (H : OddCyclicRainbowEndpointCompletionAt ε0 n0) :
    ∃ N : ℕ, 65 ≤ N ∧ ∀ n : ℕ, Odd n → N ≤ n →
      ∃ D : DirectedTerrace n, PrescribedTerrace (count n) D := by
  obtain ⟨N,hN,hbudget⟩ := path_budget_eventually hε0
  refine ⟨max n0 N, hN.trans (le_max_right _ _), ?_⟩
  intro n hodd hn
  have hnN : N ≤ n := (le_max_right n0 N).trans hn
  have hn65 : 65 ≤ n := hN.trans hnN
  have hn64 : 64 ≤ n := by omega
  have hn0 : n0 ≤ n := (le_max_left n0 N).trans hn
  have : NeZero n := ⟨by omega⟩
  have hsize := count_square_bound hn64
  obtain ⟨D,hv,hg⟩ := path_terrace_of_cyclicCompletionAt H hodd hn0
    (vertices n (count n)) (by rw [vertices_length]; omega)
    (vertices_nodup hn65 hsize) (vertices_nonzero hn65 hsize)
    (vertices_rainbow hn65 hsize) (vertices_colors_nonzero hn65 hsize)
    (hbudget n hnN).2
  have hc : colors n (count n) <+: D.word := by
    rwa [vertices_pathGaps hn65 hsize] at hg
  exact ⟨D,hasSpecifiedPrefix_of_vertices_prefix D hv,hv,hc,
    body_calendar_of_colors_prefix D hc⟩

/-- The parameter n=2h-1 is odd for every positive height. All size, floor,
square-root, parity and endpoint-budget obligations have been discharged. -/
theorem eventual_height_terrace_of_endpointAt {ε0 : ℝ} {n0 : ℕ}
    (hε0 : 0 < ε0) (H : OddCyclicRainbowEndpointCompletionAt ε0 n0) :
    ∃ h0 : ℕ, 33 ≤ h0 ∧ ∀ h : ℕ, h0 ≤ h →
      ∃ D : DirectedTerrace (2*h-1), PrescribedTerrace (count (2*h-1)) D := by
  obtain ⟨N,hN,hterrace⟩ := eventual_terrace_of_endpointAt hε0 H
  refine ⟨max 33 N, le_max_left _ _, ?_⟩
  intro h hh
  have hh33 : 33 ≤ h := (le_max_left 33 N).trans hh
  have hNn : N ≤ 2*h-1 := by omega
  have hodd : Odd (2*h-1) := by
    refine ⟨h-1, ?_⟩
    omega
  exact hterrace (2*h-1) hodd hNn

/-- AKS and Pippenger supply the endpoint theorem and hence the actual
Appendix path terrace, with one unchanged positive tolerance. -/
theorem eventual_height_terrace_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∃ h0 : ℕ, 33 ≤ h0 ∧ ∀ h : ℕ, h0 ≤ h →
        ∃ D : DirectedTerrace (2*h-1), PrescribedTerrace (count (2*h-1)) D := by
  obtain ⟨ε0,hε0,n0,H⟩ := oddCyclicEndpointCompletion_iff.mp
    (CorralFormalization.Results.cyclicCompletion_from_matching_inputs hAKS hPippenger)
  exact ⟨ε0,hε0,n0,H,eventual_height_terrace_of_endpointAt hε0 H⟩

/-- The uniform odd-abelian endpoint theorem and Appendix A use exactly the
same tolerance, with only the cyclic endpoint threshold enlarged. -/
theorem uniform_endpoint_and_appendix_terrace_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 Npath ∧
      ∃ h0 : ℕ, 33 ≤ h0 ∧ ∀ h : ℕ, h0 ≤ h →
        ∃ D : DirectedTerrace (2*h-1), PrescribedTerrace (count (2*h-1)) D := by
  obtain ⟨ε0,hε0,Nphysical,hphysical⟩ :=
    EndpointFactor.uniformPhysicalEndpointCompletion_from_AKS_Pippenger hAKS hPippenger
  have hphysical' : UniformPhysicalEndpointCompletionAt ε0 Nphysical := hphysical
  obtain ⟨Npath,H⟩ := cyclicCompletionAt_of_uniformPhysicalAt hε0 hphysical'
  exact ⟨ε0,hε0,Nphysical,hphysical',Npath,H,eventual_height_terrace_of_endpointAt hε0 H⟩

end CorralFormalization.Results.SwitchFamily.Prefix
end
