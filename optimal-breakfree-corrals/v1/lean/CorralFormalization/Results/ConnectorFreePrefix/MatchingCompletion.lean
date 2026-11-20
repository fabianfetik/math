import CorralFormalization.Results.CompletionFromMatching
import CorralFormalization.Results.ConnectorFreePrefix.EndpointCompletion

/-!
# Closing a supplied stronger prefix from the two matching inputs

The paper's physical endpoint theorem now supplies the former cyclic endpoint
premise.  The actual connector-free prefix remains an explicit input here:
this module does not construct its vertices, colours, or physical Latin family.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralFormalization.LatinCompletion.TerraceCompletion
noncomputable section

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

/-- A common endpoint tolerance and threshold close every supplied rainbow
prefix at the stronger floor.  No endpoint-existence premise is assumed.
The written `3*r^2+8` prefix itself is still a separate construction. -/
theorem supplied_prefix_completion_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      ∀ ε : ℝ, ε ≤ min ε0 ((1 : ℝ) / 100) →
        ∀ (n : ℕ) [NeZero n], Odd n → n0 ≤ n → 34 ≤ ε * (n : ℝ) →
          ∀ P : RainbowPrefix n,
            P.path.length = 3 * radius ε n * radius ε n + 8 →
              Nonempty P.ComplementaryPath := by
  have hcompletion := Results.cyclicCompletion_from_matching_inputs hAKS hPippenger
  obtain ⟨ε0, hε0, n0, hendpoint⟩ := oddCyclicEndpointCompletion_iff.mp hcompletion
  refine ⟨ε0, hε0, n0, ?_⟩
  intro ε hε n _ hodd hn0 h34 P hlen
  exact prefix_complementaryPath hendpoint hodd hn0 hε h34 P hlen

/-- The same result returns an actual spliced rotational terrace, preserving
the supplied stronger prefix and its differences. -/
theorem supplied_prefix_terrace_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      ∀ ε : ℝ, ε ≤ min ε0 ((1 : ℝ) / 100) →
        ∀ (n : ℕ) [NeZero n], Odd n → n0 ≤ n → 34 ≤ ε * (n : ℝ) →
          ∀ P : RainbowPrefix n,
            P.path.length = 3 * radius ε n * radius ε n + 8 →
              ∃ S : EndpointSpliceInput n, S.first = P.first ∧ S.prefixPath = P.path ∧
                P.path <+: S.cycleVertices ∧ pathGaps P.path <+: S.directedTerrace.word := by
  have hcompletion := Results.cyclicCompletion_from_matching_inputs hAKS hPippenger
  obtain ⟨ε0, hε0, n0, hendpoint⟩ := oddCyclicEndpointCompletion_iff.mp hcompletion
  refine ⟨ε0, hε0, n0, ?_⟩
  intro ε hε n _ hodd hn0 h34 P hlen
  exact prefix_splicedTerrace hendpoint hodd hn0 hε h34 P hlen

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
end
