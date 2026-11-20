import CorralFormalization.Results.ConnectorFreePrefix.Radius
import CorralFormalization.Results.ConnectorPrefixFloor

/-!
# Closing a supplied prefix at the deletion budget

Section 8.2 uses the `3*r*r + 7` edge budget of the new connector-free prefix.
The lemmas below apply the existing generic residual-set and endpoint machinery
at exactly that budget. A `RainbowPrefix` with the stated length is an explicit
input: its construction, marker values, direct joins, physical tiles and
Latin-family injection are not supplied here. The cyclic endpoint theorem is
also an explicit input, not a proved consequence of the manuscript's Theorem 9.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

/-- Comparison of the two numerical radii only. This does not compare
Latin-square counts of different orders or establish a new physical family. -/
theorem connectorPrefixRadius_le_radius {ε : ℝ} {n : ℕ}
    (hn : 4 ≤ ε * (n : ℝ)) :
    connectorPrefixRadius ε n ≤ radius ε n := by
  apply Nat.floor_mono
  apply Real.sqrt_le_sqrt
  linarith

/-- The cyclic endpoint premise applies at the literal new floor budget,
retaining the supplied value of the endpoint tolerance `ε0`. -/
theorem endpointCompletionAt_radius {ε0 ε : ℝ} {n0 n : ℕ} [NeZero n]
    (H : OddCyclicRainbowEndpointCompletionAt ε0 n0) (hodd : Odd n) (hn0 : n0 ≤ n)
    (hε : ε ≤ min ε0 ((1 : ℝ) / 100)) (hn : 34 ≤ ε * (n : ℝ)) :
    EndpointCompletionAt n (3 * radius ε n * radius ε n + 7) := by
  obtain ⟨hr, hlarge, hbudget⟩ :=
    radius_bounds (hε.trans (min_le_right _ _)) hn
  have ht : 3 * radius ε n * radius ε n + 7 ≤ n := by
    nlinarith
  have heprod : ε * (n : ℝ) ≤ ε0 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (hε.trans (min_le_left _ _)) (Nat.cast_nonneg n)
  exact oddCyclicEndpointCompletionAt_local H hodd hn0 ht (hbudget.trans heprod)

/-- The exact residual sizes printed in Section 8.2 follow from any actual
simple rainbow prefix with the specified vertex count. -/
theorem prefix_residual_counts {n r : ℕ} [NeZero n]
    (P : RainbowPrefix n) (hlen : P.path.length = 3 * r * r + 8) :
    P.remainingVertices.card = n - (3 * r * r + 7) ∧
      P.remainingColorResidues.card = n - (3 * r * r + 8) := by
  constructor
  · rw [P.remainingVertices_card_alt, hlen]
    omega
  · rw [P.remainingColorResidues_card, hlen]
    omega

/-- A supplied rainbow prefix of the specified size closes at the exact stronger
floor. No legacy `4*r*r + 6` connector-prefix budget is used. -/
theorem prefix_complementaryPath {ε0 ε : ℝ} {n0 n : ℕ} [NeZero n]
    (H : OddCyclicRainbowEndpointCompletionAt ε0 n0) (hodd : Odd n) (hn0 : n0 ≤ n)
    (hε : ε ≤ min ε0 ((1 : ℝ) / 100)) (hn : 34 ≤ ε * (n : ℝ))
    (P : RainbowPrefix n)
    (hlen : P.path.length = 3 * radius ε n * radius ε n + 8) :
    Nonempty P.ComplementaryPath := by
  apply P.complementaryPath_of_endpoint hodd
    (t := 3 * radius ε n * radius ε n + 7)
  · omega
  · exact endpointCompletionAt_radius H hodd hn0 hε hn

/-- The completion really gives an actual directed rotational terrace,
preserving both the vertex prefix and its directed differences. The returned
splice's `directedTerrace` enumerates every nonzero residue and colour once. -/
theorem prefix_splicedTerrace {ε0 ε : ℝ} {n0 n : ℕ} [NeZero n]
    (H : OddCyclicRainbowEndpointCompletionAt ε0 n0) (hodd : Odd n) (hn0 : n0 ≤ n)
    (hε : ε ≤ min ε0 ((1 : ℝ) / 100)) (hn : 34 ≤ ε * (n : ℝ))
    (P : RainbowPrefix n)
    (hlen : P.path.length = 3 * radius ε n * radius ε n + 8) :
    ∃ S : EndpointSpliceInput n, S.first = P.first ∧ S.prefixPath = P.path ∧
      P.path <+: S.cycleVertices ∧ pathGaps P.path <+: S.directedTerrace.word := by
  obtain ⟨Q⟩ := prefix_complementaryPath H hodd hn0 hε hn P hlen
  exact ⟨P.splice Q, rfl, rfl, (P.splice Q).prefix_vertices_preserved,
    (P.splice Q).directedTerrace_prefix⟩

/-- At every sufficiently large height, both the new finite prefix conditions
and completion of every supplied rainbow prefix with that length hold.
The displayed threshold is sufficient and is not a claimed first height. -/
theorem prefix_large_height {ε0 ε : ℝ} {n0 h : ℕ}
    (H : OddCyclicRainbowEndpointCompletionAt ε0 n0)
    (hεpos : 0 < ε) (hε : ε ≤ min ε0 ((1 : ℝ) / 100))
    (hh : max 2 (max n0 ⌈34 / ε⌉₊) ≤ h) :
    let n := 2 * h - 1
    let r := radius ε n
    3 ≤ r ∧ 200 * r * r ≤ n ∧
      ((3 * r * r + 7 : ℕ) : ℝ) ≤ ε * (n : ℝ) ∧
      ∀ P : RainbowPrefix n, P.path.length = 3 * r * r + 8 →
        Nonempty P.ComplementaryPath := by
  let n := 2 * h - 1
  let r := radius ε n
  have hh2 : 2 ≤ h := by omega
  have hn0 : n0 ≤ n := by dsimp [n]; omega
  have hnN : ⌈34 / ε⌉₊ ≤ n := by dsimp [n]; omega
  have : NeZero n := ⟨by dsimp [n]; omega⟩
  obtain ⟨hr, hlarge, hbudget⟩ := radius_bounds_of_ceil_threshold hεpos
    (hε.trans (min_le_right _ _)) hnN
  have hsmall : 200 * r * r ≤ n := by dsimp [r]; nlinarith
  have hodd : Odd n := by
    refine ⟨h - 1, ?_⟩
    dsimp [n]
    omega
  have h34 : 34 ≤ ε * (n : ℝ) := by
    have hc : 34 / ε ≤ (⌈34 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : (⌈34 / ε⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have ht := (div_le_iff₀ hεpos).mp (hc.trans hcast)
    nlinarith
  exact ⟨hr, hsmall, hbudget, fun P hlen =>
    prefix_complementaryPath H hodd hn0 hε h34 P hlen⟩

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
