import CorralFormalization.Results.ConnectorPrefixFloor
import CorralFormalization.Results.CompletionFromMatching
import CorralFormalization.Results.ConnectorFreePrefix.StrongDiversityTheorem

/-!
# Completing an arbitrary short rainbow path to a terrace

This is the path-to-terrace corollary for an arbitrary supplied path, not just
the special prefixes used in the diversity construction.  The same endpoint
tolerance is retained.  The final theorem keeps the external AKS and
Pippenger inputs explicit.
-/

open EndpointTransitions EndpointMatching.Fractional.Rounding
open CorralFormalization.LatinCompletion.TerraceCompletion
open EndpointFactor.CycleCut
open CorralLatinTailMarker CorralFormalization.PhysicalCensus
open scoped BigOperators

noncomputable section

namespace CorralFormalization.Results.PathTerraceCompletion

/-- The complete odd-abelian endpoint conclusion at specified witnesses.
This is the body of `UniformPhysicalEndpointCompletion`, with its tolerance
and threshold named so they can be shared by subsequent statements. -/
def UniformPhysicalEndpointCompletionAt (ε0 : ℝ) (n0 : ℕ) : Prop := by
  classical
  exact ∀ (G : Type) [Fintype G] [AddCommGroup G],
    Odd (Fintype.card G) → n0 ≤ Fintype.card G →
    ∀ W D X Y : Finset G,
      X ⊆ W → Y ⊆ W → Disjoint X Y → X.card = Y.card →
      (X.card : ℝ) ≤ ε0 * (Fintype.card G : ℝ) →
      (1 - ε0) * (Fintype.card G : ℝ) ≤ (W.card : ℝ) →
      (0 : G) ∉ D → D.card + X.card = W.card →
      (∑ d ∈ D, d) = (∑ y ∈ Y, y) - (∑ x ∈ X, x) →
      PhysicalEndpointConclusion W D X Y

/-- Extract the singleton cyclic receiver using exactly the same tolerance
as a specified uniform odd-abelian witness. Only the threshold is enlarged. -/
theorem cyclicCompletionAt_of_uniformPhysicalAt {ε0 : ℝ} {n0 : ℕ}
    (hε : 0 < ε0) (H : UniformPhysicalEndpointCompletionAt ε0 n0) :
    ∃ N : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 N := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / ε0)
  refine ⟨max n0 N, ?_⟩
  intro n _ hodd hn W D x y hsize hx hy hxy hz hcount hsum
  have hn0 : n0 ≤ n := le_trans (le_max_left _ _) hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (le_max_right n0 N) hn
  have hone : (1 : ℝ) ≤ ε0 * (n : ℝ) := by
    have hN' : (1 : ℝ) ≤ (N : ℝ) * ε0 := (div_le_iff₀ hε).mp hN
    nlinarith
  have hsize' : (1 - ε0) * (n : ℝ) ≤ (W.card : ℝ) := by nlinarith [hsize]
  have hclaim0 : @PhysicalEndpointConclusion (ZMod n) _ (Classical.decEq (ZMod n))
      W D {x} {y} := by
    apply H (ZMod n)
    · simpa [ZMod.card] using hodd
    · simpa [ZMod.card] using hn0
    · simpa using hx
    · simpa using hy
    · simpa [Finset.disjoint_singleton] using hxy
    · simp
    · simpa [ZMod.card] using hone
    · simpa [ZMod.card] using hsize'
    · exact hz
    · simpa using hcount
    · simpa using hsum
  have hclaim : PhysicalEndpointConclusion W D {x} {y} := by
    have hdec : Classical.decEq (ZMod n) = ZMod.decidableEq n := Subsingleton.elim _ _
    change @PhysicalEndpointConclusion (ZMod n) _ (ZMod.decidableEq n) W D {x} {y}
    rw [← hdec]
    exact hclaim0
  exact singletonPathFactor_endpoint W D x y hxy hz (hclaim.2 (by simp))

theorem pathGaps_lt {n : ℕ} [NeZero n] (p : List (ZMod n))
    (d : ℕ) (hd : d ∈ pathGaps p) : d < n := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hd
  have hil : i + 1 < p.length := by
    have := hi
    rw [pathGaps_length] at this
    omega
  rw [pathGaps_getElem p i hil] at heq
  rw [← heq]
  exact ZMod.val_lt _

/-- The directed differences in the group itself, before choosing natural
representatives. -/
def directedDifferences {n : ℕ} (p : List (ZMod n)) : List (ZMod n) :=
  EndpointFactor.edgeLabels (fun a b : ZMod n => b - a) p

theorem pathGaps_eq_map_directedDifferences {n : ℕ} (p : List (ZMod n)) :
    pathGaps p = (directedDifferences p).map ZMod.val := by
  rw [← EndpointFactor.edgeLabels_zmod_eq_pathGaps,
    EndpointFactor.edgeLabels_map]
  rfl

theorem pathGaps_nodup_iff_directedDifferences {n : ℕ} [NeZero n] (p : List (ZMod n)) :
    (pathGaps p).Nodup ↔ (directedDifferences p).Nodup := by
  rw [pathGaps_eq_map_directedDifferences, List.nodup_map_iff (ZMod.val_injective n)]

theorem pathGaps_nonzero_iff_directedDifferences {n : ℕ} [NeZero n] (p : List (ZMod n)) :
    (∀ d ∈ pathGaps p, d ≠ 0) ↔ (∀ d ∈ directedDifferences p, d ≠ 0) := by
  rw [pathGaps_eq_map_directedDifferences]
  constructor
  · intro h d hd hd0
    have hmem : d.val ∈ (directedDifferences p).map ZMod.val :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    exact h d.val hmem (by simp [hd0])
  · intro h d hd hd0
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    apply h z hz
    apply ZMod.val_injective n
    simpa using hd0

/-- Every list satisfying the path hypotheses is represented by an actual
`RainbowPrefix`, including its first and last vertices. -/
theorem rainbowPrefix_of_list {n : ℕ} [NeZero n] (p : List (ZMod n))
    (hlen : 2 ≤ p.length) (hsimple : p.Nodup)
    (hnonzero : ∀ x ∈ p, x ≠ 0)
    (hrainbow : (pathGaps p).Nodup)
    (hcolors : ∀ d ∈ pathGaps p, d ≠ 0) :
    ∃ P : RainbowPrefix n, P.path = p := by
  have hnon : p ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  obtain ⟨initialPart, hpart⟩ :=
    List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast hnon)
  cases initialPart with
  | nil =>
    rw [hpart] at hlen
    simp at hlen
  | cons first interior =>
    let P : RainbowPrefix n := {
      first := first
      last := p.getLast hnon
      interior := interior
      simple := by rw [← hpart]; exact hsimple
      nonzero := by intro x hx; rw [← hpart] at hx; exact hnonzero x hx
      rainbow := by rw [← hpart]; exact hrainbow
      colors := by
        intro d hd
        rw [← hpart] at hd
        exact ⟨Nat.pos_of_ne_zero (hcolors d hd), pathGaps_lt p d hd⟩
    }
    exact ⟨P, hpart.symm⟩

/-- The actual cycle-vertex list agrees with the vertex ordering in the
constructed directed terrace. -/
theorem splice_terrace_vertices {n : ℕ} (S : EndpointSpliceInput n) :
    List.ofFn (fun i : Fin (n-1) => (S.directedTerrace.vertices i).val) =
      S.cycleVertices := by
  apply List.ext_getElem
  · simp [S.cycle_length]
  · intro i hi hi'
    simp only [List.getElem_ofFn]
    exact S.vertexEquiv_val ⟨i, by simpa using hi⟩

/-- For a fixed cyclic endpoint witness, every eligible supplied path extends
to an actual directed terrace, with the vertex path and its edge gaps both
preserved at the beginning of the corresponding cyclic order. -/
theorem path_terrace_of_cyclicCompletionAt {ε0 : ℝ} {n0 n : ℕ} [NeZero n]
    (H : OddCyclicRainbowEndpointCompletionAt ε0 n0)
    (hodd : Odd n) (hn0 : n0 ≤ n) (p : List (ZMod n))
    (hlen : 2 ≤ p.length) (hsimple : p.Nodup)
    (hnonzero : ∀ x ∈ p, x ≠ 0)
    (hrainbow : (pathGaps p).Nodup)
    (hcolors : ∀ d ∈ pathGaps p, d ≠ 0)
    (hbudget : ((p.length - 1 : ℕ) : ℝ) ≤ ε0 * (n : ℝ)) :
    ∃ D : DirectedTerrace n,
      p <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
      pathGaps p <+: D.word := by
  obtain ⟨P, hpath⟩ := rainbowPrefix_of_list p hlen hsimple hnonzero hrainbow hcolors
  have hlen_n : P.path.length ≤ n := by
    classical
    have hcard := Finset.card_le_univ P.path.toFinset
    have hnodup : P.path.Nodup := P.simple
    rw [List.toFinset_card_of_nodup hnodup, ZMod.card] at hcard
    exact hcard
  have hlocal := oddCyclicEndpointCompletionAt_local H hodd hn0
    (by omega : P.path.length - 1 ≤ n) (by simpa [hpath] using hbudget)
  obtain ⟨Q⟩ := P.complementaryPath_of_endpoint hodd (le_refl _) hlocal
  let S := P.splice Q
  refine ⟨S.directedTerrace, ?_, ?_⟩
  · rw [splice_terrace_vertices, ← hpath]
    exact S.prefix_vertices_preserved
  · rw [← hpath]
    exact S.directedTerrace_prefix

/-- The arbitrary-path corollary follows from the two stated external
matching inputs; endpoint completion is derived, not an extra premise. -/
theorem path_terrace_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
      OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ (n : ℕ), Odd n → n0 ≤ n →
        ∀ p : List (ZMod n),
          2 ≤ p.length → p.Nodup → (∀ x ∈ p, x ≠ 0) →
          (directedDifferences p).Nodup → (∀ d ∈ directedDifferences p, d ≠ 0) →
          ((p.length - 1 : ℕ) : ℝ) ≤ ε0 * (n : ℝ) →
          ∃ D : DirectedTerrace n,
            p <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
            pathGaps p <+: D.word := by
  obtain ⟨ε0, hε0, n0, H⟩ := oddCyclicEndpointCompletion_iff.mp
    (CorralFormalization.Results.cyclicCompletion_from_matching_inputs hAKS hPippenger)
  refine ⟨ε0, hε0, n0, H, ?_⟩
  intro n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors hbudget
  have hnz : n ≠ 0 := by intro hn; subst n; norm_num at hodd
  have : NeZero n := ⟨hnz⟩
  exact path_terrace_of_cyclicCompletionAt H hodd hn0 p hlen hsimple hnonzero
    ((pathGaps_nodup_iff_directedDifferences p).mpr hrainbow)
    ((pathGaps_nonzero_iff_directedDifferences p).mpr hcolors) hbudget

/-- Paper-wide witness alignment: the odd-abelian endpoint theorem and the
arbitrary-path corollary share one actual tolerance. The cyclic corollary may
use a larger threshold to permit a singleton pair of endpoints. -/
theorem uniform_endpoint_and_path_terrace_from_matching_inputs
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ,
        OddCyclicRainbowEndpointCompletionAt ε0 Npath ∧
        ∀ (n : ℕ), Odd n → Npath ≤ n →
          ∀ p : List (ZMod n),
            2 ≤ p.length → p.Nodup → (∀ x ∈ p, x ≠ 0) →
            (directedDifferences p).Nodup → (∀ d ∈ directedDifferences p, d ≠ 0) →
            ((p.length - 1 : ℕ) : ℝ) ≤ ε0 * (n : ℝ) →
            ∃ D : DirectedTerrace n,
              p <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
              pathGaps p <+: D.word := by
  obtain ⟨ε0, hε0, Nphysical, hphysical⟩ :=
    EndpointFactor.uniformPhysicalEndpointCompletion_from_AKS_Pippenger hAKS hPippenger
  have hphysical' : UniformPhysicalEndpointCompletionAt ε0 Nphysical := hphysical
  obtain ⟨Npath, H⟩ := cyclicCompletionAt_of_uniformPhysicalAt hε0 hphysical'
  refine ⟨ε0, hε0, Nphysical, hphysical', Npath, H, ?_⟩
  intro n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors hbudget
  have hnz : n ≠ 0 := by intro hn; subst n; norm_num at hodd
  have : NeZero n := ⟨hnz⟩
  exact path_terrace_of_cyclicCompletionAt H hodd hn0 p hlen hsimple hnonzero
    ((pathGaps_nodup_iff_directedDifferences p).mpr hrainbow)
    ((pathGaps_nonzero_iff_directedDifferences p).mpr hcolors) hbudget

/-- Shrinking the witness tolerance preserves the uniform odd-abelian endpoint
conclusion. This permits independently proved consequences to share a single
paper-wide tolerance. -/
theorem uniformPhysicalAt_of_smaller_tolerance {ε0 ε1 : ℝ} {n0 : ℕ}
    (H : UniformPhysicalEndpointCompletionAt ε1 n0) (hle : ε0 ≤ ε1) :
    UniformPhysicalEndpointCompletionAt ε0 n0 := by
  classical
  intro G _ _ hodd hn0 W D X Y hX hY hXY hcard hK hW hz hcount hsum
  have hmul : ε0 * (Fintype.card G : ℝ) ≤ ε1 * (Fintype.card G : ℝ) :=
    mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
  apply H G hodd hn0 W D X Y hX hY hXY hcard (hK.trans hmul) ?_ hz hcount hsum
  nlinarith [hW, hmul]

/-- The endpoint theorem, arbitrary-path corollary and both finite diversity
bounds can share a tolerance using only the two matching inputs. In
particular, the finite bounds do not require the Latin-square estimate. -/
theorem shared_tolerance_endpoint_path_and_finite_diversity
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ,
        (∀ (n : ℕ), Odd n → Npath ≤ n →
          ∀ p : List (ZMod n),
            2 ≤ p.length → p.Nodup → (∀ x ∈ p, x ≠ 0) →
            (directedDifferences p).Nodup → (∀ d ∈ directedDifferences p, d ≠ 0) →
            ((p.length - 1 : ℕ) : ℝ) ≤ ε0 * (n : ℝ) →
            ∃ D : DirectedTerrace n,
              p <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
              pathGaps p <+: D.word) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
          ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
            latinSquareCount
                (ConnectorFreePrefix.radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
            latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) := by
  obtain ⟨εpath, hεpath, Nphysical, hphysical, Npath, hcyclic, hpath⟩ :=
    uniform_endpoint_and_path_terrace_from_matching_inputs hAKS hPippenger
  obtain ⟨εcount, hεcount, _, _, hcount⟩ :=
    ConnectorFreePrefix.strong_floor_count_from_matching_and_prefix hAKS hPippenger
      ConnectorFreePrefix.literalRainbowPrefixSupply_proved
  refine ⟨min εpath εcount, lt_min hεpath hεcount, Nphysical,
    uniformPhysicalAt_of_smaller_tolerance hphysical (min_le_left _ _), Npath, ?_, ?_⟩
  · intro n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors hbudget
    apply hpath n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors
    exact hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  · intro ε hε hbound
    have hpathbound : ε ≤ min εpath ((1 : ℝ)/100) :=
      le_min ((le_min_iff.mp hbound).1.trans (min_le_left _ _)) (le_min_iff.mp hbound).2
    have hcountbound : ε ≤ min εcount ((1 : ℝ)/100) :=
      le_min ((le_min_iff.mp hbound).1.trans (min_le_right _ _)) (le_min_iff.mp hbound).2
    obtain ⟨h1, hh1, hstrong⟩ := hcount ε hε hcountbound
    obtain ⟨h2, hh2, hold⟩ := oddCyclicEndpointCompletionAt_floor_total_lower hcyclic hε hpathbound
    refine ⟨max h1 h2, by omega, ?_⟩
    intro h hh
    exact ⟨hstrong h (by omega), hold h (by omega)⟩

/-- The paper's general endpoint result, arbitrary-path completion, and both
diversity floors admit a single positive tolerance. The logarithmic estimate
and `Theta` conclusion additionally use the published Latin-square input. -/
theorem shared_tolerance_endpoint_path_and_diversity
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{0} K D₀ C)
    (hPippenger : PippengerTheorem.{0})
    (hLatin : Asymptotic.LatinSquareFactorialBound) :
    (∃ ε0 : ℝ, 0 < ε0 ∧ ∃ Nphysical : ℕ,
      UniformPhysicalEndpointCompletionAt ε0 Nphysical ∧
      ∃ Npath : ℕ,
        (∀ (n : ℕ), Odd n → Npath ≤ n →
          ∀ p : List (ZMod n),
            2 ≤ p.length → p.Nodup → (∀ x ∈ p, x ≠ 0) →
            (directedDifferences p).Nodup → (∀ d ∈ directedDifferences p, d ≠ 0) →
            ((p.length - 1 : ℕ) : ℝ) ≤ ε0 * (n : ℝ) →
            ∃ D : DirectedTerrace n,
              p <+: List.ofFn (fun i : Fin (n-1) => (D.vertices i).val) ∧
              pathGaps p <+: D.word) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ)/100) →
          ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
            latinSquareCount
                (ConnectorFreePrefix.radius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
            latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤ A_h h (hh0.trans hh) ∧
            (ε/3)*(h : ℝ)^2*Real.log (h : ℝ) -
                ConnectorFreePrefix.radiusErrorConstant ε*(h : ℝ)^2 ≤
              Real.log (A_h h (hh0.trans hh) : ℝ))) ∧
      Asymptotics.IsTheta Filter.atTop Asymptotic.logAsymmetricCount Asymptotic.entropyScale := by
  obtain ⟨εpath, hεpath, Nphysical, hphysical, Npath, _, hpath⟩ :=
    uniform_endpoint_and_path_terrace_from_matching_inputs hAKS hPippenger
  obtain ⟨⟨εdiv, hεdiv, hdiv⟩, htheta⟩ :=
    ConnectorFreePrefix.strong_diversity_from_matching_and_latin_inputs hAKS hPippenger hLatin
  refine ⟨⟨min εpath εdiv, lt_min hεpath hεdiv, Nphysical,
    uniformPhysicalAt_of_smaller_tolerance hphysical (min_le_left _ _), Npath, ?_, ?_⟩, htheta⟩
  · intro n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors hbudget
    apply hpath n hodd hn0 p hlen hsimple hnonzero hrainbow hcolors
    exact hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  · intro ε hε hbound
    apply hdiv ε hε
    exact le_min ((le_min_iff.mp hbound).1.trans (min_le_right _ _)) (le_min_iff.mp hbound).2

end CorralFormalization.Results.PathTerraceCompletion
end
