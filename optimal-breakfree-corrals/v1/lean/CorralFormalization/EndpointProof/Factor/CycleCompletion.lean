import CorralFormalization.EndpointProof.Factor.CycleCut
import CorralFormalization.EndpointProof.Factor.Adapter
import CorralFormalization.Results.ConnectorPrefixFloor

/-!
# The full physical endpoint target supplies the cyclic paper receiver

The finite adapter extracts the actual single path from the general physical
path-factor statement, preserving all vertices and all directed differences.
The uniform theorem below is conditional on the full odd-abelian target; it
does not assert the latter's currently missing existence proof.
-/

open scoped BigOperators
namespace EndpointFactor.CycleCut

open CorralFormalization.LatinCompletion.TerraceCompletion

theorem singletonPathFactor_endpoint {n : ℕ} [NeZero n]
    (W D : Finset (ZMod n)) (x y : ZMod n)
    (hxy : x ≠ y) (hz : 0 ∉ D)
    (hfactor : PhysicalPathFactor W D {x} {y}) : EndpointPathClaim W D x y := by
  classical
  obtain ⟨paths, hnonempty, hnum, hsimple, hvertices, hcolors, hD, hstarts, hends⟩ := hfactor
  have hnum' : paths.length = 1 := by simpa using hnum
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hnum'
  have hphead : x ∈ p.head? := by
    have h := (hstarts x).mpr (by simp)
    simpa using h
  have hplast : y ∈ p.getLast? := by
    have h := (hends y).mpr (by simp)
    simpa using h
  have hhead : p.head? = some x := Option.mem_def.mp hphead
  have hlast : p.getLast? = some y := Option.mem_def.mp hplast
  obtain ⟨middle, hp⟩ := list_eq_endpoints p x y hhead hlast hxy
  have hs : p.Nodup := by simpa using hsimple
  have hW : p.toFinset = W := by simpa using hvertices
  have hc : (edgeLabels (fun a b : ZMod n => b - a) p).Nodup := by simpa using hcolors
  have hC : (edgeLabels (fun a b : ZMod n => b - a) p).toFinset = D := by simpa using hD
  have hmap : edgeLabels (fun a b : ZMod n => (b - a).val) p =
      (edgeLabels (fun a b : ZMod n => b - a) p).map ZMod.val := by
    exact edgeLabels_map (fun a b : ZMod n => b - a) ZMod.val p
  have hgaps : pathGaps p = (edgeLabels (fun a b : ZMod n => b - a) p).map ZMod.val := by
    rw [← edgeLabels_zmod_eq_pathGaps, hmap]
  have hnat : (pathGaps p).Nodup := by
    rw [hgaps]
    exact hc.map (ZMod.val_injective n)
  have hnatmem (d : ℕ) : d ∈ pathGaps p ↔ 0 < d ∧ d < n ∧ (d : ZMod n) ∈ D := by
    rw [hgaps, List.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgD : g ∈ D := by rw [← hC]; exact List.mem_toFinset.mpr hg
      have hgn : g ≠ 0 := fun he => hz (he ▸ hgD)
      exact ⟨ZMod.val_pos.mpr hgn, g.val_lt, by simpa using hgD⟩
    · rintro ⟨_, hlt, hd⟩
      refine ⟨(d : ZMod n), ?_, ZMod.val_natCast_of_lt hlt⟩
      exact List.mem_toFinset.mp (by rw [hC]; exact hd)
  refine ⟨middle, ?_, ?_, ?_, ?_⟩
  · simpa only [hp] using hs
  · intro z
    have hz' : z ∈ p ↔ z ∈ W := by rw [← hW, List.mem_toFinset]
    simpa only [hp] using hz'
  · simpa only [hp] using hnat
  · intro d
    simpa only [hp] using hnatmem d

/-- The complete paper-shaped odd-abelian claim implies the exact cyclic
single-path hypothesis already consumed by the corral diversity development.
The threshold is enlarged only to guarantee that one prescribed pair is
allowed by the paper's `K ≤ ε₀ n` condition. -/
theorem cyclicEndpointCompletion_of_uniformPhysical
    (H : UniformPhysicalEndpointCompletion.{0}) : OddCyclicRainbowEndpointCompletion := by
  classical
  obtain ⟨ε, hε, n0, hH⟩ := H
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / ε)
  refine ⟨ε, hε, max n0 N, ?_⟩
  intro n _ hodd hn W D x y hsize hx hy hxy hz hcount hsum
  have hn0 : n0 ≤ n := le_trans (le_max_left _ _) hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (le_max_right n0 N) hn
  have hone : (1 : ℝ) ≤ ε * (n : ℝ) := by
    have hN' : (1 : ℝ) ≤ (N : ℝ) * ε := (div_le_iff₀ hε).mp hN
    nlinarith
  have hsize' : (1 - ε) * (n : ℝ) ≤ (W.card : ℝ) := by nlinarith [hsize]
  have hclaim0 : @PhysicalEndpointConclusion (ZMod n) _ (Classical.decEq (ZMod n))
      W D {x} {y} := by
    apply hH (ZMod n)
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

/-- The original formalized corral lower bound is therefore also available
from the paper-shaped general endpoint statement. -/
theorem uniformPhysical_floor_total_lower (H : UniformPhysicalEndpointCompletion.{0}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ, OddCyclicRainbowEndpointCompletionAt ε0 n0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min ε0 ((1 : ℝ) / 100) →
        ∃ h0 : ℕ, ∃ hh0 : 2 ≤ h0, ∀ (h : ℕ) (hh : h0 ≤ h),
          CorralLatinTailMarker.latinSquareCount (connectorPrefixRadius ε (2*h-1)) ^ h ≤
            CorralFormalization.PhysicalCensus.A_h h (hh0.trans hh) :=
  oddCyclicEndpointCompletion_floor_total_lower (cyclicEndpointCompletion_of_uniformPhysical H)

end EndpointFactor.CycleCut
