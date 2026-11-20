import CorralFormalization.EndpointProof.Factor.LayeredTransitions

/-!
# The layer densities used by the ordinary transitions

These deterministic estimates discharge the manuscript's two generic
density windows from explicit, stronger slack assumptions. They do not
choose the paper's parameters or assert the later router budget.
-/

open scoped BigOperators Classical
namespace EndpointLayeredSample

open EndpointTransitions

noncomputable section

/-- For `J = m+3` and `k = J+9 = m+12`, the stated layer mass
equations give the paper's `0.9q < a,c ≤ (1-r/2)q` whenever `r` is
at most `1/10` and at least `100q`. -/
theorem explicitDensityWindows {m : ℕ} (hm : 0 < m) (d : Densities m)
    (hq : 0 < d.q) (hr : d.r ≤ 1/10) (hqr : 100*d.q ≤ d.r)
    (hqk : d.q*((m : ℝ)+12) = 1) :
    d.q ≤ 1/3 ∧
      (9*d.q/10 < d.a ∧ d.a ≤ (1-d.r/2)*d.q) ∧
      (9*d.q/10 < d.c ∧ d.c ≤ (1-d.r/2)*d.q) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hp0 : 0 < (m : ℝ)+1 := by positivity
  have hqr0 : 0 ≤ d.r*d.q := mul_nonneg d.r_nonneg hq.le
  have hmq : (m : ℝ)*d.q = 1-12*d.q := by nlinarith
  have hmpq : ((m : ℝ)+1)*d.q = 1-11*d.q := by nlinarith
  have hva : (m : ℝ)*d.a = 1-d.r-3*d.q := by linarith [d.vertex_total]
  have hvc : ((m : ℝ)+1)*d.c = 1-d.r-d.q := by
    have hct := d.colour_total
    push_cast at hct
    linarith
  have hprodA : (m : ℝ)*((1-d.r/2)*d.q) = (1-d.r/2)*(1-12*d.q) := by
    rw [← hmq]
    ring
  have hprodC : ((m : ℝ)+1)*((1-d.r/2)*d.q) = (1-d.r/2)*(1-11*d.q) := by
    rw [← hmpq]
    ring
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hq.le]
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- The generic vertex and ordinary-colour roles meet ordinary transition lemma's exact density
window; special roles of mass `q` meet it as well. -/
theorem ordinaryTransitionDensityWindows {m : ℕ} (hm : 0 < m) (d : Densities m)
    (hq : 0 < d.q) (hr : d.r ≤ 1/10) (hqr : 100*d.q ≤ d.r)
    (hqk : d.q*((m : ℝ)+12) = 1) :
    DensityWindow d.q d.a ∧ DensityWindow d.q d.c ∧ DensityWindow d.q d.q := by
  obtain ⟨_, ⟨ha, ha'⟩, ⟨hc, hc'⟩⟩ := explicitDensityWindows hm d hq hr hqr hqk
  have hcap : (1-d.r/2)*d.q ≤ d.q := by
    have := mul_nonneg d.r_nonneg hq.le
    nlinarith
  exact ⟨⟨ha.le, ha'.trans hcap⟩, ⟨hc.le, hc'.trans hcap⟩, ⟨by linarith, le_rfl⟩⟩

/-- Ordinary layer roles exclude the two reserves; all other roles have one
of the three paper densities `q`, `a`, or `c`. -/
def NonReserveRole {m : ℕ} : RawRole m → Prop
  | Sum.inl v => v ≠ reserveVertex m
  | Sum.inr c => c ≠ reserveColour m

theorem explicitRole_densityWindow {m : ℕ} (hm : 0 < m) (d : Densities m)
    (hq : 0 < d.q) (hr : d.r ≤ 1/10) (hqr : 100*d.q ≤ d.r)
    (hqk : d.q*((m : ℝ)+12) = 1) (role : RawRole m) (hrole : NonReserveRole role) :
    DensityWindow d.q (roleDensity d role) := by
  obtain ⟨ha, hc, hq'⟩ := ordinaryTransitionDensityWindows hm d hq hr hqr hqk
  cases role with
  | inl v =>
    cases v with
    | inl i =>
      have hi : i ≠ 0 := by simpa [NonReserveRole, reserveVertex] using hrole
      simpa [roleDensity, vertexWeight, hi] using hq'
    | inr i => simpa [roleDensity, vertexWeight] using ha
  | inr c =>
    cases c with
    | inl i =>
      have hi : i ≠ 0 := by simpa [NonReserveRole, reserveColour] using hrole
      simpa [roleDensity, colourWeight, hi] using hq'
    | inr i => simpa [roleDensity, colourWeight] using hc

/-- Any positive small reserve density admits an even paper parameter `T`
above an arbitrary prescribed real bound. The resulting actual categorical
law has `k=2T=m+12`, `q=1/k`, and both generic ordinary-transition density windows. In
particular the caller may use the maximum of the two lower bounds in §5. -/
theorem exists_evenExplicitDensities (r L : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1/10) :
    ∃ T : ℕ, Even T ∧ L ≤ (T : ℝ) ∧
      ∃ m : ℕ, 0 < m ∧ m + 12 = 2*T ∧ ∃ d : Densities m,
        d.r = r ∧ 0 < d.q ∧ 100*d.q ≤ d.r ∧ d.q*((m : ℝ)+12) = 1 ∧
          d.q ≤ 1/3 ∧ DensityWindow d.q d.a ∧ DensityWindow d.q d.c := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (100/r) L)
  let m : ℕ := 4*(N+1)
  let T : ℕ := 2*(N+4)
  let q : ℝ := 1/((m : ℝ)+12)
  have hm : 0 < m := by dsimp [m]; omega
  have hk : 0 < (m : ℝ)+12 := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hNratio : 100/r ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNL : L ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hNr : 100 ≤ (N : ℝ)*r := (div_le_iff₀ hr).mp hNratio
  have hmN : (N : ℝ) ≤ (m : ℝ)+12 := by dsimp [m]; push_cast; linarith
  have hqr : 100*q ≤ r := by
    have hmult := mul_le_mul_of_nonneg_right hmN hr.le
    have hbig : 100 ≤ r*((m : ℝ)+12) := by nlinarith
    dsimp [q]
    rw [mul_one_div]
    exact (div_le_iff₀ hk).mpr hbig
  have hrq : r + 3*q ≤ 1 := by nlinarith
  let d := Densities.ofLayerParameters m hm r q hr.le hq.le hrq
  have hqk : d.q*((m : ℝ)+12) = 1 := by
    change q*((m : ℝ)+12) = 1
    dsimp [q]
    field_simp
  have hqthird := (explicitDensityWindows hm d hq hrsmall hqr hqk).1
  have hwindows := ordinaryTransitionDensityWindows hm d hq hrsmall hqr hqk
  refine ⟨T, ?_, ?_, m, hm, ?_, d, rfl, hq, hqr, hqk, hqthird, hwindows.1, hwindows.2.1⟩
  · dsimp [T]
    exact ⟨N+4, by omega⟩
  · dsimp [T]
    push_cast
    linarith
  · dsimp [m, T]
    omega

end
end EndpointLayeredSample
