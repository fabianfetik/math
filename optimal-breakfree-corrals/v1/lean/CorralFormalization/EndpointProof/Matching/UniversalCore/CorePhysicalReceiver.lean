import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.CoreTail
import CorralFormalization.EndpointProof.Matching.CoreCapacityReceiver

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFullProduct EndpointOriginalReservoir
open EndpointFlow.AbelianTransport EndpointMatching.AbsorptionAssembly
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The three physical parts of the actual original sample. -/
def originalTailSet (s : OriginalSample G) : Finset G :=
  Finset.univ.filter (fun x => s.1 x = 0)
def originalHeadSet (s : OriginalSample G) : Finset G :=
  Finset.univ.filter (fun x => s.1 x = 1)
def originalColourSet (s : OriginalSample G) : Finset G :=
  Finset.univ.filter (fun x => s.2 x = true)

theorem original_signedTarget_iff (s : OriginalSample G) (v : Vertex G) :
    v ∈ signedTarget (originalTailSet s) (originalHeadSet s) (originalColourSet s) ↔
      originalSigned v.1 s v.2 := by
  rcases v with ⟨part,g⟩
  fin_cases part
  · have h := signedTarget_tail_mem (originalTailSet s) (originalHeadSet s) (originalColourSet s) (-g)
    simpa [originalTailSet, originalHeadSet, originalColourSet, originalSigned] using h
  · simp [originalTailSet, originalHeadSet, originalColourSet, originalSigned]
  · have h := signedTarget_color_mem (originalTailSet s) (originalHeadSet s) (originalColourSet s) (-g)
    simpa [originalTailSet, originalHeadSet, originalColourSet, originalSigned] using h

/-- The nonzero raw-minus core set is genuinely contained in the signed
original physical sample of the same augmentation. -/
theorem nonzeroRawMinus_subset_original (ω : FullSample G) :
    nonzeroRawMinus ω ⊆ signedTarget (originalTailSet (originalProcess ω))
      (originalHeadSet (originalProcess ω)) (originalColourSet (originalProcess ω)) := by
  intro v hv
  apply (original_signedTarget_iff (originalProcess ω) v).mpr
  exact signedMinus_subset_originalSigned v.1 ω v.2 ((Finset.mem_filter.mp hv).2.2)

omit [Fintype G] in
/-- A larger proven absorption capacity can be safely used at a smaller
integer capacity. -/
theorem absorbsUpTo_mono {A : Finset (Vertex G)} {a b : ℕ}
    (hab : a ≤ b) (h : AbsorbsUpTo A b) : AbsorbsUpTo A a := by
  intro S hz hb hs hd hS
  exact h S hz hb hs hd (hS.trans hab)

omit [Fintype G] in
theorem rawCoreSupply_mono {R : Finset (Vertex G)} {a b bound : ℕ}
    (hab : a ≤ b) (h : RawCoreSupply R b bound) : RawCoreSupply R a bound := by
  intro U hU
  obtain ⟨A,hsub,hdisj,hsize,habs⟩ := h U (hU.trans hab)
  exact ⟨A,hsub,hdisj,hsize,absorbsUpTo_mono hab habs⟩

/-- The smaller original exact-matching radius fits into the proven quadratic core
capacity for every density in the actual range. -/
theorem kappa_le_quadratic_core (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    kappa q ≤ (1 / 10^6 : ℝ) * (tau q)^2 := by
  obtain ⟨_,_,_,_,_,_,hcat,_,_⟩ :=
    samplingParameters_admissible q hq0 hq1
  have hτ0 : 0 ≤ tau q := by unfold tau p CorralFormalization.EndpointProof.RateBudget.SamplingConstants.rho eta; positivity
  have hcat' : 3 * (pNN q : ℝ) + 3 * (tauNN q : ℝ) ≤ 1 := by exact_mod_cast hcat
  have hτ1 : tau q ≤ 1 := by
    change 3 * p q + 3 * tau q ≤ 1 at hcat'
    have : 0 ≤ p q := by unfold p CorralFormalization.EndpointProof.RateBudget.SamplingConstants.rho eta; positivity
    nlinarith
  have hpow : (tau q)^9 ≤ (tau q)^2 :=
    pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
  unfold kappa
  have hs : 0 ≤ (tau q)^2 := sq_nonneg _
  nlinarith

theorem kappa_capacity_le_quadratic_core (q : ℝ) (n : ℕ)
    (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    ⌊kappa q * (n : ℝ)⌋₊ ≤ quadraticCoreCapacity (tau q) n := by
  unfold quadraticCoreCapacity
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right (kappa_le_quadratic_core q hq0 hq1) (Nat.cast_nonneg n)

/-- The proved paper core event discharges the old exact-matching receiver's core
supplier on the very same actual sample, at the smaller stated capacity. -/
theorem universalCoreEvent_kappa_supply (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2)
    (ω : FullSample G) (hcore : UniversalCoreEvent (tau q) ω) :
    RawCoreSupply (nonzeroRawMinus ω) ⌊kappa q * (Fintype.card G : ℝ)⌋₊
      ⌊16200 * tau q * (Fintype.card G : ℝ)⌋₊ := by
  exact rawCoreSupply_mono (kappa_capacity_le_quadratic_core q _ hq0 hq1)
    (universalCoreEvent_rawCoreSupply hcore)

/-- The physical-edit allowance and the proven core-size allowance use at
most half of the fractional supplier's q²/10000 deletion budget. -/
theorem core_and_edit_coefficients_le_fractional_budget
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) :
    16200 * tau q + (1 / 10^6 : ℝ) * kappa q ≤ q^2 / 20000 := by
  obtain ⟨_,_,_,_,_,_,hcat,_,_⟩ := samplingParameters_admissible q hq0 hq1
  have hp0 : 0 ≤ p q := by unfold p CorralFormalization.EndpointProof.RateBudget.SamplingConstants.rho eta; positivity
  have hτ0 : 0 ≤ tau q := by unfold tau p CorralFormalization.EndpointProof.RateBudget.SamplingConstants.rho eta; positivity
  have hcat' : 3 * p q + 3 * tau q ≤ 1 := by exact_mod_cast hcat
  have hp1 : p q ≤ 1 := by nlinarith
  have hτ1 : tau q ≤ 1 := by nlinarith
  have hp4 : (p q)^4 ≤ p q := pow_le_of_le_one hp0 hp1 (by norm_num)
  have hτp : tau q ≤ p q := by unfold tau; nlinarith
  have ht9 : (tau q)^9 ≤ tau q := pow_le_of_le_one hτ0 hτ1 (by norm_num)
  have hkτ : kappa q ≤ tau q := by unfold kappa; nlinarith
  have hpformula : p q = q^2 / (36 * 10^8) := by
    unfold p CorralFormalization.EndpointProof.RateBudget.SamplingConstants.rho eta
    ring
  have hq2 : 0 ≤ q^2 := sq_nonneg q
  nlinarith

/-- The fixed core and the exact-matching edit radius leave room for the possible
extra zero-cover edge inside the actual robust fractional deletion budget. -/
theorem core_and_edit_budget_for_fractional_supplier
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) (n : ℕ)
    (distance coreSize : ℕ)
    (hd : (distance : ℝ) ≤ (1 / 10^6 : ℝ) * kappa q * n)
    (ha : (coreSize : ℝ) ≤ 16200 * tau q * n)
    (hn : (60000 : ℝ) ≤ q^2 * n) :
    (distance : ℝ) + coreSize + 3 ≤ (q^2 / 10000) * n := by
  have hc := core_and_edit_coefficients_le_fractional_budget q hq0 hq1
  have hm := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n)
  nlinarith

/-- Physical exact matching from the proved core event and a still-explicit
later compatible-near-matching input; the receiver uses the actual original
sample of this augmentation and uniform exact-matching theorem's stated edit radius. -/
theorem physical_exact_from_universalCore
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1/2) (ω : FullSample G)
    (hcore : UniversalCoreEvent (tau q) ω)
    (X Y C : Finset G)
    (hdistance : (physicalEditDistance (originalTailSet (originalProcess ω))
      (originalHeadSet (originalProcess ω)) (originalColourSet (originalProcess ω)) X Y C : ℝ) ≤
        (1 / 10^6 : ℝ) * kappa q * (Fintype.card G : ℝ))
    (hlarge : (2 : ℝ) ≤ kappa q * (Fintype.card G : ℝ))
    (hXY : X.card = Y.card) (hXC : X.card = C.card)
    (hchecksum : (∑ c ∈ C, c) = (∑ y ∈ Y, y) - ∑ x ∈ X, x)
    (hnear : ∀ A : Finset (Vertex G), A ⊆ signedTarget X Y C →
      (∀ v ∈ A, v.2 ≠ 0) → Balanced A → (∑ v ∈ A, v.2 = 0) →
      A.card ≤ ⌊16200 * tau q * (Fintype.card G : ℝ)⌋₊ →
      Nonempty (CompatibleNearMatching (signedTarget X Y C) A
        ⌊kappa q * (Fintype.card G : ℝ)⌋₊)) :
    Nonempty (PhysicalDifferenceMatching X Y C) := by
  exact physical_exact_of_core_capacity_suppliers q (Fintype.card G)
    ⌊16200 * tau q * (Fintype.card G : ℝ)⌋₊ (nonzeroRawMinus_subset_original ω)
    (universalCoreEvent_kappa_supply q hq0 hq1 ω hcore) hdistance hlarge
    hXY hXC hchecksum hnear

end
end EndpointMatching.UniversalCore
