import CorralFormalization.EndpointProof.Factor.ParameterBudget
import CorralFormalization.EndpointProof.Matching.UniversalCore.CorePhysicalReceiver

/-!
# The actual tolerance hierarchy for the paper's common sample

These are the positive fixed constants in the path-factor construction, after the external
Pippenger constant has been selected. The estimates here pay the formal
ordinary-transition inputs and the displayed router slack; they do not
construct the layer fills or the geometric router.
-/

namespace EndpointLayeredSample

open CorralFormalization.EndpointProof.RateBudget.SamplingConstants
open EndpointMatching.UniversalCore
open EndpointMatching.Fractional.Rounding EndpointTransitions

noncomputable section
universe u

/-- uniform exact-matching theorem's actual symmetric-difference radius. -/
def explicitDelta (q : ℝ) : ℝ := (1 / 10^6 : ℝ) * kappa q

/-- Here `J = m+3`, since the layer model uses `m=J-3`. -/
def explicitTheta (q : ℝ) (m : ℕ) : ℝ := explicitDelta q / (10000*((m : ℝ)+3))

def explicitThinning (r : ℝ) : ℝ := r/4

def explicitRouterDensity (u : ℝ) : ℝ := u^22/20000

def explicitEta (q : ℝ) (m : ℕ) (μ : ℝ) : ℝ :=
  min (q/1000) (min (explicitTheta q m/100) (q^2*μ/1000))

def explicitEpsilon (q : ℝ) (m : ℕ) (μ r b : ℝ) : ℝ :=
  min (explicitEta q m μ/10000)
    (min (explicitDelta q/100000)
      (min (b/10^8) (min (r*q/10^8) (1/10^8))))

theorem explicitThinning_bounds (r : ℝ) (hr : 0 < r) :
    0 < explicitThinning r ∧ explicitThinning r ≤ r := by
  unfold explicitThinning
  constructor <;> linarith

theorem explicitRouterDensity_bounds (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    0 < explicitRouterDensity u ∧ explicitRouterDensity u ≤ u/2 := by
  have hp : u^21 ≤ 1 := pow_le_one₀ hu.le hu1
  have hpow : u^22 ≤ u := by
    rw [show 22 = 21+1 by decide, pow_succ]
    nlinarith
  unfold explicitRouterDensity
  constructor
  · positivity
  · nlinarith

theorem explicitDelta_bounds (q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1/2) :
    0 < explicitDelta q ∧ explicitDelta q ≤ q^2 := by
  have hδ : 0 < explicitDelta q := by
    unfold explicitDelta kappa tau p rho eta
    positivity
  have hbound := core_and_edit_coefficients_le_fractional_budget q hq hqhalf
  have hτ : 0 ≤ tau q := by unfold tau p rho eta; positivity
  refine ⟨hδ, ?_⟩
  unfold explicitDelta
  nlinarith [sq_nonneg q]

theorem explicitTheta_bounds (q : ℝ) (m : ℕ) (hq : 0 < q) (hqthird : q ≤ 1/3) :
    0 < explicitTheta q m ∧ explicitTheta q m ≤ 1/10 := by
  have hdelta := explicitDelta_bounds q hq (by linarith)
  have hden : 0 < 10000*((m : ℝ)+3) := by positivity
  refine ⟨div_pos hdelta.1 hden, ?_⟩
  unfold explicitTheta
  apply (div_le_iff₀ hden).mpr
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hqsq : q^2 ≤ 1 := by nlinarith
  nlinarith

theorem explicitEta_bounds (q : ℝ) (m : ℕ) (μ : ℝ)
    (hq : 0 < q) (hqthird : q ≤ 1/3) (hμ : 0 < μ) :
    0 < explicitEta q m μ ∧ explicitEta q m μ ≤ q/1000 ∧
      explicitEta q m μ ≤ explicitTheta q m/100 ∧ explicitEta q m μ ≤ q^2*μ/1000 := by
  have hθ : 0 < explicitTheta q m := (explicitTheta_bounds q m hq hqthird).1
  unfold explicitEta
  exact ⟨lt_min (by positivity) (lt_min (by positivity) (by positivity)),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

theorem explicitEpsilon_bounds (q : ℝ) (m : ℕ) (μ r b : ℝ)
    (hq : 0 < q) (hqthird : q ≤ 1/3) (hμ : 0 < μ) (hr : 0 < r) (hb : 0 < b) :
    0 < explicitEpsilon q m μ r b ∧
      explicitEpsilon q m μ r b ≤ explicitEta q m μ/10000 ∧
      explicitEpsilon q m μ r b ≤ explicitDelta q/100000 ∧
      explicitEpsilon q m μ r b ≤ b/10^8 ∧
      explicitEpsilon q m μ r b ≤ r*q/10^8 ∧ explicitEpsilon q m μ r b ≤ 1/10^8 := by
  have hδ : 0 < explicitDelta q := (explicitDelta_bounds q hq (by linarith)).1
  have hη : 0 < explicitEta q m μ := (explicitEta_bounds q m μ hq hqthird hμ).1
  unfold explicitEpsilon
  refine ⟨lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))), ?_, ?_, ?_, ?_, ?_⟩
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  · exact (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  · exact (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)

/-- Scalar form of the router's paper budget: `T ≥ 10⁶/b`, `q=1/(2T)`,
and `ε ≤ b/10⁸` make the displayed `25n/k+5εn < bn/4` strict. -/
theorem explicitRouter_fraction_slack (q ε b : ℝ) (hb : 0 < b)
    (hq : q ≤ b/(2*10^6)) (hε : ε ≤ b/10^8) :
    25*q + 5*ε < b/4 := by nlinarith

/-- Translate the actual paper choice of `T` into the reciprocal bound used
in the router ledger. -/
theorem reciprocalRouterBound (q T b : ℝ) (hq : 0 < q) (hb : 0 < b)
    (hT : (10^6 : ℝ)/b ≤ T) (hqT : q*(2*T) = 1) :
    q ≤ b/(2*10^6) := by
  have hTb : (10^6 : ℝ) ≤ b*T := by
    have h := (div_le_iff₀ hb).mp hT
    nlinarith
  have hbound : (2*10^6 : ℝ)*q ≤ b := by
    calc
      (2*10^6 : ℝ)*q = (10^6 : ℝ)*(2*q) := by ring
      _ ≤ (b*T)*(2*q) := mul_le_mul_of_nonneg_right hTb (by positivity)
      _ = b*(q*(2*T)) := by ring
      _ = b := by rw [hqT, mul_one]
  nlinarith

/-- The exact choices `θ=Δ/(10000J)` and `η=min{q/1000,θ/100,q²μ/1000}`
feed the shared-sample theorem. The arbitrary lower bound on even `T` can
include both paper requirements; the router event is still a separate input. -/
theorem exists_explicitSample_and_ordinaryTransitions
    (hAKS : ∃ K D₀ C : ℝ, 0 < K ∧ 0 < C ∧ AKSSetFamilyTheorem.{u} K D₀ C)
    (hPippenger : PippengerTheorem.{u}) (r L : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1/10) :
    ∃ T : ℕ, Even T ∧ L ≤ (T : ℝ) ∧ ∃ m : ℕ, 0 < m ∧ m + 12 = 2*T ∧
      ∃ d : Densities m, d.r = r ∧ 0 < d.q ∧ 100*d.q ≤ d.r ∧
        d.q*((m : ℝ)+12) = 1 ∧ d.q ≤ 1/3 ∧
        ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/2 ∧ ∃ N : ℕ,
          ∀ (G : Type u) [Fintype G] [AddCommGroup G],
            Odd (Fintype.card G) → N ≤ Fintype.card G →
            ∃ s : Sample G m,
              GoodSample d (explicitSizeTolerance (Fintype.card G)) s ∧
                LayerTransitionEvent d (explicitTheta d.q m) (explicitEta d.q m μ) s := by
  obtain ⟨T, hTeven, hTL, m, hm, hk, d, hdr, hq, hqr, hqk, hqthird, ha, hc⟩ :=
    exists_evenExplicitDensities r L hr hrsmall
  have hθ := explicitTheta_bounds d.q m hq hqthird
  obtain ⟨μ, hμ, hμhalf, hsample⟩ := exists_goodSample_and_layeredTransitions
    hAKS hPippenger d (explicitTheta d.q m) hq hqthird hθ.1 hθ.2
  obtain ⟨hη, hηq, hηθ, hημ⟩ := explicitEta_bounds d.q m μ hq hqthird hμ
  obtain ⟨N, hN⟩ := hsample (explicitEta d.q m μ) hη hηq hηθ hημ
  exact ⟨T, hTeven, hTL, m, hm, hk, d, hdr, hq, hqr, hqk, hqthird, μ, hμ, hμhalf, N, hN⟩

end
end EndpointLayeredSample
