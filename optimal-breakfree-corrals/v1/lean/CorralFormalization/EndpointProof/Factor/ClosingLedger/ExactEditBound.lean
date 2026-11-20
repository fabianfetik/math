import CorralFormalization.EndpointProof.Factor.ClosingLedger.Finite

/-! # The actual exact-matching edit ledger and its final numerical budget -/
open scoped Classical symmDiff
namespace EndpointFactor.ClosingLedger
open EndpointMatching.AbsorptionAssembly
variable {G : Type*}

/-- The closing edit bound, derived from the sampled sets, terminal sizes, and the separately
proved special-layer/end/bank inventory estimates. -/
theorem closing_edit_bound
    (rawLast rawFirst rawC specialLast specialFirst ends H₀ Hf X Y : Finset G)
    (q d s : ℝ) (K h w : ℕ)
    (hXcard : X.card = K) (hYcard : Y.card = K)
    (hlast : ((rawLast ∆ specialLast).card : ℝ) ≤ (2+q)*d+s+4*K)
    (hfirst : ((rawFirst ∆ specialFirst).card : ℝ) ≤ (2+q)*d+s+4*K)
    (hends : (ends ∆ specialLast).card = 2*(h+w))
    (hrawbank : ((rawC ∆ H₀).card : ℝ) ≤ (2+q)*d+s+K)
    (hbank : (Hf ∆ H₀).card = 2*h+w) :
    (physicalEditDistance rawLast rawFirst rawC (ends \ Y) (specialFirst \ X) Hf : ℝ) ≤
      (6+3*q)*d+3*s+11*K+4*h+3*w := by
  have hn := closing_edit_triangle rawLast rawFirst rawC specialLast specialFirst ends H₀ Hf X Y
  rw [hends,hbank,hXcard,hYcard] at hn
  have hr : (physicalEditDistance rawLast rawFirst rawC (ends \ Y) (specialFirst \ X) Hf : ℝ) ≤
      ((rawLast ∆ specialLast).card : ℝ) + 2*((h : ℝ)+w) + K +
      ((rawFirst ∆ specialFirst).card : ℝ) + K + ((rawC ∆ H₀).card : ℝ) + (2*(h : ℝ)+w) := by
    exact_mod_cast hn
  nlinarith

/-- The actual target is inside the exact-matching radius. The conclusion is strict,
and hence supplies the non-strict radius premise used by the uniform exact-matching theorem. -/
theorem closing_edit_budget
    (rawLast rawFirst rawC specialLast specialFirst ends H₀ Hf X Y : Finset G)
    (q Δ ε N d s : ℝ) (K h w : ℕ)
    (hXcard : X.card = K) (hYcard : Y.card = K)
    (hlast : ((rawLast ∆ specialLast).card : ℝ) ≤ (2+q)*d+s+4*K)
    (hfirst : ((rawFirst ∆ specialFirst).card : ℝ) ≤ (2+q)*d+s+4*K)
    (hends : (ends ∆ specialLast).card = 2*(h+w))
    (hrawbank : ((rawC ∆ H₀).card : ℝ) ≤ (2+q)*d+s+K)
    (hbank : (Hf ∆ H₀).card = 2*h+w)
    (hq : q ≤ 1/3) (hd0 : 0 ≤ d) (hd : d ≤ 2*ε*N)
    (hs : s ≤ ε*N) (hK : (K : ℝ) ≤ ε*N) (hw : (w : ℝ) ≤ ε*N)
    (hε : 0 < ε) (hεΔ : ε ≤ Δ/100000) (hN : 0 < N)
    (hh : (h : ℝ) ≤ Δ*N/10000) :
    (physicalEditDistance rawLast rawFirst rawC (ends \ Y) (specialFirst \ X) Hf : ℝ) < Δ*N := by
  exact (closing_edit_bound rawLast rawFirst rawC specialLast specialFirst ends H₀ Hf X Y
    q d s K h w hXcard hYcard hlast hfirst hends hrawbank hbank).trans_lt
      (InventoryBudget.finalEdit_budget q Δ ε N d s K h w
        hq hd0 hd hs hK hw hε hεΔ hN hh)

end EndpointFactor.ClosingLedger
