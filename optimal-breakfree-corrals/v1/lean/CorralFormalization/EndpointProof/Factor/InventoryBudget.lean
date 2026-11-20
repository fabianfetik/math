import CorralFormalization.EndpointProof.Factor.ClosingMatching
import Mathlib.Data.Finset.SymmDiff

/-!
# End-inventory and numerical edit accounting

These lemmas pay the finite symmetric-difference identity and the displayed
numerical slack used at the final exact-matching call. They do not construct the
fragment joins or assert the underlying edit inequality.
-/

open scoped symmDiff
namespace EndpointFactor.InventoryBudget

variable {G : Type*} [DecidableEq G]

/-- Removing actual old points and adding points outside the old set gives
exactly the two symmetric-difference pieces. -/
theorem symmDiff_remove_add (base removed added : Finset G)
    (hremove : removed ⊆ base) (hadd : Disjoint base added) :
    ((base \ removed) ∪ added) ∆ base = removed ∪ added := by
  ext x
  have hr : x ∈ removed → x ∈ base := fun hx => hremove hx
  have hd : x ∈ base → x ∈ added → False := fun hb ha =>
    Finset.disjoint_left.mp hadd hb ha
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- This is the finite identity underlying both the endpoint and colour
inventory changes in the fragment-joining step. -/
theorem symmDiff_remove_add_card (base removed added : Finset G)
    (hremove : removed ⊆ base) (hadd : Disjoint base added) :
    (((base \ removed) ∪ added) ∆ base).card = removed.card + added.card := by
  rw [symmDiff_remove_add base removed added hremove hadd, Finset.card_union_of_disjoint]
  exact hadd.mono_left hremove

/-- The exact expansion of the paper's special-layer and final-bank ledger. -/
theorem finalEdit_expression (q d s K h w : ℝ) :
    2 * ((2 + q)*d + s + 4*K) + (2 + q)*d + s + 3*K + 4*h + 3*w =
      (6 + 3*q)*d + 3*s + 11*K + 4*h + 3*w := by ring

/-- The explicit bounds pay the final closing-radius inequality, once
the separate geometric argument has established the displayed edit bound. -/
theorem finalEdit_budget (q Δ ε n d s K h w : ℝ)
    (hq : q ≤ 1/3) (hd0 : 0 ≤ d) (hd : d ≤ 2*ε*n)
    (hs : s ≤ ε*n) (hK : K ≤ ε*n) (hw : w ≤ ε*n)
    (hε : 0 < ε) (hεΔ : ε ≤ Δ/100000) (hn : 0 < n)
    (hh : h ≤ Δ*n/10000) :
    (6 + 3*q)*d + 3*s + 11*K + 4*h + 3*w < Δ*n := by
  have hqd : (6 + 3*q)*d ≤ 7*d := by
    have hmul := mul_nonneg (sub_nonneg.mpr hq) hd0
    nlinarith
  have heps : ε*n ≤ Δ*n/100000 := by
    have hmul := mul_le_mul_of_nonneg_right hεΔ hn.le
    nlinarith
  have hΔ : 0 < Δ*n := mul_pos (by linarith) hn
  nlinarith

end EndpointFactor.InventoryBudget
