import CorralFormalization.EndpointProof.Factor.Allocation.GenericLayers
import CorralFormalization.EndpointProof.Factor.Allocation.BankBounds

/-!
# Ordinary colour pools and the closing bank

All actual raw ordinary colour roles and the closing bank are protected at
once. Router colours are taken from the separate reserve role; the closing
bank may be smaller than its raw sample, so its retention is capped.
-/

open scoped BigOperators Classical symmDiff
namespace EndpointFactor.Allocation
open EndpointLayeredSample EndpointRouter
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G] {m : ℕ}

def explicitColourRole {m : ℕ} : Fin (m+2) → ColourRole m :=
  Fin.lastCases (specialColour m) (fun i : Fin (m+1) => Sum.inr i)

theorem explicitColourRole_injective : Function.Injective (@explicitColourRole m) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j => simp [explicitColourRole, specialColour] at hij
  | cast i =>
      induction j using Fin.lastCases with
      | last => simp [explicitColourRole, specialColour] at hij
      | cast j =>
          simp only [explicitColourRole, Fin.lastCases_castSucc, Sum.inr.injEq] at hij
          exact congrArg Fin.castSucc hij

theorem explicitColourRole_ne_reserve (i : Fin (m+2)) :
    explicitColourRole i ≠ reserveColour m := by
  induction i using Fin.lastCases with
  | last => simp [explicitColourRole, specialColour, reserveColour]
  | cast i => simp [explicitColourRole, reserveColour]

def explicitColourCapacity (ℓ w K : ℕ) : Fin (m+2) → ℕ :=
  Fin.lastCases (ℓ+w-K) (fun _ : Fin (m+1) => ℓ)

theorem explicitColourCapacity_sum (ℓ w K : ℕ) :
    (∑ i, @explicitColourCapacity m ℓ w K i) = (m+1)*ℓ + (ℓ+w-K) := by
  rw [Fin.sum_univ_castSucc]
  simp [explicitColourCapacity, nsmul_eq_mul]

/-- The colours remaining after the actual 10ℓ-colour router pay all
ordinary pools and the closing bank exactly. -/
theorem colour_room (sample : AugmentedSample G m) (special : Fin 3 → Finset G)
    (W D : Finset G) (ℓ w K : ℕ) (router : PhysicalRouter sample special W D ℓ)
    (hW : W.card = (m+12)*ℓ+w) (hD : D.card+K = W.card) (hK : K ≤ ℓ) :
    (D \ fixedColorFinset router.first router.second).card =
      (m+1)*ℓ + (ℓ+w-K) := by
  have hsplit := Finset.card_sdiff_add_card_eq_card router.color_in_target
  have hcolor := router.color_card
  have hexpand : (m+12)*ℓ = (m+1)*ℓ + 11*ℓ := by ring
  rw [hexpand] at hW
  omega

theorem raw_colour_disjoint_router (sample : AugmentedSample G m)
    (special : Fin 3 → Finset G) (W D : Finset G) (ℓ : ℕ)
    (router : PhysicalRouter sample special W D ℓ) (i : Fin (m+2)) :
    Disjoint (colourSet (forgetAugmented sample) (explicitColourRole i))
      (fixedColorFinset router.first router.second) := by
  have hraw : Disjoint (colourSet (forgetAugmented sample) (explicitColourRole i))
      (colourSet (forgetAugmented sample) (reserveColour m)) :=
    colourSet_disjoint _ (explicitColourRole_ne_reserve i)
  exact hraw.mono_right router.color_in_reserve

theorem raw_colour_inter_available (sample : AugmentedSample G m)
    (special : Fin 3 → Finset G) (W D : Finset G) (ℓ : ℕ)
    (router : PhysicalRouter sample special W D ℓ) (i : Fin (m+2)) :
    colourSet (forgetAugmented sample) (explicitColourRole i) ∩
        (D \ fixedColorFinset router.first router.second) =
      colourSet (forgetAugmented sample) (explicitColourRole i) ∩ D := by
  ext x
  have hdisj := raw_colour_disjoint_router sample special W D ℓ router i
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · tauto
  · rintro ⟨hr, hd⟩
    exact ⟨hr, hd, fun hx => Finset.disjoint_left.mp hdisj hr hx⟩

/-- Actual ordinary pools and closing bank constructed simultaneously from
the same sample and the physical router's actual unused colours. -/
theorem exists_explicit_colour_pools
    (dist : Densities m) (sample : AugmentedSample G m)
    (special : Fin 3 → Finset G) (W D : Finset G) (ℓ w K d : ℕ)
    (router : PhysicalRouter sample special W D ℓ) (tolerance : ℝ)
    (hsize : SizeEvent dist tolerance (forgetAugmented sample))
    (htol : 0 ≤ tolerance)
    (hW : W.card = (m+12)*ℓ+w) (hD : D.card+K = W.card)
    (hdiv : (m+12)*ℓ+d = Fintype.card G) (hK : K ≤ ℓ)
    (hℓ : (ℓ : ℝ) = dist.q * Fintype.card G - dist.q*d)
    (hfit : dist.c * Fintype.card G+tolerance ≤ (ℓ : ℝ)) :
    ∃ chosen : Fin (m+2) → Finset G,
      (∀ i, chosen i ⊆ D \ fixedColorFinset router.first router.second ∧
        (chosen i).card = explicitColourCapacity ℓ w K i) ∧
      (∀ i j, i ≠ j → Disjoint (chosen i) (chosen j)) ∧
      Finset.univ.biUnion chosen = D \ fixedColorFinset router.first router.second ∧
      (∀ i : Fin (m+1),
        (colourSet (forgetAugmented sample) (Sum.inr i) \ chosen i.castSucc).card ≤ d+K) ∧
      ((colourSet (forgetAugmented sample) (specialColour m) \
          chosen (Fin.last (m+1))).card : ℝ) ≤ d+tolerance+K ∧
      ((colourSet (forgetAugmented sample) (specialColour m) ∆
          chosen (Fin.last (m+1))).card : ℝ) ≤ (2+dist.q)*d+tolerance+K := by
  let U := D \ fixedColorFinset router.first router.second
  let raw (i : Fin (m+2)) := colourSet (forgetAugmented sample) (explicitColourRole i)
  let cap : Fin (m+2) → ℕ := explicitColourCapacity ℓ w K
  have hroles : Function.Injective (@explicitColourRole m) := explicitColourRole_injective
  have hrawdisj : ∀ i j, i ≠ j → Disjoint (raw i) (raw j) := by
    intro i j hij
    exact colourSet_disjoint _ (fun heq => hij (hroles heq))
  have hUcard : U.card = (m+1)*ℓ + (ℓ+w-K) := colour_room sample special W D ℓ w K router hW hD hK
  have hcapsum : (∑ i, cap i) = U.card := by
    rw [show (∑ i, cap i) = (m+1)*ℓ + (ℓ+w-K) from explicitColourCapacity_sum ℓ w K]
    exact hUcard.symm
  obtain ⟨chosen, hchosen, hpair, hleft⟩ :=
    exists_capped_raw_allocation (m+2) U raw cap hrawdisj hcapsum.le
  have hcomplete : Finset.univ.biUnion chosen = U := by
    have hsub : Finset.univ.biUnion chosen ⊆ U := by
      intro x hx
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      exact (hchosen i).1 hi
    have hzero : (U \ Finset.univ.biUnion chosen).card = 0 := by omega
    apply Finset.Subset.antisymm hsub
    intro x hx
    by_contra hnot
    have hx' : x ∈ U \ Finset.univ.biUnion chosen := Finset.mem_sdiff.mpr ⟨hx, hnot⟩
    have : U \ Finset.univ.biUnion chosen = ∅ := Finset.card_eq_zero.mp hzero
    simp [this] at hx'
  have hmissD : ((Finset.univ : Finset G) \ D).card + w = d+K := by
    have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
    simp only [Finset.card_univ] at hsplit
    omega
  have hq1 : dist.q ≤ 1 := by have := dist.q_le_half; linarith
  have hordfit (i : Fin (m+1)) :
      (colourSet (forgetAugmented sample) (Sum.inr i)).card ≤ ℓ := by
    have hi := hsize.2 (Sum.inr i)
    have hi' : |((colourSet (forgetAugmented sample) (Sum.inr i)).card : ℝ) -
        dist.c * Fintype.card G| ≤ tolerance := by
      simpa [colourWeight, mul_comm] using hi
    have hreal : ((colourSet (forgetAugmented sample) (Sum.inr i)).card : ℝ) ≤ ℓ := by
      have h := (abs_le.mp hi').2
      linarith
    exact_mod_cast hreal
  have hord (i : Fin (m+1)) :
      (colourSet (forgetAugmented sample) (Sum.inr i) \ chosen i.castSucc).card ≤ d+K := by
    have hinter : (raw i.castSucc ∩ chosen i.castSucc).card =
        min (raw i.castSucc ∩ U).card (cap i.castSucc) := (hchosen i.castSucc).2.2.1
    have hcap : cap i.castSucc = ℓ := by simp [cap, explicitColourCapacity]
    have hfit' : (raw i.castSucc ∩ U).card ≤ cap i.castSucc := by
      rw [hcap]
      have hc := Finset.card_le_card (Finset.inter_subset_left : raw i.castSucc ∩ U ⊆ raw i.castSucc)
      have hr : (raw i.castSucc).card ≤ ℓ := by simpa [raw, explicitColourRole] using hordfit i
      omega
    have hretain := capped_allocation_retains_fitting (raw i.castSucc) U (chosen i.castSucc)
      (cap i.castSucc) (hchosen i.castSucc).1 hinter hfit'
    have hretainD : colourSet (forgetAugmented sample) (Sum.inr i) ∩ D ⊆ chosen i.castSucc := by
      have heq := raw_colour_inter_available sample special W D ℓ router i.castSucc
      have heq' : raw i.castSucc ∩ U = raw i.castSucc ∩ D := by simpa [raw, U] using heq
      rw [heq'] at hretain
      simpa [raw, explicitColourRole] using hretain
    have hsub : colourSet (forgetAugmented sample) (Sum.inr i) \ chosen i.castSucc ⊆
        (Finset.univ : Finset G) \ D := by
      intro x hx
      obtain ⟨hxraw, hxnot⟩ := Finset.mem_sdiff.mp hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hxD
      exact hxnot (hretainD (Finset.mem_inter.mpr ⟨hxraw, hxD⟩))
    have hc := Finset.card_le_card hsub
    omega
  let bankIndex : Fin (m+2) := Fin.last (m+1)
  let bank := chosen bankIndex
  let Cstar := colourSet (forgetAugmented sample) (specialColour m)
  have hbankraw : raw bankIndex = Cstar := by simp [raw, bankIndex, Cstar, explicitColourRole]
  have hbankcap : cap bankIndex = ℓ+w-K := by simp [cap, bankIndex, explicitColourCapacity]
  have hinter : (Cstar ∩ bank).card = min (Cstar ∩ D).card (ℓ+w-K) := by
    have hi := (hchosen bankIndex).2.2.1
    have heq := raw_colour_inter_available sample special W D ℓ router bankIndex
    have heq' : raw bankIndex ∩ U = raw bankIndex ∩ D := by simpa [raw, U] using heq
    rw [heq'] at hi
    simpa [bank, hbankraw, hbankcap] using hi
  have hbankD : bank ⊆ D := (hchosen bankIndex).1.trans Finset.sdiff_subset
  have hbankcard : bank.card = ℓ+w-K := by simpa [bank, hbankcap] using (hchosen bankIndex).2.1
  have hCstar : |(Cstar.card : ℝ) - dist.q * Fintype.card G| ≤ tolerance := by
    have h := hsize.2 (specialColour m)
    simpa [Cstar, specialColour, colourWeight, mul_comm] using h
  have hbankcapReal : ((ℓ+w-K : ℕ) : ℝ) = (ℓ : ℝ)+w-K := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hcapacity : ((ℓ+w-K : ℕ) : ℝ) =
      dist.q * Fintype.card G - dist.q*d + w-K := by linarith
  have hmissstar : ((Cstar \ D).card : ℝ) ≤ (d : ℝ)-w+K := by
    have hsub : Cstar \ D ⊆ (Finset.univ : Finset G) \ D := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
    have hc := Finset.card_le_card hsub
    have hc' : ((Cstar \ D).card : ℝ) ≤ (((Finset.univ : Finset G) \ D).card : ℝ) := by
      exact_mod_cast hc
    have hmissD' : ((((Finset.univ : Finset G) \ D).card : ℝ) + w) = d+K := by
      exact_mod_cast hmissD
    linarith
  have hbounds := capped_bank_explicit_bounds Cstar D bank (ℓ+w-K)
    dist.q (Fintype.card G) d tolerance w K dist.q_nonneg hq1 (Nat.cast_nonneg _)
    htol (Nat.cast_nonneg _) hbankD hbankcard hinter hCstar hcapacity hmissstar
  refine ⟨chosen, ?_, hpair, hcomplete, hord, ?_, ?_⟩
  · intro i
    exact ⟨(hchosen i).1, (hchosen i).2.1⟩
  · exact hbounds.1
  · exact hbounds.2

end
end EndpointFactor.Allocation
