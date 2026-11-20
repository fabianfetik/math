import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Lean.Elab.Tactic.Omega

namespace CorralFormalization.OddSeamAssignment

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. -/

/-- The odd height used by the paper's uniform owner assignment. -/
def h (A : ℕ) : ℕ := 2 * A + 3

private theorem evenWrapModZero (A : ℕ) :
    (2 * (2 * A + 1) + 4) % (2 * (2 * A + 3)) = 0 := by
  have heq : 2 * (2 * A + 1) + 4 = 2 * (2 * A + 3) := by omega
  rw [heq, Nat.mod_self]

private theorem evenWrapModTwo (A : ℕ) :
    (2 * (2 * A + 2) + 4) % (2 * (2 * A + 3)) = 2 := by
  have heq : 2 * (2 * A + 2) + 4 = 2 * (2 * A + 3) + 2 := by omega
  have htwo : 2 < 2 * (2 * A + 3) := by omega
  rw [heq, Nat.add_mod]
  simp [Nat.mod_eq_of_lt htwo]

/-- The input permutation obtained by swapping the two specified pairs. -/
def explicitInputSwaps (A : ℕ) : Equiv.Perm (ZMod (h A)) :=
  Equiv.swap ((A - 1 : ℕ) : ZMod (h A)) (A : ZMod (h A)) *
    Equiv.swap ((2 * A + 1 : ℕ) : ZMod (h A)) ((2 * A + 2 : ℕ) : ZMod (h A))

/-- Equation (11): first exchange images at A-1,A and h-2,h-1, then
translate cyclically by A. The group product is composition, so the swaps act
on the input before the translation. -/
def explicitOwner (A : ℕ) : Equiv.Perm (ZMod (h A)) :=
  Equiv.addRight (A : ZMod (h A)) * explicitInputSwaps A

theorem explicitOwner_bijective (A : ℕ) : Function.Bijective (explicitOwner A) :=
  (explicitOwner A).bijective

/-- Equation (11)'s owner map is bijective throughout its stated range. -/
theorem explicitOwner_bijective_of_ge_two (A : ℕ) (_hA : 2 ≤ A) :
    Function.Bijective (explicitOwner A) :=
  explicitOwner_bijective A

/-- A transposition on natural representatives. -/
def natSwap (a b x : ℕ) : ℕ := if x = a then b else if x = b then a else x

/-- The exact two-swap input map on canonical natural representatives. The
right swap acts first, as it does in the permutation product above. -/
def swapIndex (A s : ℕ) : ℕ :=
  natSwap (A - 1) A (natSwap (2 * A + 1) (2 * A + 2) s)

/-- The literal piecewise values printed in equation (11), written with
natural representatives and the inequalities appropriate to 0 ≤ s < h. -/
def printedOwnerValue (A s : ℕ) : ℕ :=
  if s ≤ A - 2 then s + A else
  if s = A - 1 then 2 * A else
  if s = A then 2 * A - 1 else
  if s = A + 1 then 2 * A + 1 else
  if s = A + 2 then 2 * A + 2 else
  if A + 3 ≤ s ∧ s ≤ 2 * A then s - A - 3 else
  if s = 2 * A + 1 then A - 1 else A - 2

def ownerValue (A : ℕ) (s : Fin (h A)) : ℕ :=
  (explicitOwner A (s.val : ZMod (h A))).val

/-- Casting two representatives below the modulus is injective. -/
theorem natCast_eq_iff_of_lt (A x y : ℕ) (hx : x < h A) (hy : y < h A) :
    (x : ZMod (h A)) = (y : ZMod (h A)) ↔ x = y := by
  constructor
  · intro he
    have hv := congrArg ZMod.val he
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hv
  · rintro rfl
    rfl

/-- The two swap points are pairwise distinct when A ≥ 2, so the operation is
precisely the two independent image exchanges described in the paper. -/
theorem swap_points_pairwise_distinct (A : ℕ) (hA : 2 ≤ A) :
    ((A - 1 : ℕ) : ZMod (h A)) ≠ (A : ZMod (h A)) ∧
    ((A - 1 : ℕ) : ZMod (h A)) ≠ ((2 * A + 1 : ℕ) : ZMod (h A)) ∧
    ((A - 1 : ℕ) : ZMod (h A)) ≠ ((2 * A + 2 : ℕ) : ZMod (h A)) ∧
    (A : ZMod (h A)) ≠ ((2 * A + 1 : ℕ) : ZMod (h A)) ∧
    (A : ZMod (h A)) ≠ ((2 * A + 2 : ℕ) : ZMod (h A)) ∧
    ((2 * A + 1 : ℕ) : ZMod (h A)) ≠ ((2 * A + 2 : ℕ) : ZMod (h A)) := by
  have hh : 0 < h A := by simp [h]
  have hAm1 : A - 1 < h A := by dsimp [h]; omega
  have hA_lt : A < h A := by dsimp [h]; omega
  have h1_lt : 2 * A + 1 < h A := by dsimp [h]; omega
  have h2_lt : 2 * A + 2 < h A := by dsimp [h]; omega
  constructor
  · intro he
    have : A - 1 = A := (natCast_eq_iff_of_lt A _ _ hAm1 hA_lt).mp he
    omega
  constructor
  · intro he
    have : A - 1 = 2 * A + 1 := (natCast_eq_iff_of_lt A _ _ hAm1 h1_lt).mp he
    omega
  constructor
  · intro he
    have : A - 1 = 2 * A + 2 := (natCast_eq_iff_of_lt A _ _ hAm1 h2_lt).mp he
    omega
  constructor
  · intro he
    have : A = 2 * A + 1 := (natCast_eq_iff_of_lt A _ _ hA_lt h1_lt).mp he
    omega
  constructor
  · intro he
    have : A = 2 * A + 2 := (natCast_eq_iff_of_lt A _ _ hA_lt h2_lt).mp he
    omega
  · intro he
    have : 2 * A + 1 = 2 * A + 2 := (natCast_eq_iff_of_lt A _ _ h1_lt h2_lt).mp he
    omega

/-- A transposition commutes with passage between natural representatives and
`ZMod`, provided all three representatives lie below the modulus. -/
theorem swap_apply_natSwap (A a b x : ℕ)
    (ha : a < h A) (hb : b < h A) (hx : x < h A) :
    Equiv.swap (a : ZMod (h A)) (b : ZMod (h A)) (x : ZMod (h A)) =
      (natSwap a b x : ZMod (h A)) := by
  have eA := natCast_eq_iff_of_lt A x a hx ha
  have eB := natCast_eq_iff_of_lt A x b hx hb
  simp [natSwap, Equiv.swap_apply_def, eA, eB]

/-- The input swap map agrees with its natural-index description. -/
theorem explicitInputSwaps_apply (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    explicitInputSwaps A (s.val : ZMod (h A)) = (swapIndex A s.val : ZMod (h A)) := by
  have hh : 0 < h A := by dsimp [h]; omega
  have hA1 : A - 1 < h A := by dsimp [h]; omega
  have hA2 : A < h A := by dsimp [h]; omega
  have hP1 : 2 * A + 1 < h A := by dsimp [h]; omega
  have hP2 : 2 * A + 2 < h A := by dsimp [h]; omega
  have hSecond := swap_apply_natSwap A (2 * A + 1) (2 * A + 2) s.val
    hP1 hP2 s.isLt
  have hMid : natSwap (2 * A + 1) (2 * A + 2) s.val < h A := by
    unfold natSwap
    split_ifs <;> omega
  have hFirst := swap_apply_natSwap A (A - 1) A
    (natSwap (2 * A + 1) (2 * A + 2) s.val) hA1 hA2 hMid
  change (Equiv.swap ((A - 1 : ℕ) : ZMod (h A)) (A : ZMod (h A)) *
      Equiv.swap ((2 * A + 1 : ℕ) : ZMod (h A)) ((2 * A + 2 : ℕ) : ZMod (h A)))
      (s.val : ZMod (h A)) = _
  rw [Equiv.Perm.mul_apply, hSecond, hFirst]
  rfl

/-- Equation (11) as a cyclic translation applied after the two input swaps. -/
theorem explicitOwner_apply_eq_add_swapIndex (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    explicitOwner A (s.val : ZMod (h A)) =
      ((swapIndex A s.val + A : ℕ) : ZMod (h A)) := by
  rw [explicitOwner, Equiv.Perm.mul_apply, Equiv.coe_addRight,
    explicitInputSwaps_apply A hA s]
  simp


/-- On canonical indices, the two disjoint transpositions simplify to the
natural input exchange used in the printed piecewise assignment. -/
theorem swapIndex_piecewise (A : ℕ) (hA : 2 ≤ A) (s : ℕ) :
    swapIndex A s =
      if s = A - 1 then A else
      if s = A then A - 1 else
      if s = 2 * A + 1 then 2 * A + 2 else
      if s = 2 * A + 2 then 2 * A + 1 else s := by
  unfold swapIndex natSwap
  split_ifs <;> omega

/-- Reading the ZMod permutation on the representative s gives the usual
remainder of the swapped input plus A. -/
theorem ownerValue_eq_mod (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    ownerValue A s = (swapIndex A s.val + A) % h A := by
  unfold ownerValue
  rw [explicitOwner_apply_eq_add_swapIndex A hA s]
  change ((swapIndex A s.val + A : ℕ) % h A) = _
  rfl

/-- Equation (11) is exactly the cyclic translate and the two image exchanges,
when indexed by the canonical representatives 0,...,h-1. -/
theorem ownerValue_eq_printed (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    ownerValue A s = printedOwnerValue A s.val := by
  rw [ownerValue_eq_mod A hA s]
  have hs := s.isLt
  by_cases hs0 : s.val ≤ A - 2
  · have hsw : swapIndex A s.val = s.val := by
      rw [swapIndex_piecewise A hA s.val]
      split_ifs <;> omega
    rw [hsw]
    rw [Nat.mod_eq_of_lt (by dsimp [h]; omega : s.val + A < h A)]
    unfold printedOwnerValue
    split_ifs <;> omega
  · by_cases hs1 : s.val = A - 1
    · have hsw : swapIndex A s.val = A := by
        rw [swapIndex_piecewise A hA s.val]
        split_ifs <;> omega
      rw [hsw]
      rw [Nat.mod_eq_of_lt (by dsimp [h]; omega : A + A < h A)]
      unfold printedOwnerValue
      split_ifs <;> omega
    · by_cases hs2 : s.val = A
      · have hsw : swapIndex A s.val = A - 1 := by
          rw [swapIndex_piecewise A hA s.val]
          split_ifs <;> omega
        rw [hsw]
        rw [Nat.mod_eq_of_lt (by dsimp [h]; omega : A - 1 + A < h A)]
        unfold printedOwnerValue
        split_ifs <;> omega
      · by_cases hs3 : s.val = A + 1
        · have hsw : swapIndex A s.val = s.val := by
            rw [swapIndex_piecewise A hA s.val]
            split_ifs <;> omega
          rw [hsw, hs3]
          rw [Nat.mod_eq_of_lt (by dsimp [h]; omega : A + 1 + A < h A)]
          unfold printedOwnerValue
          split_ifs <;> omega
        · by_cases hs4 : s.val = A + 2
          · have hsw : swapIndex A s.val = s.val := by
              rw [swapIndex_piecewise A hA s.val]
              split_ifs <;> omega
            rw [hsw, hs4]
            rw [Nat.mod_eq_of_lt (by dsimp [h]; omega : A + 2 + A < h A)]
            unfold printedOwnerValue
            split_ifs <;> omega
          · by_cases hmid : A + 3 ≤ s.val ∧ s.val ≤ 2 * A
            · have hsw : swapIndex A s.val = s.val := by
                rw [swapIndex_piecewise A hA s.val]
                split_ifs <;> omega
              rw [hsw]
              have hmod : (s.val + A) % h A = s.val - A - 3 := by
                rw [Nat.mod_eq_sub_mod (by dsimp [h]; omega)]
                have hsub : s.val + A - h A = s.val - A - 3 := by
                  dsimp [h]
                  omega
                have hlt : s.val - A - 3 < h A := by dsimp [h]; omega
                rw [hsub, Nat.mod_eq_of_lt hlt]
              rw [hmod]
              unfold printedOwnerValue
              split_ifs <;> omega
            · by_cases hs5 : s.val = 2 * A + 1
              · have hsw : swapIndex A s.val = 2 * A + 2 := by
                  rw [swapIndex_piecewise A hA s.val]
                  split_ifs <;> omega
                rw [hsw, hs5]
                have hmod : (2 * A + 2 + A) % h A = A - 1 := by
                  rw [Nat.mod_eq_sub_mod (by dsimp [h]; omega)]
                  have hsub : 2 * A + 2 + A - h A = A - 1 := by
                    dsimp [h]
                    omega
                  have hlt : A - 1 < h A := by dsimp [h]; omega
                  rw [hsub, Nat.mod_eq_of_lt hlt]
                rw [hmod]
                unfold printedOwnerValue
                split_ifs <;> omega
              · have hs6 : s.val = 2 * A + 2 := by
                  dsimp [h] at hs
                  omega
                have hsw : swapIndex A s.val = 2 * A + 1 := by
                  rw [swapIndex_piecewise A hA s.val]
                  split_ifs <;> omega
                rw [hsw, hs6]
                have hmod : (2 * A + 1 + A) % h A = A - 2 := by
                  rw [Nat.mod_eq_sub_mod (by dsimp [h]; omega)]
                  have hsub : 2 * A + 1 + A - h A = A - 2 := by
                    dsimp [h]
                    omega
                  have hlt : A - 2 < h A := by dsimp [h]; omega
                  rw [hsub, Nat.mod_eq_of_lt hlt]
                rw [hmod]
                unfold printedOwnerValue
                split_ifs <;> omega


/-- The two points in the small factor D_t from equation (7). -/
def dFirst (A t : ℕ) : ℕ := 2 * t + 1

def dSecond (A t : ℕ) : ℕ := (2 * t + 4) % (2 * h A)

def dHead (A : ℕ) (t : Fin (h A)) : ℕ := min (dFirst A t.val) (dSecond A t.val)

def dTail (A : ℕ) (t : Fin (h A)) : ℕ :=
  2 * h A - max (dFirst A t.val) (dSecond A t.val)

/-- The head and tail formulas in equation (8) follow by sorting the two
explicit points of D_t, including the two wrap cases. -/
theorem dHead_eq_endpoint_formula (A : ℕ) (t : Fin (h A)) :
    dHead A t =
      if t.val ≤ h A - 3 then 2 * t.val + 1
      else if t.val = h A - 2 then 0 else 2 := by
  simp [h]
  have ht : t.val < 2 * A + 3 := by simpa [h] using t.isLt
  by_cases ht0 : t.val ≤ 2 * A
  · have hsecond : 2 * t.val + 4 < 2 * (2 * A + 3) := by omega
    have hfirstle : 2 * t.val + 1 ≤ 2 * t.val + 4 := by omega
    simp [dHead, dFirst, dSecond, h, ht0, Nat.mod_eq_of_lt hsecond,
      Nat.min_eq_left hfirstle]
  · by_cases ht1 : t.val = 2 * A + 1
    · have htFin : t = (⟨2 * A + 1, by simp [h]⟩ : Fin (h A)) :=
        Fin.ext ht1
      subst t
      simp [dHead, dFirst, dSecond, h, evenWrapModZero]
    · have ht2 : t.val = 2 * A + 2 := by omega
      have htFin : t = (⟨2 * A + 2, by simp [h]⟩ : Fin (h A)) :=
        Fin.ext ht2
      subst t
      have hmin : 2 ≤ 2 * (2 * A + 2) + 1 := by omega
      simp [dHead, dFirst, dSecond, h, evenWrapModTwo, Nat.min_eq_right hmin]

/-- Tail-deficit half of equation (8), using the paper's convention
`2h - max(D_t)` rather than `2h - 1 - max(D_t)`. -/
theorem dTail_eq_endpoint_formula (A : ℕ) (t : Fin (h A)) :
    dTail A t =
      if t.val ≤ h A - 3 then 2 * h A - 2 * t.val - 4
      else if t.val = h A - 2 then 3 else 1 := by
  simp [h]
  have ht : t.val < 2 * A + 3 := by simpa [h] using t.isLt
  by_cases ht0 : t.val ≤ 2 * A
  · have hsecond : 2 * t.val + 4 < 2 * (2 * A + 3) := by omega
    have hfirstle : 2 * t.val + 1 ≤ 2 * t.val + 4 := by omega
    simp [dTail, dFirst, dSecond, h, ht0, Nat.mod_eq_of_lt hsecond,
      Nat.max_eq_right hfirstle]
    omega
  · by_cases ht1 : t.val = 2 * A + 1
    · have htFin : t = (⟨2 * A + 1, by simp [h]⟩ : Fin (h A)) :=
        Fin.ext ht1
      subst t
      simp [dTail, dFirst, dSecond, h, evenWrapModZero]
      omega
    · have ht2 : t.val = 2 * A + 2 := by omega
      have htFin : t = (⟨2 * A + 2, by simp [h]⟩ : Fin (h A)) :=
        Fin.ext ht2
      subst t
      have hmax : 2 ≤ 2 * (2 * A + 2) + 1 := by omega
      simp [dTail, dFirst, dSecond, h, evenWrapModTwo, Nat.max_eq_left hmax]
      omega

/-- The tail rows of the endpoint table in §4.3, as a function of the
original owner index s. -/
def explicitTailEndpoint (A s : ℕ) : ℕ :=
  if s ≤ A - 2 then 2 * A + 2 - 2 * s else
  if s = A - 1 then 2 else
  if s = A + 1 then 3 else
  if s = A + 2 then 1 else
  if s = 2 * A + 1 then 2 * A + 4 else
  if s = 2 * A + 2 then 2 * A + 6 else 0

/-- The head rows of the endpoint table in §4.3. -/
def explicitHeadEndpoint (A s : ℕ) : ℕ :=
  if s = A then 4 * A - 1 else
  if A + 3 ≤ s ∧ s ≤ 2 * A then 2 * s - 2 * A - 5 else 0

/-- The rows for which §4.3 supplies a tail deficit rather than a first point. -/
def explicitUsesTail (A s : ℕ) : Prop :=
  s ≤ A - 1 ∨ s = A + 1 ∨ s = A + 2 ∨ s = 2 * A + 1 ∨ s = 2 * A + 2

instance (A s : ℕ) : Decidable (explicitUsesTail A s) := by
  unfold explicitUsesTail
  infer_instance

def explicitHeadValueFormula (A t : ℕ) : ℕ :=
  if t ≤ h A - 3 then 2 * t + 1 else if t = h A - 2 then 0 else 2

def explicitTailValueFormula (A t : ℕ) : ℕ :=
  if t ≤ h A - 3 then 2 * h A - 2 * t - 4
  else if t = h A - 2 then 3 else 1

theorem ownerValue_lt (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    ownerValue A s < h A := by
  rw [ownerValue_eq_printed A hA s]
  have hs := s.isLt
  unfold printedOwnerValue
  simp [h] at hs ⊢
  split_ifs <;> omega

/-- The representative in ZMod corresponding to pi(s). -/
def explicitOwnerIndex (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) : Fin (h A) :=
  ⟨ownerValue A s, ownerValue_lt A hA s⟩

@[simp] theorem explicitOwnerIndex_val (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    (explicitOwnerIndex A hA s).val = ownerValue A s := rfl

/-- The same index computed directly from the printed piecewise formula. -/
def explicitPrintedIndex (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) : Fin (h A) :=
  ⟨printedOwnerValue A s.val, by
    rw [← ownerValue_eq_printed A hA s]
    exact ownerValue_lt A hA s⟩

@[simp] theorem explicitPrintedIndex_val (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (h A)) :
    (explicitPrintedIndex A hA s).val = printedOwnerValue A s.val := rfl

theorem explicitOwnerIndex_eq_printed (A : ℕ) (hA : 2 ≤ A)
    (s : Fin (h A)) :
    explicitOwnerIndex A hA s = explicitPrintedIndex A hA s := by
  apply Fin.ext
  exact ownerValue_eq_printed A hA s

/-- Pure natural-number verification that equation (11)'s displayed values
send each owner to the endpoint listed in §4.3, when evaluated by (8). -/
theorem printedEndpointTableMatch (A s : ℕ) (hA : 2 ≤ A) (hs : s < h A) :
    if explicitUsesTail A s then
      explicitTailEndpoint A s = explicitTailValueFormula A (printedOwnerValue A s)
    else
      explicitHeadEndpoint A s = explicitHeadValueFormula A (printedOwnerValue A s) := by
  classical
  change s < 2 * A + 3 at hs
  by_cases hs0 : s ≤ A - 2
  · simp [explicitUsesTail, explicitTailEndpoint, explicitHeadEndpoint,
      explicitTailValueFormula, explicitHeadValueFormula, printedOwnerValue, h, hs0] <;>
      split_ifs <;> omega
  · by_cases hs1 : s = A - 1
    · simp [explicitUsesTail, explicitTailEndpoint, explicitHeadEndpoint,
        explicitTailValueFormula, explicitHeadValueFormula, printedOwnerValue, h, hs0, hs1] <;>
        split_ifs <;> omega
    · by_cases hs2 : s = A
      · simp [explicitUsesTail, explicitTailEndpoint, explicitHeadEndpoint,
          explicitTailValueFormula, explicitHeadValueFormula, printedOwnerValue, h,
          hs0, hs1, hs2] <;> split_ifs <;> omega
      · by_cases hs3 : s = A + 1
        · simp [explicitUsesTail, explicitTailEndpoint, explicitHeadEndpoint,
            explicitTailValueFormula, explicitHeadValueFormula, printedOwnerValue, h,
            hs0, hs1, hs2, hs3] <;> split_ifs <;> omega
        · by_cases hs4 : s = A + 2
          · simp [explicitUsesTail, explicitTailEndpoint, explicitHeadEndpoint,
              explicitTailValueFormula, explicitHeadValueFormula, printedOwnerValue, h,
              hs0, hs1, hs2, hs3, hs4] <;> split_ifs <;> omega
          · by_cases hmid : A + 3 ≤ s ∧ s ≤ 2 * A
            · simp [explicitUsesTail, explicitTailEndpoint, explicitHeadEndpoint,
                explicitTailValueFormula, explicitHeadValueFormula, printedOwnerValue, h,
                hs0, hs1, hs2, hs3, hs4, hmid] <;> split_ifs <;> omega
            · by_cases hs5 : s = 2 * A + 1
              · simp [explicitUsesTail, explicitTailEndpoint, explicitHeadEndpoint,
                  explicitTailValueFormula, explicitHeadValueFormula, printedOwnerValue, h,
                  hs0, hs1, hs2, hs3, hs4, hmid, hs5] <;> split_ifs <;> omega
              · have hs6 : s = 2 * A + 2 := by omega
                simp [explicitUsesTail, explicitTailEndpoint, explicitHeadEndpoint,
                  explicitTailValueFormula, explicitHeadValueFormula, printedOwnerValue, h,
                  hs0, hs1, hs2, hs3, hs4, hmid, hs5, hs6] <;>
                  split_ifs <;> omega

/-- Equation (11), followed by equation (8), gives each numerical endpoint
listed in the §4.3 table. This is the concrete arithmetic verification of the
table's stated values against the actual assigned index. -/
theorem explicitPrintedEndpointMatch (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    if explicitUsesTail A s.val then
      explicitTailEndpoint A s.val = dTail A (explicitPrintedIndex A hA s)
    else
      explicitHeadEndpoint A s.val = dHead A (explicitPrintedIndex A hA s) := by
  classical
  have htable := printedEndpointTableMatch A s.val hA s.isLt
  by_cases hu : explicitUsesTail A s.val
  · simp only [if_pos hu] at htable ⊢
    have hd : dTail A (explicitPrintedIndex A hA s) =
        explicitTailValueFormula A (printedOwnerValue A s.val) := by
      have hd0 := dTail_eq_endpoint_formula A (explicitPrintedIndex A hA s)
      change dTail A (explicitPrintedIndex A hA s) =
        explicitTailValueFormula A (printedOwnerValue A s.val) at hd0
      exact hd0
    exact htable.trans hd.symm
  · simp only [if_neg hu] at htable ⊢
    have hd : dHead A (explicitPrintedIndex A hA s) =
        explicitHeadValueFormula A (printedOwnerValue A s.val) := by
      have hd0 := dHead_eq_endpoint_formula A (explicitPrintedIndex A hA s)
      change dHead A (explicitPrintedIndex A hA s) =
        explicitHeadValueFormula A (printedOwnerValue A s.val) at hd0
      exact hd0
    exact htable.trans hd.symm

/-- Transfer the printed endpoint calculation to the permutation itself. -/
theorem explicitOwnerEndpointMatch (A : ℕ) (hA : 2 ≤ A) (s : Fin (h A)) :
    if explicitUsesTail A s.val then
      explicitTailEndpoint A s.val = dTail A (explicitOwnerIndex A hA s)
    else
      explicitHeadEndpoint A s.val = dHead A (explicitOwnerIndex A hA s) := by
  rw [explicitOwnerIndex_eq_printed]
  exact explicitPrintedEndpointMatch A hA s

/-- Transfer an explicitly supplied §4.3 endpoint table to the matching
equations required by Lemma 4. The remaining paper-specific obligation is to
prove the table hypotheses from (9)--(10); that requires showing every bucket
is nonempty before taking its minimum and maximum. -/
theorem endpointMatch_of_table (A : ℕ) (hA : 2 ≤ A)
    (fC tC : Fin (h A) → ℕ)
    (hTail : ∀ s, explicitUsesTail A s.val →
      tC s = explicitTailEndpoint A s.val)
    (hHead : ∀ s, ¬ explicitUsesTail A s.val →
      fC s = explicitHeadEndpoint A s.val)
    (s : Fin (h A)) :
    if explicitUsesTail A s.val then
      tC s = dTail A (explicitOwnerIndex A hA s)
    else
      fC s = dHead A (explicitOwnerIndex A hA s) := by
  classical
  by_cases hu : explicitUsesTail A s.val
  · simp only [if_pos hu]
    calc
      tC s = explicitTailEndpoint A s.val := hTail s hu
      _ = dTail A (explicitOwnerIndex A hA s) := by
        simpa [hu] using explicitOwnerEndpointMatch A hA s
  · simp only [if_neg hu]
    calc
      fC s = explicitHeadEndpoint A s.val := hHead s hu
      _ = dHead A (explicitOwnerIndex A hA s) := by
        simpa [hu] using explicitOwnerEndpointMatch A hA s

end CorralFormalization.OddSeamAssignment

#print axioms CorralFormalization.OddSeamAssignment.explicitOwner_bijective
#print axioms CorralFormalization.OddSeamAssignment.ownerValue_eq_printed
#print axioms CorralFormalization.OddSeamAssignment.dHead_eq_endpoint_formula
#print axioms CorralFormalization.OddSeamAssignment.dTail_eq_endpoint_formula
#print axioms CorralFormalization.OddSeamAssignment.explicitOwnerEndpointMatch
#print axioms CorralFormalization.OddSeamAssignment.endpointMatch_of_table
