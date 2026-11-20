import CorralFormalization.DiversityCompletion.LatinConnectorPrefix

/-! Literal connector-prefix vertices and their internal colours, before connectors or
terrace completion. No path simplicity or rainbow premise is assumed. -/

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix

open LatinTransfer TerraceLift LatinPrefix

variable {r : ℕ} [NeZero r]

def P (i : Cell r) : ℕ := predecessor i.1 i.2
def C (i : Cell r) : ℕ := centerBase i.2 + canonicalSymbol i
def N (i : Cell r) : ℕ := successor i.1 i.2
def incoming (i : Cell r) : ℕ := cellA i + canonicalSymbol i
def outgoing (i : Cell r) : ℕ := cellB i - canonicalSymbol i

theorem symbol_lt (i : Cell r) : canonicalSymbol i < r :=
  ((cyclicLatinSquare r).entry i.1 i.2).isLt

theorem incomingBase_le_centerBase (hr : 2 ≤ r) (j u : Fin r) :
    incomingBase j ≤ centerBase u := by
  have hj := Nat.mul_lt_mul_of_pos_left j.isLt (by omega : 0 < r)
  dsimp [incomingBase, centerBase]
  nlinarith

theorem P_add_base (hr : 2 ≤ r) (i : Cell r) :
    P i + incomingBase i.1 = centerBase i.2 :=
  Nat.sub_add_cancel (incomingBase_le_centerBase hr i.1 i.2)

theorem base_mod (j : Fin r) : incomingBase j % r = 0 ∧ outgoingBase j % r = 0 := by
  simp [incomingBase, outgoingBase, Nat.add_mod, Nat.mul_mod]

theorem centerBase_mod (u : Fin r) : centerBase u % r = u.val := by
  have he : centerBase u = r*(20*r+u.val)+u.val := by unfold centerBase; ring
  rw [he]
  simp [Nat.add_mod, Nat.mod_eq_of_lt u.isLt]

theorem P_mod (hr : 2 ≤ r) (i : Cell r) : P i % r = i.2.val := by
  have h := congrArg (fun x => x % r) (P_add_base hr i)
  simpa only [Nat.add_mod, (base_mod i.1).1, Nat.add_zero, Nat.mod_mod, centerBase_mod] using h

theorem N_mod (i : Cell r) : N i % r = i.2.val := by
  simp only [N, successor, Nat.add_mod, (base_mod i.1).2, centerBase_mod,
    Nat.add_zero, Nat.mod_eq_of_lt i.2.isLt]

theorem P_injective (hr : 2 ≤ r) : Function.Injective (P (r := r)) := by
  intro i j hij
  have hu : i.2 = j.2 := Fin.ext (by
    have h := congrArg (fun x => x % r) hij
    simpa only [P_mod hr] using h)
  have hi := P_add_base hr i
  have hj := P_add_base hr j
  have hb : incomingBase i.1 = incomingBase j.1 := by rw [hij, hu] at hi; omega
  have hm : r*i.1.val = r*j.1.val := by dsimp [incomingBase] at hb; omega
  have hv := Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) hm
  exact Prod.ext (Fin.ext hv) hu

theorem N_injective (hr : 2 ≤ r) : Function.Injective (N (r := r)) := by
  intro i j hij
  have hu : i.2 = j.2 := Fin.ext (by
    have h := congrArg (fun x => x % r) hij
    simpa only [N_mod] using h)
  have hb : outgoingBase i.1 = outgoingBase j.1 := by
    simpa only [N, successor, hu, Nat.add_left_cancel_iff] using hij
  have hm : r*i.1.val = r*j.1.val := by dsimp [outgoingBase] at hb; omega
  have hv := Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) hm
  exact Prod.ext (Fin.ext hv) hu

theorem center_digits {u v s t : Fin r}
    (he : centerBase u+s.val = centerBase v+t.val) : u = v ∧ s = t := by
  have hd : (r+1)*u.val+s.val = (r+1)*v.val+t.val := by
    dsimp [centerBase] at he
    omega
  have hdiv := congrArg (fun x => x/(r+1)) hd
  rw [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt (by omega : s.val < r+1),
    Nat.div_eq_of_lt (by omega : t.val < r+1)] at hdiv
  have hu : u = v := Fin.ext (by simpa using hdiv)
  subst v
  exact ⟨rfl, Fin.ext (by omega)⟩

theorem C_injective : Function.Injective (C (r := r)) := by
  intro i j hij
  have he : centerBase i.2+((cyclicLatinSquare r).entry i.1 i.2).val =
      centerBase j.2+((cyclicLatinSquare r).entry j.1 j.2).val := hij
  obtain ⟨hu, hs⟩ := center_digits he
  have hj : i.1 = j.1 := by
    apply ((cyclicLatinSquare r).column_bijective j.2).injective
    simpa only [hu] using hs
  exact Prod.ext hj hu

theorem radix_digits {j k s t : Fin r}
    (he : r*j.val+s.val = r*k.val+t.val) : j = k ∧ s = t := by
  have hd := congrArg (fun x => x/r) he
  rw [Nat.mul_add_div (NeZero.pos r), Nat.mul_add_div (NeZero.pos r),
    Nat.div_eq_of_lt s.isLt, Nat.div_eq_of_lt t.isLt] at hd
  have hj : j = k := Fin.ext (by simpa using hd)
  subst k
  exact ⟨rfl, Fin.ext (by omega)⟩

theorem incoming_injective : Function.Injective (incoming (r := r)) := by
  intro i j hij
  have he : r*i.1.val+((cyclicLatinSquare r).entry i.1 i.2).val =
      r*j.1.val+((cyclicLatinSquare r).entry j.1 j.2).val := by
    dsimp [incoming, cellA, incomingBase, canonicalSymbol] at hij
    omega
  obtain ⟨hj, hs⟩ := radix_digits he
  have hu : i.2 = j.2 := by
    apply ((cyclicLatinSquare r).row_bijective j.1).injective
    simpa only [hj] using hs
  exact Prod.ext hj hu

theorem symbol_le_outgoingBase (hr : 2 ≤ r) (i : Cell r) :
    canonicalSymbol i ≤ outgoingBase i.1 := by
  have hs := symbol_lt i
  dsimp [outgoingBase]
  nlinarith

theorem outgoing_injective (hr : 2 ≤ r) : Function.Injective (outgoing (r := r)) := by
  intro i j hij
  have hi := Nat.sub_add_cancel (symbol_le_outgoingBase hr i)
  have hj := Nat.sub_add_cancel (symbol_le_outgoingBase hr j)
  have he : r*i.1.val+((cyclicLatinSquare r).entry j.1 j.2).val =
      r*j.1.val+((cyclicLatinSquare r).entry i.1 i.2).val := by
    change outgoingBase i.1-canonicalSymbol i = outgoingBase j.1-canonicalSymbol j at hij
    dsimp [outgoingBase, canonicalSymbol] at hi hj hij
    omega
  obtain ⟨hrow, hs⟩ := radix_digits he
  have hu : i.2 = j.2 := by
    apply ((cyclicLatinSquare r).row_bijective j.1).injective
    simpa only [hrow] using hs.symm
  exact Prod.ext hrow hu

/-- Tight ordinary connector-prefix bands, written without truncated endpoint subtraction. -/
theorem point_bands (hr : 2 ≤ r) (i : Cell r) :
    9*r*r+r ≤ P i ∧ P i < 11*r*r ∧
    20*r*r ≤ C i ∧ C i+2 ≤ 21*r*r+r ∧
    70*r*r ≤ N i ∧ N i+r+1 ≤ 72*r*r := by
  have hj := Nat.mul_lt_mul_of_pos_left i.1.isLt (by omega : 0 < r)
  have hu := Nat.mul_lt_mul_of_pos_left i.2.isLt (by omega : 0 < r+1)
  have hjclosed := Nat.mul_le_mul_left r (Nat.succ_le_of_lt i.1.isLt)
  have huclosed := Nat.mul_le_mul_left (r+1) (Nat.succ_le_of_lt i.2.isLt)
  have hs := symbol_lt i
  have hP := P_add_base hr i
  dsimp [P, C, N, successor, incomingBase, outgoingBase, centerBase] at hP ⊢
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem color_bands (hr : 2 ≤ r) (i : Cell r) :
    10*r*r ≤ incoming i ∧ incoming i < 11*r*r ∧
    50*r*r+1 ≤ outgoing i+r ∧ outgoing i+r ≤ 51*r*r := by
  have hj := Nat.mul_lt_mul_of_pos_left i.1.isLt (by omega : 0 < r)
  have hjclosed := Nat.mul_le_mul_left r (Nat.succ_le_of_lt i.1.isLt)
  have hs := symbol_lt i
  have hsub := Nat.sub_add_cancel (symbol_le_outgoingBase hr i)
  dsimp [incoming, outgoing, cellA, cellB, incomingBase, outgoingBase] at hsub ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

theorem P_lt_C (hr : 2 ≤ r) (i j : Cell r) : P i < C j := by
  have hi := point_bands hr i
  have hj := point_bands hr j
  nlinarith

theorem C_lt_N (hr : 2 ≤ r) (i j : Cell r) : C i < N j := by
  have hi := point_bands hr i
  have hj := point_bands hr j
  have hsq : r ≤ r*r := by nlinarith
  nlinarith

theorem incoming_lt_outgoing (hr : 2 ≤ r) (i j : Cell r) : incoming i < outgoing j := by
  have hi := color_bands hr i
  have hj := color_bands hr j
  have hsq : r ≤ r*r := by nlinarith
  nlinarith

end CorralFormalization.LatinCompletion.LatinPrefixSupply.FixedConnectorPrefix
