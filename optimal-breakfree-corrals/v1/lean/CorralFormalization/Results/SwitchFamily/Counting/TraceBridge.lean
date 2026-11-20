import CorralFormalization.Results.SwitchFamily.Counting.Orbits

/-!
# Actual local-word counts and the transfer-matrix trace

This is a new extension after the frozen counting core. It proves the
closed-walk identification rather than assuming that an arbitrary sequence
with the same first values counts the cyclic layouts.
-/

set_option backward.isDefEq.respectTransparency false

namespace CorralFormalization.Results.SwitchFamily.Counting

open Finset Matrix

namespace Transfer

variable {α : Type*} (R : α → α → Prop)

/-- A length-n directed path, retaining both endpoints and every edge. -/
abbrev Path (n : ℕ) (a b : α) :=
  {f : Fin (n+1) → α // f 0 = a ∧ f (Fin.last n) = b ∧
    ∀ i : Fin n, R (f i.castSucc) (f i.succ)}

def zeroEquiv (a b : α) : Path R 0 a b ≃ {e : Unit // a=b} where
  toFun f := ⟨(), f.2.1.symm.trans f.2.2.1⟩
  invFun e := ⟨fun _ => a,rfl,e.2,fun i => Fin.elim0 i⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Fin.ext (by have hi := i.isLt; omega)
    subst i
    exact f.2.1.symm
  right_inv e := by apply Subtype.ext; rfl

/-- Cutting the actual first edge gives an actual path decomposition. -/
def succEquiv (n : ℕ) (a b : α) :
    Path R (n+1) a b ≃ Σ c : α, {e : Unit // R a c} × Path R n c b where
  toFun f := ⟨f.1 1, ⟨⟨(),by
    have he := f.2.2.2 0
    simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one, f.2.1] using he⟩,
    ⟨fun i => f.1 i.succ,rfl,by simpa only [Fin.succ_last] using f.2.2.1,
      fun i => by simpa only [Fin.castSucc_succ] using f.2.2.2 i.succ⟩⟩⟩
  invFun v := ⟨Fin.cons a v.2.2.1,by simp,by simpa using v.2.2.2.2.1,
    fun i => by
      cases i using Fin.cases with
      | zero => simpa [v.2.2.2.1] using v.2.1.2
      | succ i => simpa only [Fin.castSucc_succ, Fin.cons_succ] using v.2.2.2.2.2 i⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero => simpa using f.2.1.symm
    | succ i => rfl
  right_inv v := by
    rcases v with ⟨c,e,⟨f,hstart,hend,hedge⟩⟩
    cases hstart
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext; rfl

/-- The final sample at time n+1 is the repeated time-zero endpoint.
All n+1 cyclic edges are retained, including the edge across the cut. -/
def cyclicEquiv (n : ℕ) :
    LocalWord α R (n+1) ≃ Σ a : α, Path R (n+1) a a where
  toFun u := ⟨u 0, ⟨fun i => u (i.val : ZMod (n+1)),by simp,by simp,
    fun i => by
      simpa only [Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one] using
        u.2 (i.val : ZMod (n+1))⟩⟩
  invFun p := ⟨fun x : ZMod (n+1) => p.2.1 (Fin.castSucc x),by
    change ∀ x : Fin (n+1), R (p.2.1 x.castSucc) (p.2.1 ((x+1).castSucc))
    intro x
    have he := p.2.2.2.2 x
    cases x using Fin.lastCases with
    | last =>
      rw [Fin.last_add_one]
      simpa only [Fin.succ_last,Fin.castSucc_zero,p.2.2.1,p.2.2.2.1] using he
    | cast j =>
      have hj : (j.castSucc + 1 : Fin (n+1)) = j.succ := by
        apply Fin.ext
        have hn : 1 < n+1 := by have hi := j.isLt; omega
        have hjlt : j.val+1 < n+1 := by have hi := j.isLt; omega
        change (j.val + (1 : Fin (n+1)).val) % (n+1) = j.val+1
        have hone : (1 : Fin (n+1)).val = 1 := Nat.mod_eq_of_lt hn
        rw [hone,Nat.mod_eq_of_lt hjlt]
      rw [hj]
      simpa only [Fin.castSucc_succ] using he⟩
  left_inv u := by
    apply Subtype.ext
    funext x
    change u ((x.val : ℕ) : ZMod (n+1)) = u x
    rw [ZMod.natCast_zmod_val]
  right_inv p := by
    rcases p with ⟨a,⟨f,hstart,hend,hedge⟩⟩
    cases hstart
    apply Sigma.ext (by simp)
    apply (Subtype.heq_iff_coe_eq (by intro g; simp)).mpr
    funext i
    cases i using Fin.lastCases with
    | last => simpa using hend.symm
    | cast j =>
      change f ((Fin.ofNat (n+1) j.val).castSucc) = f j.castSucc
      have hj : (Fin.ofNat (n+1) j.val) = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
      rw [hj]

variable [Fintype α] [DecidableEq α] [DecidableRel R]

def adjacency : Matrix α α ℕ := fun a b => if R a b then 1 else 0

private theorem edge_card (a b : α) :
    Fintype.card {e : Unit // R a b} = if R a b then 1 else 0 := by
  classical
  by_cases hr : R a b <;> simp [hr]

theorem path_card (n : ℕ) (a b : α) :
    Fintype.card (Path R n a b) = (adjacency R ^ n) a b := by
  induction n generalizing a b with
  | zero =>
    rw [Fintype.card_congr (zeroEquiv R a b)]
    by_cases hab : a=b <;> simp [hab,Matrix.one_apply]
  | succ n ih =>
    rw [Fintype.card_congr (succEquiv R n a b),Fintype.card_sigma]
    simp_rw [Fintype.card_prod,edge_card,ih]
    rw [pow_succ',Matrix.mul_apply]
    rfl
/-- The trace counts the actual cyclic word type. -/
theorem localWord_card_trace (n : ℕ) :
    Nat.card (LocalWord α R (n+1)) = Matrix.trace (adjacency R ^ (n+1)) := by
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (cyclicEquiv R n),Fintype.card_sigma]
  simp_rw [path_card]
  rfl

end Transfer/-- The printed directed 2/3 transfer matrix over natural counts. -/
def tileMatrix : Matrix (Fin 3) (Fin 3) ℕ := Transfer.adjacency tileEdge

theorem tileMatrix_eq : tileMatrix = !![0,1,0;1,0,1;1,0,0] := by decide +kernel

/-- The actual positive-period layout count equals the matrix trace.
At j=0 the state-word count is not asserted to equal the trace of I. -/
theorem C_eq_trace (j : ℕ) [NeZero j] :
    C j = Matrix.trace (tileMatrix ^ j) := by
  cases j with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Transfer.localWord_card_trace tileEdge n

end CorralFormalization.Results.SwitchFamily.Counting
