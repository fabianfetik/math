import CorralFormalization.DiversityCompletion.LatinPrefixFrame

/-!
# Literal connector-free (L6), (L14), and (H4) geometry

Only the distinct, bounded column coordinates are inputs.  Their Walecki
construction and the rainbow-prefix argument are separate.  In particular,
this file does not assume a physical partition or a completed terrace.
-/

namespace CorralFormalization.LatinCompletion.ConnectorFreePhysical

open LatinTransfer TerraceLift

/-- The exact column data needed downstream of the rainbow-prefix proof.
The column need not be below `r` when `r` is odd. -/
structure Coordinates (r : ℕ) where
  modulus : ℕ
  lower : r ≤ modulus
  upper : modulus ≤ r + 1
  column : Fin r → Fin modulus
  column_injective : Function.Injective column

namespace Coordinates

variable {r : ℕ} [NeZero r] (D : Coordinates r)

def xi (t : Fin r) : ℕ :=
  20*r*r+(D.modulus+1)*(D.column t).val-
    (D.modulus+1)*(D.column ⟨0,NeZero.pos r⟩).val

def a (j : Fin r) : ℕ := 10*r*r+D.modulus*j.val
def b (j : Fin r) : ℕ := 50*r*r+D.modulus*j.val

def predecessor (j t : Fin r) : ℕ := D.xi t-D.a j
def successor (j t : Fin r) : ℕ := D.xi t+D.b j

def residue (t s : Fin r) : ℕ := D.xi t+s.val

def offset (_D : Coordinates r) (h : ℕ) (j : Fin r) : ZMod h := (r*j.val : ℕ)

def phase (_D : Coordinates r) {h : ℕ} (a : ZMod h) (t : Fin r) : ZMod h :=
  a+((2+t.val : ℕ) : ZMod h)

/-- Exactly (H4): `xi_t+s+(a+2+t)n mod h*n`. -/
def site (h n : ℕ) (c : ZMod h × Fin r × Fin r) : ZMod (h*n) :=
  ((D.residue c.2.1 c.2.2+(D.phase c.1 c.2.1).val*n : ℕ) : ZMod (h*n))

def cellA (i : Cell r) : ℕ := D.a i.1
def cellB (i : Cell r) : ℕ := D.b i.1

def choice {h : ℕ} (L : Family h r) (q : ZMod h) (i : Cell r) : ℕ :=
  ((L (q+D.offset h i.1)).entry i.1 i.2).val

theorem column_product_bound (hr : 3 ≤ r) (t : Fin r) :
    (D.modulus+1)*(D.column t).val ≤ 2*r*r := by
  have hm := D.upper
  have hc := (D.column t).isLt
  have hmul := Nat.mul_le_mul_left (D.modulus+1)
    (by omega : (D.column t).val+1 ≤ D.modulus)
  have hsq := Nat.mul_le_mul hm hm
  nlinarith

theorem xi_normalization (hr : 3 ≤ r) (t : Fin r) :
    D.xi t+(D.modulus+1)*(D.column ⟨0,NeZero.pos r⟩).val =
      20*r*r+(D.modulus+1)*(D.column t).val := by
  apply Nat.sub_add_cancel
  have := D.column_product_bound hr ⟨0,NeZero.pos r⟩
  nlinarith

theorem xi_bounds (hr : 3 ≤ r) (t : Fin r) :
    18*r*r ≤ D.xi t ∧ D.xi t ≤ 22*r*r := by
  have hzero := D.column_product_bound hr ⟨0,NeZero.pos r⟩
  have ht := D.column_product_bound hr t
  have he := D.xi_normalization hr t
  constructor <;> nlinarith

theorem a_positive (hr : 3 ≤ r) (j : Fin r) : 0 < D.a j := by
  dsimp [a]
  nlinarith

theorem local_gap_geometry {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (j t s : Fin r) :
    D.predecessor j t < D.xi t+s.val ∧
    D.xi t+s.val < D.successor j t ∧
    D.predecessor j t+D.a j = D.xi t ∧
    D.xi t+s.val-D.predecessor j t = D.a j+s.val ∧
    D.successor j t-(D.xi t+s.val) = D.b j-s.val ∧
    2 < D.a j+s.val ∧ D.a j+s.val < n ∧
    2 < D.b j-s.val ∧ D.b j-s.val < n := by
  have hxi := D.xi_bounds hr t
  have hm := D.upper
  have hj := j.isLt
  have hs := s.isLt
  have hprod := Nat.mul_le_mul_left D.modulus (by omega : j.val ≤ r-1)
  have hprod' : D.modulus*j.val ≤ r*r := by nlinarith
  have ha : D.a j ≤ D.xi t := by dsimp [a]; nlinarith
  have hb : s.val < D.b j := by dsimp [b]; nlinarith
  have hin : 2 < D.a j+s.val ∧ D.a j+s.val < n := by
    dsimp [a]
    constructor <;> nlinarith
  have hout : 2 < D.b j-s.val ∧ D.b j-s.val < n := by
    have hB : 2+s.val < D.b j ∧ D.b j < n := by
      dsimp [b]
      constructor <;> nlinarith
    omega
  have hcancel := Nat.sub_add_cancel ha
  dsimp [predecessor,successor]
  omega

theorem residue_lt {n : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n) (t s : Fin r) :
    D.residue t s < n := by
  have := D.xi_bounds hr t
  have := s.isLt
  dsimp [residue]
  nlinarith

theorem residue_injective (hr : 3 ≤ r) :
    Function.Injective (fun p : Fin r × Fin r => D.residue p.1 p.2) := by
  rintro ⟨t,s⟩ ⟨v,w⟩ he
  have hnormt := D.xi_normalization hr t
  have hnormv := D.xi_normalization hr v
  have hdigit : (D.modulus+1)*(D.column t).val+s.val =
      (D.modulus+1)*(D.column v).val+w.val := by
    dsimp [residue] at he
    omega
  have hs : s.val < D.modulus+1 := by have := D.lower; have := s.isLt; omega
  have hw : w.val < D.modulus+1 := by have := D.lower; have := w.isLt; omega
  have hdiv := congrArg (fun k => k/(D.modulus+1)) hdigit
  rw [Nat.mul_add_div (by omega),Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt hs,Nat.div_eq_of_lt hw] at hdiv
  have htv : t=v := D.column_injective (Fin.ext (by simpa using hdiv))
  subst v
  have hsw : s=w := Fin.ext (by omega)
  subst w
  rfl

theorem offset_injective {h : ℕ} (hh : r*r ≤ h) : Function.Injective (D.offset h) := by
  intro j k he
  have hr : 0 < r := NeZero.pos r
  have hj : r*j.val < h := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left j.isLt hr) hh
  have hk : r*k.val < h := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left k.isLt hr) hh
  have hv := congrArg ZMod.val he
  change ((r*j.val : ℕ) : ZMod h).val=((r*k.val : ℕ) : ZMod h).val at hv
  rw [ZMod.val_natCast_of_lt hj,ZMod.val_natCast_of_lt hk] at hv
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hr hv)

theorem site_eq_unreduced {h n : ℕ} [NeZero h] (a : ZMod h) (t s : Fin r) :
    D.site h n (a,t,s)=
      ((D.residue t s+(a.val+(2+t.val))*n : ℕ) : ZMod (h*n)) := by
  have hcast : ((a.val+(2+t.val) : ℕ) : ZMod h)=D.phase a t := by simp [phase]
  have hp := congrArg ZMod.val hcast
  rw [ZMod.val_natCast] at hp
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  change D.residue t s+(D.phase a t).val*n ≡
    D.residue t s+(a.val+(2+t.val))*n [MOD h*n]
  rw [← hp]
  exact ((Nat.mod_modEq _ h).mul_right' n).add_left _

theorem site_val {h n : ℕ} [NeZero h] (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (c : ZMod h × Fin r × Fin r) :
    (D.site h n c).val=D.residue c.2.1 c.2.2+(D.phase c.1 c.2.1).val*n := by
  apply ZMod.val_natCast_of_lt
  have := D.residue_lt hr hn c.2.1 c.2.2
  have := (D.phase c.1 c.2.1).val_lt
  nlinarith

/-- Distinct literal H4 pools and symbols are physically disjoint. -/
theorem site_injective {h n : ℕ} [NeZero h] (hr : 3 ≤ r) (hn : 200*r*r ≤ n) :
    Function.Injective (D.site h n) := by
  rintro ⟨a,t,s⟩ ⟨b,v,w⟩ he
  have ht := D.residue_lt hr hn t s
  have hv := D.residue_lt hr hn v w
  have hnpos : 0 < n := by nlinarith
  have heval := congrArg ZMod.val he
  rw [D.site_val hr hn,D.site_val hr hn] at heval
  have hres := congrArg (fun k => k%n) heval
  simp only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt hv] at hres
  have htv := D.residue_injective hr (a₁ := (t,s)) (a₂ := (v,w)) hres
  have htv' : t=v := congrArg Prod.fst htv
  have hsw : s=w := congrArg Prod.snd htv
  subst v
  subst w
  have hpval : (D.phase a t).val=(D.phase b t).val := by nlinarith
  have hp := ZMod.val_injective h hpval
  have hab : a=b := add_right_cancel hp
  subst b
  rfl

/-- Formula (L14) reduces to exactly the (H4) site after rephasing by `r*j`. -/
theorem lift_eq_site {h n : ℕ} [NeZero h] (q : ZMod h) (j t s : Fin r) :
    ((q.val*n+D.residue t s+(2+r*j.val+t.val)*n : ℕ) : ZMod (h*n))=
      D.site h n (q+D.offset h j,t,s) := by
  simp only [site,Nat.cast_add]
  change zeroSite h n q+(D.residue t s : ZMod (h*n))+
    (((2+r*j.val+t.val)*n : ℕ) : ZMod (h*n)) =
      (D.residue t s : ZMod (h*n))+zeroSite h n (D.phase (q+D.offset h j) t)
  have hOff : zeroSite h n (D.offset h j)=((r*j.val*n : ℕ) : ZMod (h*n)) :=
    zeroSite_natCast h n (r*j.val)
  have hC : zeroSite h n ((2+t.val : ℕ) : ZMod h)=
      (((2+t.val)*n : ℕ) : ZMod (h*n)) := zeroSite_natCast h n (2+t.val)
  rw [phase,zeroSite_add,zeroSite_add,hOff,hC]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

end Coordinates
end CorralFormalization.LatinCompletion.ConnectorFreePhysical
