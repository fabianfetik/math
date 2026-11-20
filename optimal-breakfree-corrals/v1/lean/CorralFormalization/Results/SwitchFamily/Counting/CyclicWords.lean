import Mathlib

/-!
# Marked directed cycle words and their genuine rotation quotient

The adjacency rule, including the last-to-first edge, is imposed at every
marked phase.  This retains internal tile positions even at periods one and
two; in particular it does not replace a short directed interval by its
underlying set of residues.  The decoration alphabet is held fixed when the
period is changed.
-/

namespace CorralFormalization.Results.SwitchFamily.Counting

open Function Finset

/-- An actual cyclic local word, with the edge across the marked cut included. -/
abbrev LocalWord (α : Type*) (R : α → α → Prop) (h : ℕ) :=
  {f : ZMod h → α // ∀ x, R (f x) (f (x+1))}

namespace LocalWord

variable {α : Type*} {R : α → α → Prop} {h : ℕ}

instance [Fintype α] [NeZero h] [DecidableRel R] : Fintype (LocalWord α R h) :=
  inferInstanceAs (Fintype {f : ZMod h → α // ∀ x, R (f x) (f (x+1))})

instance [DecidableEq α] [NeZero h] : DecidableEq (LocalWord α R h) := inferInstanceAs
  (DecidableEq {f : ZMod h → α // ∀ x, R (f x) (f (x+1))})

instance : CoeFun (LocalWord α R h) (fun _ => ZMod h → α) := ⟨Subtype.val⟩

@[ext] theorem ext {u v : LocalWord α R h} (huv : ∀ x, u x = v x) : u = v :=
  Subtype.ext (funext huv)

/-- Positive precomposition gives a left additive action since the phase group
is commutative. -/
def rotate (t : ZMod h) (u : LocalWord α R h) : LocalWord α R h :=
  ⟨fun x => u (x+t), fun x => by simpa [add_assoc, add_comm, add_left_comm] using u.2 (x+t)⟩

@[simp] theorem rotate_apply (t : ZMod h) (u : LocalWord α R h) (x : ZMod h) :
    rotate t u x = u (x+t) := rfl

instance : AddAction (ZMod h) (LocalWord α R h) where
  vadd := rotate
  zero_vadd u := by
    apply Subtype.ext; funext x
    change u (x+0) = u x
    simp
  add_vadd t s u := by
    apply Subtype.ext; funext x
    change u (x+(t+s)) = u ((x+t)+s)
    simp [add_assoc]

@[simp] theorem vadd_apply (t : ZMod h) (u : LocalWord α R h) (x : ZMod h) :
    (t +ᵥ u) x = u (x+t) := rfl

theorem fixed_iff (t : ZMod h) (u : LocalWord α R h) :
    t +ᵥ u = u ↔ ∀ x, u (x+t) = u x := by
  constructor
  · intro he x; exact congrArg (fun v : LocalWord α R h => v x) he
  · exact fun he => ext he

/-- The integer lift is useful for Bézout: both the ambient period and any
rotation period are genuine periods of this function. -/
def intLift (u : LocalWord α R h) (x : ℤ) : α := u (x : ZMod h)

theorem intLift_period (u : LocalWord α R h) : Periodic u.intLift (h : ℤ) := by
  intro x
  simp [intLift]

theorem intLift_period_of_fixed (u : LocalWord α R h) (t : ℕ)
    (ht : (t : ZMod h) +ᵥ u = u) : Periodic u.intLift (t : ℤ) := by
  intro x
  simpa [intLift] using (fixed_iff _ _).mp ht (x : ZMod h)

/-- Bézout, rather than a quotient of underlying tile-support sets. -/
theorem periodic_gcd {f : ℤ → α} {a b : ℕ}
    (ha : Periodic f (a : ℤ)) (hb : Periodic f (b : ℤ)) :
    Periodic f (Nat.gcd a b : ℤ) := by
  rw [Nat.gcd_eq_gcd_ab]
  simpa [mul_comm] using (ha.int_mul (Nat.gcdA a b)).add_period
    (hb.int_mul (Nat.gcdB a b))

theorem periodic_emod {f : ℤ → α} {d : ℕ} (hd : Periodic f (d : ℤ)) (x : ℤ) :
    f (x % d) = f x := by
  rw [Int.emod_def]
  simpa [mul_comm] using hd.sub_int_mul_eq (x / d) (x := x)

/-- Pullback along the actual residue map preserves every local edge, also
when the edge crosses either marked cut. -/
def inflate {d : ℕ} (hd : d ∣ h) (u : LocalWord α R d) : LocalWord α R h :=
  ⟨fun x => u (ZMod.castHom hd (ZMod d) x), fun x => by
    change R (u (ZMod.castHom hd (ZMod d) x)) (u (ZMod.castHom hd (ZMod d) (x+1)))
    rw [map_add, map_one]
    exact u.2 (ZMod.castHom hd (ZMod d) x)⟩

@[simp] theorem inflate_apply {d : ℕ} (hd : d ∣ h) (u : LocalWord α R d) (x : ZMod h) :
    inflate hd u x = u (ZMod.castHom hd (ZMod d) x) := rfl

/-- A word whose integer lift has period d descends by residue representatives.
The following lemma proves that no information is lost at the cut. -/
def descend {d : ℕ} [NeZero d] (u : LocalWord α R h)
    (hd : Periodic u.intLift (d : ℤ)) : LocalWord α R d := by
  let g : ZMod d → α := fun x => u ((x.val : ℕ) : ZMod h)
  have hg : ∀ x : ℤ, g (x : ZMod d) = u.intLift x := by
    intro x
    have he : u.intLift (((x : ZMod d).val : ℕ) : ℤ) = u.intLift x := by
      rw [ZMod.val_intCast]
      exact periodic_emod hd x
    simpa [g, intLift] using he
  refine ⟨g, ?_⟩
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have hz : ((z : ZMod d) + 1) = ((z+1 : ℤ) : ZMod d) := by simp
  rw [hz, hg, hg]
  simpa [intLift] using u.2 (z : ZMod h)

@[simp] theorem descend_intCast {d : ℕ} [NeZero d] (u : LocalWord α R h)
    (hd : Periodic u.intLift (d : ℤ)) (x : ℤ) :
    descend u hd (x : ZMod d) = u (x : ZMod h) := by
  have he : u.intLift (((x : ZMod d).val : ℕ) : ℤ) = u.intLift x := by
    rw [ZMod.val_intCast]
    exact periodic_emod hd x
  simpa [descend, intLift] using he

theorem inflate_descend {d : ℕ} [NeZero d] (hdh : d ∣ h) (u : LocalWord α R h)
    (hd : Periodic u.intLift (d : ℤ)) : inflate hdh (descend u hd) = u := by
  ext x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp

/-- An exact bijection between fixed h-words and d-words, d = gcd(h,t).
The alphabet and the local relation are identical on both sides. -/
def fixedEquiv (t : ℕ) [NeZero (Nat.gcd h t)] :
    {u : LocalWord α R h // (t : ZMod h) +ᵥ u = u} ≃
      LocalWord α R (Nat.gcd h t) where
  toFun u := descend u.1 (periodic_gcd u.1.intLift_period
    (u.1.intLift_period_of_fixed t u.2))
  invFun v := ⟨inflate (Nat.gcd_dvd_left h t) v, by
    apply (fixed_iff _ _).mpr
    intro x
    simp only [inflate_apply, map_add, map_natCast]
    rw [show (t : ZMod (Nat.gcd h t)) = 0 from
      (CharP.cast_eq_zero_iff (ZMod (Nat.gcd h t)) (Nat.gcd h t) t).mpr (Nat.gcd_dvd_right h t)]
    simp⟩
  left_inv u := by
    apply Subtype.ext
    exact inflate_descend _ _ _
  right_inv v := by
    ext x
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    simp

/-- Burnside here counts the actual quotient by the above rotation action. -/
theorem orbit_card_mul [NeZero h] [Fintype α] [DecidableRel R] :
    Nat.card (Quotient (AddAction.orbitRel (ZMod h) (LocalWord α R h))) * h =
      ∑ t : ZMod h, Nat.card (AddAction.fixedBy (LocalWord α R h) t) := by
  classical
  letI := Fintype.ofFinite (Quotient (AddAction.orbitRel (ZMod h) (LocalWord α R h)))
  letI (t : ZMod h) := Fintype.ofFinite (AddAction.fixedBy (LocalWord α R h) t)
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using (AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    (ZMod h) (LocalWord α R h)).symm

end LocalWord

/-- State 0 is a tile start. A two-tile has states 0,1 and a three-tile
has states 0,1,2; starts and internal positions remain distinct. -/
def tileEdge (a b : Fin 3) : Prop :=
  (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) ∨ (a=1 ∧ b=2) ∨ (a=2 ∧ b=0)

instance : DecidableRel tileEdge := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

abbrev Layout (h : ℕ) := LocalWord (Fin 3) tileEdge h

/-- C_j from the paper, as actual marked local-word cardinality, for j > 0. -/
def layoutCount (j : ℕ) [NeZero j] : ℕ := Fintype.card (Layout j)

/-- A fixed Q-element alphabet is chosen at the target height. No occurrence
of `m` is recomputed when h is replaced by a divisor. -/
abbrev DecoratedLayout (h Q : ℕ) :=
  LocalWord (Fin 3 × Fin Q) (fun a b => tileEdge a.1 b.1) h

/-- Decorations are independent at the marked phases. -/
def decoratedEquiv (h Q : ℕ) :
    DecoratedLayout h Q ≃ Layout h × (ZMod h → Fin Q) where
  toFun u := (⟨fun x => (u x).1, u.2⟩, fun x => (u x).2)
  invFun u := ⟨fun x => (u.1 x,u.2 x), u.1.2⟩
  left_inv u := by apply Subtype.ext; rfl
  right_inv u := by rfl

theorem decorated_card (h Q : ℕ) [NeZero h] :
    Fintype.card (DecoratedLayout h Q) = layoutCount h * Q^h := by
  rw [Fintype.card_congr (decoratedEquiv h Q), Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rfl

/-- Rotation fixed points, including small gcd periods and cut-crossing tiles. -/
theorem decorated_fixed_card (h Q t : ℕ) [NeZero h] :
    Fintype.card {u : DecoratedLayout h Q // (t : ZMod h) +ᵥ u = u} =
      letI : NeZero (Nat.gcd h t) := ⟨Nat.ne_of_gt (Nat.gcd_pos_of_pos_left t (NeZero.pos h))⟩
      layoutCount (Nat.gcd h t) * Q^(Nat.gcd h t) := by
  letI : NeZero (Nat.gcd h t) := ⟨Nat.ne_of_gt (Nat.gcd_pos_of_pos_left t (NeZero.pos h))⟩
  rw [Fintype.card_congr (LocalWord.fixedEquiv t), decorated_card]

/-- In particular no layout can have period one. -/
theorem layoutCount_one : layoutCount 1 = 0 := by decide +kernel

theorem layoutCount_two : layoutCount 2 = 2 := by decide +kernel

theorem layoutCount_three : layoutCount 3 = 3 := by decide +kernel

theorem layoutCount_four : layoutCount 4 = 2 := by decide +kernel

theorem layoutCount_five : layoutCount 5 = 5 := by decide +kernel

end CorralFormalization.Results.SwitchFamily.Counting
