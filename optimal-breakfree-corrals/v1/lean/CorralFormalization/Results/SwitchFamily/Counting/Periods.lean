import CorralFormalization.Results.SwitchFamily.Counting.Orbits

/-!
# Least periods and Möbius inversion for actual marked local words
-/

namespace CorralFormalization.Results.SwitchFamily.Counting

open Function Finset

namespace LocalWord

variable {α : Type*} {R : α → α → Prop} {h d : ℕ}

/-- The actual one-phase translation on the marked object. -/
def step : LocalWord α R h → LocalWord α R h := rotate 1

theorem step_iterate (u : LocalWord α R h) (k : ℕ) :
    step^[k] u = (k : ZMod h) +ᵥ u := by
  induction k with
  | zero => simp [step]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    ext x
    simp [step, rotate, Nat.cast_add, add_comm, add_left_comm]

theorem isPeriodicPt_iff_fixed (u : LocalWord α R h) (k : ℕ) :
    IsPeriodicPt step k u ↔ (k : ZMod h) +ᵥ u = u := by
  change step^[k] u = u ↔ _
  rw [step_iterate]

noncomputable def period (u : LocalWord α R h) : ℕ := minimalPeriod step u

theorem period_dvd (u : LocalWord α R h) : u.period ∣ h := by
  apply IsPeriodicPt.minimalPeriod_dvd
  rw [isPeriodicPt_iff_fixed]
  simp

theorem period_pos [NeZero h] (u : LocalWord α R h) : 0 < u.period := by
  apply IsPeriodicPt.minimalPeriod_pos (NeZero.pos h)
  rw [isPeriodicPt_iff_fixed]
  simp

theorem period_mem_divisors [NeZero h] (u : LocalWord α R h) : u.period ∈ h.divisors :=
  Nat.mem_divisors.mpr ⟨u.period_dvd, NeZero.ne h⟩

theorem fixed_iff_period_dvd (u : LocalWord α R h) (k : ℕ) :
    (k : ZMod h) +ᵥ u = u ↔ u.period ∣ k := by
  rw [← isPeriodicPt_iff_fixed, Function.isPeriodicPt_iff_minimalPeriod_dvd]
  rfl

theorem inflate_injective (hdh : d ∣ h) :
    Function.Injective (inflate hdh : LocalWord α R d → LocalWord α R h) := by
  intro u v he
  ext x
  obtain ⟨y, hy⟩ := ZMod.castHom_surjective hdh x
  have hxy := congrArg (fun w : LocalWord α R h => w y) he
  simpa only [inflate_apply, hy] using hxy

/-- Inflation preserves every rotation period, not only one chosen period. -/
theorem inflate_fixed_iff (hdh : d ∣ h) (u : LocalWord α R d) (k : ℕ) :
    (k : ZMod h) +ᵥ inflate hdh u = inflate hdh u ↔ (k : ZMod d) +ᵥ u = u := by
  constructor
  · intro hk
    apply (fixed_iff _ _).mpr
    intro x
    obtain ⟨y, hy⟩ := ZMod.castHom_surjective hdh x
    have hyk := (fixed_iff _ _).mp hk y
    simpa only [inflate_apply, map_add, map_natCast, hy] using hyk
  · intro hk
    apply (fixed_iff _ _).mpr
    intro x
    simpa only [inflate_apply, map_add, map_natCast] using
      (fixed_iff _ _).mp hk (ZMod.castHom hdh (ZMod d) x)

theorem period_inflate (hdh : d ∣ h) (u : LocalWord α R d) :
    (inflate hdh u).period = u.period := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro k
  rw [isPeriodicPt_iff_fixed, isPeriodicPt_iff_fixed, inflate_fixed_iff]

theorem period_rotate (t : ZMod h) (u : LocalWord α R h) :
    (t +ᵥ u).period = u.period := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro k
  rw [isPeriodicPt_iff_fixed, isPeriodicPt_iff_fixed]
  constructor
  · intro hk
    apply (fixed_iff _ _).mpr
    intro x
    have he := (fixed_iff _ _).mp hk (x-t)
    change u ((x-t)+(k : ZMod h)+t) = u ((x-t)+t) at he
    have hx : (x-t)+(k : ZMod h)+t = x+k := by abel
    simpa only [hx, sub_add_cancel] using he
  · intro hk
    apply (fixed_iff _ _).mpr
    intro x
    have he := (fixed_iff _ _).mp hk (x+t)
    simpa [vadd_apply, add_assoc, add_comm, add_left_comm] using he

/-- Actual marked objects with full least period. -/
abbrev Primitive (α : Type*) (R : α → α → Prop) (h : ℕ) :=
  {u : LocalWord α R h // u.period = h}

noncomputable instance [Fintype α] [NeZero h] [DecidableRel R] :
    Fintype (Primitive α R h) := Fintype.ofFinite _

/-- Primitive d-words are in bijection with h-words of least period d,
using the same alphabet and relation. -/
noncomputable def primitiveFiberEquiv [NeZero d] (hdh : d ∣ h) :
    Primitive α R d ≃ {u : LocalWord α R h // u.period = d} :=
  Equiv.ofBijective (fun v => ⟨inflate hdh v.1, (period_inflate hdh v.1).trans v.2⟩) (by
    constructor
    · intro u v he
      apply Subtype.ext
      apply inflate_injective hdh
      exact congrArg Subtype.val he
    · intro u
      have hp : (d : ZMod h) +ᵥ u.1 = u.1 :=
        (fixed_iff_period_dvd u.1 d).mpr (by rw [u.2])
      let v := descend u.1 (u.1.intLift_period_of_fixed d hp)
      have hv : inflate hdh v = u.1 := inflate_descend hdh _ _
      have hpv : v.period = d := by rw [← period_inflate hdh v, hv, u.2]
      exact ⟨⟨v,hpv⟩, Subtype.ext hv⟩)

/-- The actual disjoint decomposition by least period. -/
theorem sum_primitive_card [Fintype α] [DecidableRel R] [NeZero h] :
    (∑ d ∈ h.divisors, Nat.card (Primitive α R d)) =
      Nat.card (LocalWord α R h) := by
  classical
  calc
    (∑ d ∈ h.divisors, Nat.card (Primitive α R d)) =
        ∑ d ∈ h.divisors, #{u : LocalWord α R h | u.period = d} := by
      apply Finset.sum_congr rfl
      intro d hd
      letI : NeZero d := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)⟩
      rw [Nat.card_congr (primitiveFiberEquiv (Nat.mem_divisors.mp hd).1),
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card (LocalWord α R h) := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      rw [Finset.filter_eq_self.mpr (fun u _ => u.period_mem_divisors),
        Finset.card_univ, Nat.card_eq_fintype_card]

instance : AddAction (ZMod h) (Primitive α R h) where
  vadd t u := ⟨t +ᵥ u.1, (period_rotate t u.1).trans u.2⟩
  zero_vadd u := by apply Subtype.ext; exact zero_vadd _ _
  add_vadd t s u := by apply Subtype.ext; exact add_vadd _ _ _

/-- Full least period is exactly trivial rotational stabilizer. -/
theorem primitive_fixed_iff [NeZero h] (u : Primitive α R h) (t : ZMod h) :
    t +ᵥ u = u ↔ t = 0 := by
  constructor
  · intro ht
    have he : t +ᵥ u.1 = u.1 := congrArg Subtype.val ht
    rw [← ZMod.natCast_zmod_val t, fixed_iff_period_dvd, u.2] at he
    have hv : t.val = 0 := Nat.eq_zero_of_dvd_of_lt he (ZMod.val_lt t)
    exact (ZMod.val_eq_zero t).mp hv
  · rintro rfl; exact zero_vadd _ _

/-- The quotient is formed after restricting the genuine rotation action to
its primitive objects. -/
noncomputable def primitiveOrbitCount (α : Type*) (R : α → α → Prop) (h : ℕ) : ℕ :=
  Nat.card (Quotient (AddAction.orbitRel (ZMod h) (Primitive α R h)))

theorem primitive_orbit_card_mul [Fintype α] [DecidableRel R] [NeZero h] :
    primitiveOrbitCount α R h * h = Nat.card (Primitive α R h) := by
  classical
  letI := Fintype.ofFinite (Quotient (AddAction.orbitRel (ZMod h) (Primitive α R h)))
  letI (t : ZMod h) := Fintype.ofFinite (AddAction.fixedBy (Primitive α R h) t)
  have hb := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    (ZMod h) (Primitive α R h)
  have hc : ∀ t : ZMod h, Fintype.card (AddAction.fixedBy (Primitive α R h) t) =
      if t = 0 then Fintype.card (Primitive α R h) else 0 := by
    intro t
    rw [Fintype.card_subtype]
    change #{u : Primitive α R h | t +ᵥ u = u} = _
    simp only [primitive_fixed_iff]
    split_ifs with ht <;> simp [ht]
  simp_rw [hc] at hb
  simpa [primitiveOrbitCount, Nat.card_eq_fintype_card] using hb.symm

end LocalWord

noncomputable def primitiveCount (h Q : ℕ) : ℕ :=
  Nat.card (LocalWord.Primitive (Fin 3 × Fin Q) (fun a b => tileEdge a.1 b.1) h)

noncomputable def aperiodicOrbitCount (h Q : ℕ) : ℕ :=
  LocalWord.primitiveOrbitCount (Fin 3 × Fin Q) (fun a b => tileEdge a.1 b.1) h

theorem sum_primitiveCount (h Q : ℕ) [NeZero h] :
    (∑ d ∈ h.divisors, primitiveCount d Q) = C h * Q^h := by
  rw [← decorated_natCard]
  exact LocalWord.sum_primitive_card

/-- Formula (A10)'s numerator counts actual full-period marked words. -/
theorem primitiveCount_moebius (h Q : ℕ) [NeZero h] :
    (primitiveCount h Q : ℤ) =
      ∑ d ∈ h.divisors, ArithmeticFunction.moebius d * (C (h/d) : ℤ) * (Q : ℤ)^(h/d) := by
  have hs : ∀ j > 0, (∑ d ∈ j.divisors, (primitiveCount d Q : ℤ)) =
      (C j : ℤ) * (Q : ℤ)^j := by
    intro j hj
    letI : NeZero j := ⟨hj.ne'⟩
    exact_mod_cast sum_primitiveCount j Q
  have hi := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hs h (NeZero.pos h)
  change (∑ x ∈ h.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 *
    ((C x.2 : ℤ) * (Q : ℤ)^x.2)) = _ at hi
  rw [Nat.sum_divisorsAntidiagonal (fun d j => ArithmeticFunction.moebius d *
    ((C j : ℤ) * (Q : ℤ)^j))] at hi
  simpa only [mul_assoc] using hi.symm

/-- The division by h is justified by the actual action on full-period words. -/
theorem aperiodic_orbit_mul (h Q : ℕ) [NeZero h] :
    aperiodicOrbitCount h Q * h = primitiveCount h Q :=
  LocalWord.primitive_orbit_card_mul

/-- A complete abstract version of (A10), in integers to retain the signs
of Möbius inversion without truncated natural subtraction. -/
theorem aperiodic_moebius_mul (h Q : ℕ) [NeZero h] :
    (aperiodicOrbitCount h Q : ℤ) * h =
      ∑ d ∈ h.divisors, ArithmeticFunction.moebius d * (C (h/d) : ℤ) * (Q : ℤ)^(h/d) := by
  rw [← primitiveCount_moebius]
  exact_mod_cast aperiodic_orbit_mul h Q

/-- The displayed rational division form of (A10), for actual primitive
cyclic-word orbits. -/
theorem aperiodic_moebius (h Q : ℕ) [NeZero h] :
    (aperiodicOrbitCount h Q : ℚ) =
      (∑ d ∈ h.divisors, (ArithmeticFunction.moebius d : ℚ) *
        (C (h/d) : ℚ) * (Q : ℚ)^(h/d)) / (h : ℚ) := by
  apply (eq_div_iff (by exact_mod_cast NeZero.ne h)).mpr
  have hi := congrArg (fun z : ℤ => (z : ℚ)) (aperiodic_moebius_mul h Q)
  push_cast at hi
  exact hi

end CorralFormalization.Results.SwitchFamily.Counting
