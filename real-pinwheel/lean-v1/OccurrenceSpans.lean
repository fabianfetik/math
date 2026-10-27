import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.NormNum

/-!
# Occurrence spans and bilateral service windows

This file develops the order-theoretic equivalence used by the pinwheel
formalization.  A `StrictMono` map `t : ℤ → ℤ`, together with the explicit
range-completeness hypothesis in `CompleteEnumeration`, is an enumeration of
the slots carrying a fixed label.  The schedule itself is represented by an
arbitrary predicate `p : ℤ → Prop`; no existence of such an enumeration is
claimed here.
-/

open Finset

namespace RealPinwheel

/-- `t` is a complete enumeration of the slots satisfying `p`.

The second conjunct says exactly that every slot in the label's occurrence set
appears at one (necessarily unique) integer index.  The first conjunct gives
the order of occurrences.  In particular, this is a hypothesis about an
already supplied bilateral enumeration; it does not assert that one exists.
-/
def CompleteEnumeration (p : ℤ → Prop) (t : ℤ → ℤ) : Prop :=
  StrictMono t ∧ ∀ x : ℤ, p x ↔ ∃ j : ℤ, t j = x

lemma CompleteEnumeration.strictMono {p : ℤ → Prop} {t : ℤ → ℤ}
    (h : CompleteEnumeration p t) : StrictMono t :=
  h.1

lemma CompleteEnumeration.mem_range_iff {p : ℤ → Prop} {t : ℤ → ℤ}
    (h : CompleteEnumeration p t) (x : ℤ) : p x ↔ ∃ j : ℤ, t j = x :=
  h.2 x

lemma strictMono_int_step (t : ℤ → ℤ) (ht : StrictMono t) (j : ℤ) :
    t j + 1 ≤ t (j + 1) := by
  have hlt : t j < t (j + 1) := ht (by omega)
  omega

lemma strictMono_int_step_back (t : ℤ → ℤ) (ht : StrictMono t) (j : ℤ) :
    t (j - 1) + 1 ≤ t j := by
  have hlt : t (j - 1) < t j := ht (by omega)
  omega

/-! The following two bounds make the bilateral nature of a strict integer
enumeration explicit.  They are also used to find the occurrence immediately
before an arbitrary window. -/

lemma strictMono_int_lower_bound {t : ℤ → ℤ} (ht : StrictMono t) (n : ℕ) :
    t (-(n : ℤ)) ≤ t 0 - (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := strictMono_int_step_back t ht (-(n : ℤ))
      have hs' : t (-(n : ℤ) - 1) + 1 ≤ t (-(n : ℤ)) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hs
      have hi : t (-(n : ℤ) - 1) ≤ t 0 - (n : ℤ) - 1 := by omega
      have hidx : (-(Nat.succ n : ℤ)) = -(n : ℤ) - 1 := by omega
      have hval : t 0 - (Nat.succ n : ℤ) = t 0 - (n : ℤ) - 1 := by omega
      rw [hidx, hval]
      exact hi

lemma strictMono_int_upper_bound {t : ℤ → ℤ} (ht : StrictMono t) (n : ℕ) :
    t (n : ℤ) ≥ t 0 + (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := strictMono_int_step t ht (n : ℤ)
      norm_num at hs ⊢
      omega

lemma exists_strictMono_bracket {t : ℤ → ℤ} (ht : StrictMono t) (m : ℤ) :
    ∃ j : ℤ, t j < m ∧ m ≤ t (j + 1) := by
  let n : ℤ := min 0 (m - t 0 - 1)
  have hn : n ≤ 0 := min_le_left _ _
  have htn : t n < m := by
    have hqneg : -(((-n).toNat : ℤ)) = n := by omega
    have hbound := strictMono_int_lower_bound ht (-n).toNat
    rw [hqneg] at hbound
    have hn_right : n ≤ m - t 0 - 1 := min_le_right _ _
    dsimp [n] at hn_right
    omega
  let K : ℤ := max 0 (m - t 0)
  have hs_upper : ∀ k : ℤ, t k < m → k ≤ K := by
    intro k hk
    by_cases hk_nonneg : 0 ≤ k
    · have hupper := strictMono_int_upper_bound ht k.toNat
      have hk_eq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
      rw [hk_eq] at hupper
      dsimp [K] at *
      omega
    · have hlow := strictMono_int_lower_bound ht (-k).toNat
      have hk_eq : -(((-k).toNat : ℤ)) = k := by
        have hq : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
        omega
      rw [hk_eq] at hlow
      dsimp [K]
      omega
  have hnk : n ≤ K := hs_upper n htn
  have hF : (Finset.Icc n K).filter (fun k => t k < m) |>.Nonempty := by
    refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hnk⟩, htn⟩⟩
  let F : Finset ℤ := (Finset.Icc n K).filter (fun k => t k < m)
  let j : ℤ := F.max' hF
  have hj_mem : j ∈ F := F.max'_mem hF
  have hj_max : ∀ k ∈ F, k ≤ j := by
    intro k hk
    exact F.le_max' k hk
  have hj_mem' := Finset.mem_filter.mp hj_mem
  refine ⟨j, ?_, ?_⟩
  · exact hj_mem'.2
  · by_contra hnext
    have hnextlt : t (j + 1) < m := lt_of_not_ge hnext
    have hnextK : j + 1 ≤ K := hs_upper (j + 1) hnextlt
    have hnext_mem : j + 1 ∈ F := by
      apply Finset.mem_filter.mpr
      have hnj : n ≤ j := (Finset.mem_Icc.mp hj_mem'.1).1
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, hnextK⟩, hnextlt⟩
    have hle : j + 1 ≤ j := hj_max (j + 1) hnext_mem
    omega

lemma card_Ioc_int (j : ℤ) (ell : ℕ) : #(Finset.Ioc j (j + (ell : ℤ))) = ell := by
  have hcard := Int.card_Ioc_of_le (a := j) (b := j + (ell : ℤ)) (by omega)
  apply Int.ofNat_inj.mp
  rw [hcard]
  omega

lemma card_Ioc_int_pred (j : ℤ) (ell : ℕ) (hell : 0 < ell) :
    #(Finset.Ioc j (j + (ell : ℤ) - 1)) = ell - 1 := by
  have hcard := Int.card_Ioc_of_le (a := j) (b := j + (ell : ℤ) - 1) (by omega)
  apply Int.ofNat_inj.mp
  rw [hcard]
  omega

/-- The number of occurrences of `p` in the integer window `[m,m+L)`.

The classical decision procedure is encapsulated in this definition so the
mathematical statements below do not carry a decidability hypothesis for the
schedule predicate. -/
noncomputable def windowCount (p : ℤ → Prop) (m L : ℤ) : ℕ := by
  classical
  exact ((Finset.Ico m (m + L)).filter p).card

/-! A fixed integer window length.  The cardinality is taken over exactly the
integer slots `Ico m (m + L)`, so the right endpoint is excluded. -/

theorem window_span_iff_fixed_length
    {p : ℤ → Prop} {t : ℤ → ℤ}
    (hcomplete : CompleteEnumeration p t)
    {ell : ℕ} (hell : 0 < ell) (L : ℤ) :
    (∀ m : ℤ, ell ≤ windowCount p m L) ↔
      ∀ j : ℤ, t (j + (ell : ℤ)) - t j ≤ L := by
  classical
  let ht : StrictMono t := hcomplete.strictMono
  constructor
  · intro hw j
    by_contra hspan
    have hspan' : L < t (j + (ell : ℤ)) - t j := lt_of_not_ge hspan
    let m : ℤ := t j + 1
    have hwindow : ∀ {x : ℤ}, x ∈ Finset.Ico m (m + L) → p x →
        x ∈ (Finset.Ioc j (j + (ell : ℤ) - 1)).image t := by
      intro x hx hpx
      rcases hcomplete.mem_range_iff x |>.mp hpx with ⟨i, hi⟩
      have hxi : t i ∈ Finset.Ico m (m + L) := by simpa [hi] using hx
      have hlow : t j < t i := by
        rw [Finset.mem_Ico] at hxi
        dsimp [m] at hxi
        have : t j < t i := by omega
        exact this
      have hupper : t i < t (j + (ell : ℤ)) := by
        rw [Finset.mem_Ico] at hxi
        dsimp [m] at hxi
        omega
      have hi_bounds : i ∈ Finset.Ioc j (j + (ell : ℤ) - 1) := by
        rw [Finset.mem_Ioc]
        constructor
        · exact (ht.lt_iff_lt).mp hlow
        · have hi_lt : i < j + (ell : ℤ) := (ht.lt_iff_lt).mp hupper
          omega
      exact Finset.mem_image.mpr ⟨i, hi_bounds, hi⟩
    have hsub :
        ((Finset.Ico m (m + L)).filter p) ⊆
          (Finset.Ioc j (j + (ell : ℤ) - 1)).image t := by
      intro x hx
      rw [Finset.mem_filter] at hx
      exact hwindow hx.1 hx.2
    have hcardle := Finset.card_le_card hsub
    have hcard := card_Ioc_int_pred j ell hell
    rw [Finset.card_image_of_injective _ ht.injective, hcard] at hcardle
    have hw' : ell ≤ ((Finset.Ico m (m + L)).filter p).card := by
      simpa [windowCount] using hw m
    dsimp [m] at hcardle hw'
    omega
  · intro hspan m
    obtain ⟨j, hjlt, hjnext⟩ := exists_strictMono_bracket ht m
    have htop : t (j + (ell : ℤ)) < m + L := by
      have hbound := hspan j
      omega
    have himage : (Finset.Ioc j (j + (ell : ℤ))).image t ⊆
        (Finset.Ico m (m + L)).filter p := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      have hibounds := (Finset.mem_Ioc.mp hi)
      have hti_low : m ≤ t i := by
        have hji : j + 1 ≤ i := by omega
        exact (hjnext.trans (ht.monotone hji))
      have hti_top : t i < m + L := by
        have hik : i ≤ j + (ell : ℤ) := by omega
        exact (ht.monotone hik).trans_lt htop
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hti_low, hti_top⟩, hcomplete.mem_range_iff (t i) |>.mpr ⟨i, rfl⟩⟩
    have hcardle := Finset.card_le_card himage
    rw [Finset.card_image_of_injective _ ht.injective, card_Ioc_int j ell] at hcardle
    simpa [windowCount] using hcardle

/-! Real periods enter only through the integer length obtained by `Int.ceil`.
No positivity assumption on `a` is needed for this equivalence: if the ceiling
length is nonpositive, both sides are false because a strict enumeration has
positive `ell`-spans. -/

theorem window_span_iff_real_period
    {p : ℤ → Prop} {t : ℤ → ℤ}
    (hcomplete : CompleteEnumeration p t)
    {ell : ℕ} (hell : 0 < ell) (a : ℝ) :
    (∀ m : ℤ, ell ≤ windowCount p m (Int.ceil (((ell : ℕ) : ℝ) * a))) ↔
      ∀ j : ℤ, t (j + (ell : ℤ)) - t j ≤ Int.ceil (((ell : ℕ) : ℝ) * a) := by
  exact window_span_iff_fixed_length hcomplete hell (Int.ceil (((ell : ℕ) : ℝ) * a))

/-! The equivalence can be used independently at every positive scale. -/

theorem all_windows_span_iff_real_period
    {p : ℤ → Prop} {t : ℤ → ℤ}
    (hcomplete : CompleteEnumeration p t) (a : ℝ) :
    (∀ ell : ℕ, 0 < ell →
      ∀ m : ℤ, ell ≤ windowCount p m (Int.ceil (((ell : ℕ) : ℝ) * a))) ↔
      ∀ ell : ℕ, 0 < ell →
        ∀ j : ℤ, t (j + (ell : ℤ)) - t j ≤
          Int.ceil (((ell : ℕ) : ℝ) * a) := by
  constructor
  · intro h ell hell
    exact (window_span_iff_real_period hcomplete hell a).mp (h ell hell)
  · intro h ell hell
    exact (window_span_iff_real_period hcomplete hell a).mpr (h ell hell)

end RealPinwheel
