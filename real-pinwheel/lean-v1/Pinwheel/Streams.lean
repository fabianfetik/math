import Pinwheel.Rates
import Mathlib.NumberTheory.Rayleigh
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-!
# Complementary mechanical streams

This file contains the elementary, bilateral construction used by the
five-task cover.  The two streams are the floor and ceiling-minus-one Beatty
sequences.  A finite cyclic labelling of either stream is represented by a
periodic index predicate; this keeps the analytic part of the construction
independent of the particular cycles used by the catalogue.
-/

namespace RealPinwheel

open Set

/-! The two physical streams.  We use the definitions from Rayleigh's theorem
directly, so that the complement identity also applies at rational parameters
and at negative indices. -/

noncomputable def leftStream (A : ℝ) : ℤ → ℤ := beattySeq A⁻¹

noncomputable def rightStream (A : ℝ) : ℤ → ℤ := beattySeq' (1 - A)⁻¹

def leftMem (A : ℝ) (t : ℤ) : Prop := t ∈ Set.range (leftStream A)

def rightMem (A : ℝ) (t : ℤ) : Prop := t ∈ Set.range (rightStream A)

lemma leftStream_strictMono {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    StrictMono (leftStream A) := by
  have hq : 1 < A⁻¹ := (one_lt_inv₀ hA0).2 hA1
  intro n m hnm
  unfold leftStream beattySeq
  have hnm1 : (1 : ℝ) ≤ (m : ℝ) - n := by
    exact_mod_cast (show (1 : ℤ) ≤ m - n by omega)
  have hmul : (1 : ℝ) < ((m : ℝ) - n) * A⁻¹ := by
    calc
      (1 : ℝ) < A⁻¹ := hq
      _ ≤ ((m : ℝ) - n) * A⁻¹ := by
        simpa using mul_le_mul_of_nonneg_right hnm1 (inv_pos.mpr hA0).le
  have hgap : (n : ℝ) * A⁻¹ + 1 < (m : ℝ) * A⁻¹ := by
    nlinarith
  have hfloor : ((⌊(n : ℝ) * A⁻¹⌋ : ℤ) : ℝ) + 1 ≤ (m : ℝ) * A⁻¹ := by
    have hf : ((⌊(n : ℝ) * A⁻¹⌋ : ℤ) : ℝ) ≤ (n : ℝ) * A⁻¹ :=
      Int.floor_le _
    linarith
  have hle : (⌊(n : ℝ) * A⁻¹⌋ : ℤ) + 1 ≤ ⌊(m : ℝ) * A⁻¹⌋ :=
    (Int.le_floor).2 (by simpa only [Int.cast_add, Int.cast_one] using hfloor)
  omega

lemma rightStream_strictMono {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    StrictMono (rightStream A) := by
  have hB0 : 0 < 1 - A := sub_pos.mpr hA1
  have hq : 1 < (1 - A)⁻¹ :=
    (one_lt_inv₀ hB0).2 (sub_lt_self 1 hA0)
  intro n m hnm
  unfold rightStream beattySeq'
  have hnm1 : (1 : ℝ) ≤ (m : ℝ) - n := by
    exact_mod_cast (show (1 : ℤ) ≤ m - n by omega)
  have hmul : (1 : ℝ) < ((m : ℝ) - n) * (1 - A)⁻¹ := by
    calc
      (1 : ℝ) < (1 - A)⁻¹ := hq
      _ ≤ ((m : ℝ) - n) * (1 - A)⁻¹ := by
        simpa using mul_le_mul_of_nonneg_right hnm1 (inv_pos.mpr hB0).le
  have hgap : (n : ℝ) * (1 - A)⁻¹ + 1 <
      (m : ℝ) * (1 - A)⁻¹ := by
    nlinarith
  have hceil : (⌈(n : ℝ) * (1 - A)⁻¹⌉ : ℝ) <
      (m : ℝ) * (1 - A)⁻¹ := by
    exact lt_of_lt_of_le (Int.ceil_lt_add_one _) (le_of_lt hgap)
  have hle : ⌈(n : ℝ) * (1 - A)⁻¹⌉ <
      ⌈(m : ℝ) * (1 - A)⁻¹⌉ := (Int.lt_ceil).2 hceil
  omega

lemma leftStream_injective {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    Function.Injective (leftStream A) :=
  (leftStream_strictMono hA0 hA1).injective

lemma rightStream_injective {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    Function.Injective (rightStream A) :=
  (rightStream_strictMono hA0 hA1).injective

lemma stream_range_complement {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    (Set.range (leftStream A))ᶜ = Set.range (rightStream A) := by
  change {x | ¬ ∃ k, beattySeq A⁻¹ k = x} =
    {x | ∃ k, beattySeq' (1 - A)⁻¹ k = x}
  exact compl_beattySeq (Real.HolderConjugate.inv_one_sub_inv hA0 hA1)

lemma stream_partition {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) (t : ℤ) :
    leftMem A t ∨ rightMem A t := by
  by_cases h : leftMem A t
  · exact Or.inl h
  · right
    have ht : t ∈ (Set.range (leftStream A))ᶜ := h
    rw [stream_range_complement hA0 hA1] at ht
    exact ht

lemma stream_disjoint {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) {t : ℤ} :
    ¬(leftMem A t ∧ rightMem A t) := by
  intro ht
  have hnot : t ∈ (Set.range (leftStream A))ᶜ := by
    rw [stream_range_complement hA0 hA1]
    exact ht.2
  exact hnot ht.1

/-! A useful exact representation of a residue class on the integer line. -/

def IndexPeriodic (c : ℤ → Fin 5) (i : Fin 5) (p a : ℤ) : Prop :=
  0 < p ∧ 0 ≤ a ∧ a < p ∧ ∀ n : ℤ, c n = i ↔ n % p = a

def ListIndexPeriodic (w : List (Fin 5)) (i : Fin 5) (p a : ℤ) : Prop :=
  0 < p ∧ 0 ≤ a ∧ a < p ∧ p ∣ (w.length : ℤ) ∧
    ∀ k : Fin w.length, w.get k = i ↔ (k : ℤ) % p = a

def listCycle (w : List (Fin 5)) (n : ℤ) : Fin 5 :=
  let k := (n % (w.length : ℤ)).toNat
  if h : k < w.length then w.get ⟨k, h⟩ else 0

lemma int_eq_add_mul_of_emod_eq {n p a : ℤ} (hp : 0 < p)
    (ha0 : 0 ≤ a) (hap : a < p) (hmod : n % p = a) :
    ∃ k : ℤ, n = a + p * k := by
  refine ⟨n / p, ?_⟩
  have hdiv := Int.emod_add_mul_ediv n p
  omega

lemma emod_add_mul_eq {a p j : ℤ} (hp : 0 < p) (ha0 : 0 ≤ a) (hap : a < p) :
    (a + p * j) % p = a := by
  rw [Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt ha0 hap

lemma emod_mod_of_dvd {n p N : ℤ} (hdiv : p ∣ N) :
    (n % N) % p = n % p := by
  exact Int.emod_emod_of_dvd n hdiv

lemma listCycle_eq_get {w : List (Fin 5)} (hw : w ≠ []) (n : ℤ)
    (hidx : (n % (w.length : ℤ)).toNat < w.length) :
    listCycle w n = w.get ⟨(n % (w.length : ℤ)).toNat, hidx⟩ := by
  unfold listCycle
  rw [dif_pos hidx]

lemma listCycle_indexPeriodic {w : List (Fin 5)} {i : Fin 5} {p a : ℤ}
    (hw : w ≠ []) (h : ListIndexPeriodic w i p a) :
    IndexPeriodic (listCycle w) i p a := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro n
  let N : ℤ := w.length
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (List.length_pos_of_ne_nil hw)
  have hrem0 : 0 ≤ n % N := Int.emod_nonneg n hN.ne'
  have hremN : n % N < N := Int.emod_lt_of_pos n hN
  have hidx : (n % (w.length : ℤ)).toNat < w.length := by
    apply (Int.toNat_lt hrem0).2
    exact_mod_cast hremN
  let k : Fin w.length :=
    ⟨(n % N).toNat, by
      apply (Int.toNat_lt hrem0).2
      exact_mod_cast hremN⟩
  have hfinite := h.2.2.2.2 k
  have hmod := emod_mod_of_dvd (n := n) (p := p) (N := N) h.2.2.2.1
  have hkcast : (k : ℤ) = n % N := by
    dsimp [k, N]
    exact Int.toNat_of_nonneg hrem0
  have hcycle := listCycle_eq_get hw n hidx
  rw [hcycle]
  rw [hkcast] at hfinite
  simpa [hmod] using hfinite

/-! Rounding estimates used for occurrence spans.  They are stated on the
whole real line; in particular no positivity of the base point is needed. -/

lemma floor_increment_le_ceil (x y : ℝ) :
    ⌊x + y⌋ - ⌊x⌋ ≤ ⌈y⌉ := by
  have hx : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hy : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
  have hxy : x + y < (⌊x⌋ : ℝ) + (⌈y⌉ : ℝ) + 1 := by
    linarith
  have hlt : ⌊x + y⌋ < (⌊x⌋ + ⌈y⌉ + 1 : ℤ) := by
    apply (Int.floor_lt).2
    simpa only [Int.cast_add, Int.cast_one] using hxy
  omega

lemma ceil_add_le (x y : ℝ) :
    ⌈x + y⌉ ≤ ⌈x⌉ + ⌈y⌉ := by
  apply (Int.ceil_le).2
  have hx : (x : ℝ) ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  have hy : (y : ℝ) ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
  push_cast
  linarith

lemma leftStream_increment {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1)
    (n d : ℤ) (hd : 0 ≤ d) :
    leftStream A (n + d) - leftStream A n ≤
      ⌈(d : ℝ) / A⌉ := by
  have h := floor_increment_le_ceil
    ((n : ℝ) * A⁻¹) ((d : ℝ) * A⁻¹)
  simpa [leftStream, beattySeq, add_mul, Int.cast_add, div_eq_mul_inv] using h

lemma rightStream_increment {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1)
    (n d : ℤ) (hd : 0 ≤ d) :
    rightStream A (n + d) - rightStream A n ≤
      ⌈(d : ℝ) / (1 - A)⌉ := by
  have h := ceil_add_le
    ((n : ℝ) * (1 - A)⁻¹) ((d : ℝ) * (1 - A)⁻¹)
  have h' : ⌈(n : ℝ) * (1 - A)⁻¹ + (d : ℝ) * (1 - A)⁻¹⌉ -
      ⌈(n : ℝ) * (1 - A)⁻¹⌉ ≤
      ⌈(d : ℝ) / (1 - A)⌉ := by
    simpa [div_eq_mul_inv, add_comm] using h
  simpa [rightStream, beattySeq', add_mul, Int.cast_add, div_eq_mul_inv] using h'

lemma leftStream_span_bound {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1)
    {p : ℤ} {r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hpr : r ≤ A / p) (a j ell : ℤ) (hell : 0 < ell) :
    leftStream A (a + p * (j + ell)) - leftStream A (a + p * j) ≤
      ⌈(ell : ℝ) * (r : ℝ)⁻¹⌉ := by
  have hd : 0 ≤ p * ell := by positivity
  have hinc := leftStream_increment hA0 hA1
    (a + p * j) (p * ell) hd
  have harg : ((p * ell : ℤ) : ℝ) / A ≤
      (ell : ℝ) * (r : ℝ)⁻¹ := by
    have hdivpos : 0 < A / (p : ℝ) := div_pos hA0 (by exact_mod_cast hp)
    have hinv : (A / (p : ℝ))⁻¹ ≤ r⁻¹ :=
      (inv_le_inv₀ hdivpos hr).2 hpr
    have hcoef : (p : ℝ) / A ≤ r⁻¹ := by
      calc
        (p : ℝ) / A = (A / (p : ℝ))⁻¹ := by
          have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
          field_simp [hA0.ne', hpR]
        _ ≤ r⁻¹ := hinv
    have harg' := mul_le_mul_of_nonneg_left hcoef
      (by positivity : 0 ≤ (ell : ℝ))
    calc
      ((p * ell : ℤ) : ℝ) / A = (p : ℝ) / A * (ell : ℝ) := by
        push_cast
        ring
      _ ≤ (ell : ℝ) * r⁻¹ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using harg'
  have hceil := Int.ceil_mono harg
  have hrewrite : a + p * (j + ell) = (a + p * j) + p * ell := by ring
  calc
    leftStream A (a + p * (j + ell)) - leftStream A (a + p * j) ≤
        ⌈((p * ell : ℤ) : ℝ) / A⌉ := by
      rw [hrewrite]
      exact hinc
    _ ≤ ⌈(ell : ℝ) * r⁻¹⌉ := hceil

lemma rightStream_span_bound {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1)
    {p : ℤ} {r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hpr : r ≤ (1 - A) / p) (a j ell : ℤ) (hell : 0 < ell) :
    rightStream A (a + p * (j + ell)) - rightStream A (a + p * j) ≤
      ⌈(ell : ℝ) * (r : ℝ)⁻¹⌉ := by
  have hd : 0 ≤ p * ell := by positivity
  have hinc := rightStream_increment hA0 hA1
    (a + p * j) (p * ell) hd
  have harg : ((p * ell : ℤ) : ℝ) / (1 - A) ≤
      (ell : ℝ) * (r : ℝ)⁻¹ := by
    have hB0 : 0 < 1 - A := sub_pos.mpr hA1
    have hdivpos : 0 < (1 - A) / (p : ℝ) :=
      div_pos hB0 (by exact_mod_cast hp)
    have hinv : ((1 - A) / (p : ℝ))⁻¹ ≤ r⁻¹ :=
      (inv_le_inv₀ hdivpos hr).2 hpr
    have hcoef : (p : ℝ) / (1 - A) ≤ r⁻¹ := by
      calc
        (p : ℝ) / (1 - A) = ((1 - A) / (p : ℝ))⁻¹ := by
          have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
          field_simp [hB0.ne', hpR]
        _ ≤ r⁻¹ := hinv
    have harg' := mul_le_mul_of_nonneg_left hcoef
      (by positivity : 0 ≤ (ell : ℝ))
    calc
      ((p * ell : ℤ) : ℝ) / (1 - A) =
          (p : ℝ) / (1 - A) * (ell : ℝ) := by
        push_cast
        ring
      _ ≤ (ell : ℝ) * r⁻¹ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using harg'
  have hceil := Int.ceil_mono harg
  have hrewrite : a + p * (j + ell) = (a + p * j) + p * ell := by ring
  calc
    rightStream A (a + p * (j + ell)) - rightStream A (a + p * j) ≤
        ⌈((p * ell : ℤ) : ℝ) / (1 - A)⌉ := by
      rw [hrewrite]
      exact hinc
    _ ≤ ⌈(ell : ℝ) * r⁻¹⌉ := hceil

/-! The schedule chooses the left value on left-stream slots and the right
value on right-stream slots.  The range-complement theorem supplies the
right witness in the second branch. -/

noncomputable def streamSchedule (A : ℝ) (u v : ℤ → Fin 5)
    (hA0 : 0 < A) (hA1 : A < 1) (t : ℤ) : Fin 5 := by
  classical
  by_cases h : leftMem A t
  · exact u (Classical.choose h)
  · have hr : rightMem A t := (stream_partition hA0 hA1 t).resolve_left h
    exact v (Classical.choose hr)

lemma streamSchedule_left (A : ℝ) (u v : ℤ → Fin 5)
    (hA0 : 0 < A) (hA1 : A < 1) (n : ℤ) :
    streamSchedule A u v hA0 hA1 (leftStream A n) = u n := by
  classical
  have h : leftMem A (leftStream A n) := ⟨n, rfl⟩
  unfold streamSchedule
  simp only [h, ↓reduceDIte]
  congr 1
  apply leftStream_injective hA0 hA1
  exact Classical.choose_spec h

lemma streamSchedule_right (A : ℝ) (u v : ℤ → Fin 5)
    (hA0 : 0 < A) (hA1 : A < 1) (n : ℤ) :
    streamSchedule A u v hA0 hA1 (rightStream A n) = v n := by
  classical
  have hr : rightMem A (rightStream A n) := ⟨n, rfl⟩
  have hl : ¬leftMem A (rightStream A n) := by
    intro h
    exact (stream_disjoint hA0 hA1) ⟨h, hr⟩
  unfold streamSchedule
  simp only [hl, ↓reduceDIte]
  congr 1
  apply rightStream_injective hA0 hA1
  exact Classical.choose_spec ((stream_partition hA0 hA1 _).resolve_left hl)

/-! Every label in a cycle is assigned to one side.  Its occurrence indices
form one residue class, and hence have a bilateral affine enumeration. -/

noncomputable def streamEnum (A : ℝ) (u v : ℤ → Fin 5)
    (side : Fin 5 → Prop) (p a : Fin 5 → ℤ) (i : Fin 5) (j : ℤ) : ℤ :=
  by
    classical
    exact if side i then leftStream A (a i + p i * j)
      else rightStream A (a i + p i * j)

lemma streamEnum_left (A : ℝ) (u v : ℤ → Fin 5)
    (side : Fin 5 → Prop) (p a : Fin 5 → ℤ) (i : Fin 5)
    (hi : side i) :
    streamEnum A u v side p a i =
      (fun j : ℤ => leftStream A (a i + p i * j)) := by
  classical
  funext j
  unfold streamEnum
  rw [if_pos hi]

lemma streamEnum_right (A : ℝ) (u v : ℤ → Fin 5)
    (side : Fin 5 → Prop) (p a : Fin 5 → ℤ) (i : Fin 5)
    (hi : ¬side i) :
    streamEnum A u v side p a i =
      (fun j : ℤ => rightStream A (a i + p i * j)) := by
  classical
  funext j
  unfold streamEnum
  rw [if_neg hi]

lemma streamEnum_strictMono (A : ℝ) (u v : ℤ → Fin 5)
    (side : Fin 5 → Prop) (p a : Fin 5 → ℤ)
    (hA0 : 0 < A) (hA1 : A < 1)
    (hleft : ∀ i, side i → 0 < p i)
    (hright : ∀ i, ¬side i → 0 < p i)
    (i : Fin 5) : StrictMono (streamEnum A u v side p a i) := by
  classical
  by_cases hi : side i
  · rw [streamEnum_left A u v side p a i hi]
    apply (leftStream_strictMono hA0 hA1).comp
    intro j k hjk
    simpa [add_comm] using
      (add_lt_add_left (mul_lt_mul_of_pos_left hjk (hleft i hi)) (a i))
  · rw [streamEnum_right A u v side p a i hi]
    apply (rightStream_strictMono hA0 hA1).comp
    intro j k hjk
    simpa [add_comm] using
      (add_lt_add_left (mul_lt_mul_of_pos_left hjk (hright i hi)) (a i))

lemma stream_completeEnumeration (A : ℝ) (u v : ℤ → Fin 5)
    (side : Fin 5 → Prop) (p a : Fin 5 → ℤ)
    (hA0 : 0 < A) (hA1 : A < 1)
    (hdisj : ∀ n j, u n ≠ v j)
    (hleft : ∀ i, side i → IndexPeriodic u i (p i) (a i))
    (hright : ∀ i, ¬side i → IndexPeriodic v i (p i) (a i))
    (i : Fin 5) :
    CompleteEnumeration
      (fun x => streamSchedule A u v hA0 hA1 x = i)
      (streamEnum A u v side p a i) := by
  classical
  constructor
  · exact streamEnum_strictMono A u v side p a hA0 hA1
      (fun k hk => (hleft k hk).1) (fun k hk => (hright k hk).1) i
  · intro x
    constructor
    · intro hx
      by_cases hi : side i
      · by_cases hl : leftMem A x
        · obtain ⟨n, hn⟩ := hl
          have hval : u n = i := by
            have hs := streamSchedule_left A u v hA0 hA1 n
            rw [← hn, hs] at hx
            exact hx
          have hper := hleft i hi
          obtain ⟨j, hj⟩ := int_eq_add_mul_of_emod_eq hper.1 hper.2.1
            hper.2.2.1 ((hper.2.2.2 n).mp hval)
          refine ⟨j, ?_⟩
          rw [streamEnum_left A u v side p a i hi]
          rw [← hn, hj]
        · have hr : rightMem A x :=
            (stream_partition hA0 hA1 x).resolve_left hl
          obtain ⟨j, hj⟩ := hr
          have hval : v j = i := by
            have hs := streamSchedule_right A u v hA0 hA1 j
            rw [← hj, hs] at hx
            exact hx
          have hper := hleft i hi
          have hu : u (a i) = i := by
            apply (hper.2.2.2 _).mpr
            exact Int.emod_eq_of_lt hper.2.1 hper.2.2.1
          exact False.elim ((hdisj (a i) j) (hu.trans hval.symm))
      · by_cases hr : rightMem A x
        · obtain ⟨n, hn⟩ := hr
          have hval : v n = i := by
            have hs := streamSchedule_right A u v hA0 hA1 n
            rw [← hn, hs] at hx
            exact hx
          have hper := hright i hi
          obtain ⟨j, hj⟩ := int_eq_add_mul_of_emod_eq hper.1 hper.2.1
            hper.2.2.1 ((hper.2.2.2 n).mp hval)
          refine ⟨j, ?_⟩
          rw [streamEnum_right A u v side p a i hi]
          rw [← hn, hj]
        · have hl : leftMem A x :=
            (stream_partition hA0 hA1 x).resolve_right hr
          obtain ⟨n, hn⟩ := hl
          have hval : u n = i := by
            have hs := streamSchedule_left A u v hA0 hA1 n
            rw [← hn, hs] at hx
            exact hx
          have hper := hright i hi
          have hv : v (a i) = i := by
            apply (hper.2.2.2 _).mpr
            exact Int.emod_eq_of_lt hper.2.1 hper.2.2.1
          exact False.elim ((hdisj n (a i)) (hval.trans hv.symm))
    · rintro ⟨j, rfl⟩
      by_cases hi : side i
      · rw [streamEnum_left A u v side p a i hi]
        rw [streamSchedule_left]
        exact (hleft i hi).2.2.2 _ |>.mpr
          (emod_add_mul_eq (hleft i hi).1 (hleft i hi).2.1
            (hleft i hi).2.2.1)
      · rw [streamEnum_right A u v side p a i hi]
        rw [streamSchedule_right]
        exact (hright i hi).2.2.2 _ |>.mpr
          (emod_add_mul_eq (hright i hi).1 (hright i hi).2.1
            (hright i hi).2.2.1)

/-! The main reusable construction theorem.  The two families of bounds say
that every requested rate is below the reciprocal of its integer index gap,
after multiplying by the density of its physical stream. -/

theorem stream_schedulable_of_bounds {A : ℝ} (u v : ℤ → Fin 5)
    (side : Fin 5 → Prop) (p a : Fin 5 → ℤ)
    (hA0 : 0 < A) (hA1 : A < 1)
    (hdisj : ∀ n j, u n ≠ v j)
    (hleft : ∀ i, side i → IndexPeriodic u i (p i) (a i))
    (hright : ∀ i, ¬side i → IndexPeriodic v i (p i) (a i))
    (r : Fin 5 → ℝ) (hr : ∀ i, 0 < r i)
    (hleftRate : ∀ i, side i → r i ≤ A / (p i : ℝ))
    (hrightRate : ∀ i, ¬side i → r i ≤ (1 - A) / (p i : ℝ)) :
    SchedulableRates r := by
  refine schedulableRates_of_enumerations hr
    (streamSchedule A u v hA0 hA1)
    (streamEnum A u v side p a)
    (fun i => stream_completeEnumeration A u v side p a hA0 hA1
      hdisj hleft hright i) ?_
  intro i ell hell j
  by_cases hi : side i
  · rw [streamEnum_left A u v side p a i hi]
    exact leftStream_span_bound hA0 hA1 (hleft i hi).1 (hr i)
      (hleftRate i hi) (a i) j (ell : ℤ) (by exact_mod_cast hell)
  · rw [streamEnum_right A u v side p a i hi]
    exact rightStream_span_bound hA0 hA1 (hright i hi).1 (hr i)
      (hrightRate i hi) (a i) j (ell : ℤ) (by exact_mod_cast hell)

end RealPinwheel
