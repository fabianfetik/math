import Pinwheel.Streams
import Mathlib.Data.Finset.Max

/-! Alphabet-general cyclic stream compiler, extending the existing five-label
construction to the seven-role certificate sources and their parent groups. -/
namespace RealPinwheel.SevenStreams
variable {α : Type*} [Inhabited α]

def IndexPeriodic (c : ℤ → α) (i : α) (p a : ℤ) : Prop :=
  0 < p ∧ 0 ≤ a ∧ a < p ∧ ∀ n : ℤ, c n = i ↔ n % p = a

def ListIndexPeriodic (w : List (α)) (i : α) (p a : ℤ) : Prop :=
  0 < p ∧ 0 ≤ a ∧ a < p ∧ p ∣ (w.length : ℤ) ∧
    ∀ k : Fin w.length, w.get k = i ↔ (k : ℤ) % p = a

def listCycle (w : List (α)) (n : ℤ) : α :=
  let k := (n % (w.length : ℤ)).toNat
  if h : k < w.length then w.get ⟨k, h⟩ else default

lemma listCycle_eq_get {w : List (α)} (_hw : w ≠ []) (n : ℤ)
    (hidx : (n % (w.length : ℤ)).toNat < w.length) :
    listCycle w n = w.get ⟨(n % (w.length : ℤ)).toNat, hidx⟩ := by
  unfold listCycle
  rw [dif_pos hidx]

lemma listCycle_indexPeriodic {w : List (α)} {i : α} {p a : ℤ}
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

noncomputable def streamSchedule (A : ℝ) (u v : ℤ → α)
    (hA0 : 0 < A) (hA1 : A < 1) (t : ℤ) : α := by
  classical
  by_cases h : leftMem A t
  · exact u (Classical.choose h)
  · have hr : rightMem A t := (stream_partition hA0 hA1 t).resolve_left h
    exact v (Classical.choose hr)

omit [Inhabited α] in
lemma streamSchedule_left (A : ℝ) (u v : ℤ → α)
    (hA0 : 0 < A) (hA1 : A < 1) (n : ℤ) :
    streamSchedule A u v hA0 hA1 (leftStream A n) = u n := by
  classical
  have h : leftMem A (leftStream A n) := ⟨n, rfl⟩
  unfold streamSchedule
  simp only [h, ↓reduceDIte]
  congr 1
  apply leftStream_injective hA0 hA1
  exact Classical.choose_spec h

omit [Inhabited α] in
lemma streamSchedule_right (A : ℝ) (u v : ℤ → α)
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

noncomputable def streamEnum (A : ℝ) (_u _v : ℤ → α)
    (side : α → Prop) (p a : α → ℤ) (i : α) (j : ℤ) : ℤ :=
  by
    classical
    exact if side i then leftStream A (a i + p i * j)
      else rightStream A (a i + p i * j)

omit [Inhabited α] in
lemma streamEnum_left (A : ℝ) (u v : ℤ → α)
    (side : α → Prop) (p a : α → ℤ) (i : α)
    (hi : side i) :
    streamEnum A u v side p a i =
      (fun j : ℤ => leftStream A (a i + p i * j)) := by
  classical
  funext j
  unfold streamEnum
  rw [if_pos hi]

omit [Inhabited α] in
lemma streamEnum_right (A : ℝ) (u v : ℤ → α)
    (side : α → Prop) (p a : α → ℤ) (i : α)
    (hi : ¬side i) :
    streamEnum A u v side p a i =
      (fun j : ℤ => rightStream A (a i + p i * j)) := by
  classical
  funext j
  unfold streamEnum
  rw [if_neg hi]

omit [Inhabited α] in
lemma streamEnum_strictMono (A : ℝ) (u v : ℤ → α)
    (side : α → Prop) (p a : α → ℤ)
    (hA0 : 0 < A) (hA1 : A < 1)
    (hleft : ∀ i, side i → 0 < p i)
    (hright : ∀ i, ¬side i → 0 < p i)
    (i : α) : StrictMono (streamEnum A u v side p a i) := by
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

omit [Inhabited α] in
lemma stream_completeEnumeration (A : ℝ) (u v : ℤ → α)
    (side : α → Prop) (p a : α → ℤ)
    (hA0 : 0 < A) (hA1 : A < 1)
    (hdisj : ∀ n j, u n ≠ v j)
    (hleft : ∀ i, side i → IndexPeriodic u i (p i) (a i))
    (hright : ∀ i, ¬side i → IndexPeriodic v i (p i) (a i))
    (i : α) :
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

omit [Inhabited α] in
theorem stream_schedulable_of_bounds [DecidableEq α] {A : ℝ} (u v : ℤ → α)
    (side : α → Prop) (p a : α → ℤ)
    (hA0 : 0 < A) (hA1 : A < 1)
    (hdisj : ∀ n j, u n ≠ v j)
    (hleft : ∀ i, side i → IndexPeriodic u i (p i) (a i))
    (hright : ∀ i, ¬side i → IndexPeriodic v i (p i) (a i))
    (r : α → ℝ) (hr : ∀ i, 0 < r i)
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

theorem listCycle_mem {w : List (α)} (hw : w ≠ []) (n : ℤ) :
    listCycle w n ∈ w := by
  have hlen : 0 < (w.length : ℤ) := by
    exact_mod_cast List.length_pos_of_ne_nil hw
  have hidx : (n % (w.length : ℤ)).toNat < w.length := by
    apply (Int.toNat_lt (Int.emod_nonneg n hlen.ne')).mpr
    exact Int.emod_lt_of_pos n hlen
  rw [listCycle_eq_get hw n hidx]
  exact List.get_mem _ _

theorem listCycle_ne_of_disjoint {u v : List (α)}
    (hu : u ≠ []) (hv : v ≠ []) (h : List.Disjoint u v) (n m : ℤ) :
    listCycle u n ≠ listCycle v m := by
  intro heq
  have hleft := listCycle_mem hu n
  have hright := listCycle_mem hv m
  rw [← heq] at hright
  exact List.disjoint_left.mp h hleft hright


/-- Cross-side load inequalities choose one common mechanical split. -/
theorem list_stream_schedulable_of_pair_loads [Fintype α] [DecidableEq α]
    (u v : List α) (hu : u ≠ []) (hv : v ≠ []) (hdis : List.Disjoint u v)
    (side : α → Prop) (p a : α → ℤ)
    (hl : ∀ i, side i → ListIndexPeriodic u i (p i) (a i))
    (hright : ∀ i, ¬side i → ListIndexPeriodic v i (p i) (a i))
    (hneL : ∃ i, side i) (hneR : ∃ i, ¬side i)
    (r : α → ℝ) (hr : ∀ i, 0 < r i)
    (hloads : ∀ i j, side i → ¬side j → (p i : ℝ)*r i+(p j : ℝ)*r j ≤ 1) :
    SchedulableRates r := by
  classical
  let left := Finset.univ.filter side
  have hleftne : left.Nonempty := by
    obtain ⟨i,hi⟩ := hneL
    exact ⟨i,by simp [left,hi]⟩
  obtain ⟨i,hi,himax⟩ := Finset.exists_max_image left (fun i => (p i : ℝ)*r i) hleftne
  have hiside : side i := (Finset.mem_filter.mp hi).2
  obtain ⟨j,hjside⟩ := hneR
  have hpi : (0 : ℝ) < p i := by exact_mod_cast (hl i hiside).1
  have hpj : (0 : ℝ) < p j := by exact_mod_cast (hright j hjside).1
  let A := (p i : ℝ)*r i
  have hA0 : 0 < A := mul_pos hpi (hr i)
  have hA1 : A < 1 := by
    have := hloads i j hiside hjside
    have := mul_pos hpj (hr j)
    dsimp [A]
    linarith
  apply stream_schedulable_of_bounds (listCycle u) (listCycle v) side p a hA0 hA1
    (listCycle_ne_of_disjoint hu hv hdis)
    (fun k hk => listCycle_indexPeriodic hu (hl k hk))
    (fun k hk => listCycle_indexPeriodic hv (hright k hk)) r hr
  · intro k hk
    have hpk : (0 : ℝ) < p k := by exact_mod_cast (hl k hk).1
    apply (le_div_iff₀ hpk).mpr
    have hh := himax k (by simp [left,hk])
    simpa [A,mul_comm] using hh
  · intro k hk
    have hpk : (0 : ℝ) < p k := by exact_mod_cast (hright k hk).1
    apply (le_div_iff₀ hpk).mpr
    have hh := hloads i k hiside hk
    dsimp [A]
    nlinarith

end RealPinwheel.SevenStreams
