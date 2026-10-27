import Pinwheel.SevenStreams
import Pinwheel.WeakServiceTransport

/-! Reusable adapters for the exact two-root cyclic sources in the WS7 band.
The profile records finite cycles and their indexed residue descriptions;
rate-dependent work is confined to the explicit cross-root load inequalities.
-/

namespace RealPinwheel

open SevenStreams

/-- Two disjoint finite cycles whose roles occupy complementary mechanical
streams. `period` and `residue` give the exact cyclic positions for every
role. -/
structure WeakSevenCyclicProfile where
  left : List (Fin 7)
  right : List (Fin 7)
  side : Fin 7 → Prop
  period : Fin 7 → ℤ
  residue : Fin 7 → ℤ
  left_ne : left ≠ []
  right_ne : right ≠ []
  disjoint : List.Disjoint left right
  left_nonempty : ∃ i, side i
  right_nonempty : ∃ i, ¬ side i
  period_pos : ∀ i, 0 < period i
  left_periodic : ∀ i, side i →
    SevenStreams.ListIndexPeriodic left i (period i) (residue i)
  right_periodic : ∀ i, ¬ side i →
    SevenStreams.ListIndexPeriodic right i (period i) (residue i)

/-- The common ordinary source supplied by a cyclic profile when all pairs
across the two parent streams fit in one time slot. -/
theorem WeakSevenCyclicProfile.schedulable_of_pair_loads
    (profile : WeakSevenCyclicProfile) {r : Fin 7 → ℝ}
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ i j, profile.side i → ¬ profile.side j →
      (profile.period i : ℝ) * r i + (profile.period j : ℝ) * r j ≤ 1) :
    SchedulableRates r := by
  apply list_stream_schedulable_of_pair_loads
    profile.left profile.right profile.left_ne profile.right_ne profile.disjoint
    profile.side profile.period profile.residue
    profile.left_periodic profile.right_periodic
    profile.left_nonempty profile.right_nonempty r hr hloads

/-- If a cap vector satisfies every cross-root load inequality, then all
smaller positive rate vectors have the same ordinary source. -/
theorem WeakSevenCyclicProfile.schedulable_of_caps
    (profile : WeakSevenCyclicProfile) {r cap : Fin 7 → ℝ}
    (hr : ∀ i, 0 < r i)
    (hcap : ∀ i, r i ≤ cap i)
    (hloads : ∀ i j, profile.side i → ¬ profile.side j →
      (profile.period i : ℝ) * cap i + (profile.period j : ℝ) * cap j ≤ 1) :
    SchedulableRates r := by
  apply profile.schedulable_of_pair_loads hr
  intro i j hi hj
  have hpi : (0 : ℝ) ≤ profile.period i := by
    exact_mod_cast (profile.period_pos i).le
  have hpj : (0 : ℝ) ≤ profile.period j := by
    exact_mod_cast (profile.period_pos j).le
  calc
    (profile.period i : ℝ) * r i + (profile.period j : ℝ) * r j ≤
        (profile.period i : ℝ) * cap i + (profile.period j : ℝ) * cap j :=
      add_le_add (mul_le_mul_of_nonneg_left (hcap i) hpi)
        (mul_le_mul_of_nonneg_left (hcap j) hpj)
    _ ≤ 1 := hloads i j hi hj

/-- Transport the rate labels of a cyclic profile by an equivalence.  This is
used when the marked role is inserted at rank one. -/
theorem WeakSevenCyclicProfile.schedulable_of_relabelled_pair_loads
    (profile : WeakSevenCyclicProfile) (e : Fin 7 ≃ Fin 7)
    {r : Fin 7 → ℝ}
    (hr : ∀ i, 0 < r i)
    (hloads : ∀ i j, profile.side (e.symm i) →
      ¬ profile.side (e.symm j) →
      (profile.period (e.symm i) : ℝ) * r i +
        (profile.period (e.symm j) : ℝ) * r j ≤ 1) :
    SchedulableRates r := by
  apply SchedulableRates.relabel e
  apply profile.schedulable_of_pair_loads (fun i => hr (e i))
  intro i j hi hj
  have hii : e.symm (e i) = i := e.symm_apply_apply i
  have hij : e.symm (e j) = j := e.symm_apply_apply j
  simpa [hii, hij] using hloads (e i) (e j) (by simpa [hii] using hi)
    (by simpa [hij] using hj)

/-- Cap-box version of the role-relabelled source adapter. -/
theorem WeakSevenCyclicProfile.schedulable_of_relabelled_caps
    (profile : WeakSevenCyclicProfile) (e : Fin 7 ≃ Fin 7)
    {r cap : Fin 7 → ℝ}
    (hr : ∀ i, 0 < r i)
    (hcap : ∀ i, r i ≤ cap i)
    (hloads : ∀ i j, profile.side (e.symm i) →
      ¬ profile.side (e.symm j) →
      (profile.period (e.symm i) : ℝ) * cap i +
        (profile.period (e.symm j) : ℝ) * cap j ≤ 1) :
    SchedulableRates r := by
  apply profile.schedulable_of_relabelled_pair_loads e hr
  intro i j hi hj
  have hpi : (0 : ℝ) ≤ profile.period (e.symm i) := by
    exact_mod_cast (profile.period_pos (e.symm i)).le
  have hpj : (0 : ℝ) ≤ profile.period (e.symm j) := by
    exact_mod_cast (profile.period_pos (e.symm j)).le
  calc
    (profile.period (e.symm i) : ℝ) * r i +
        (profile.period (e.symm j) : ℝ) * r j ≤
      (profile.period (e.symm i) : ℝ) * cap i +
        (profile.period (e.symm j) : ℝ) * cap j :=
      add_le_add (mul_le_mul_of_nonneg_left (hcap i) hpi)
        (mul_le_mul_of_nonneg_left (hcap j) hpj)
    _ ≤ 1 := hloads i j hi hj

/-! The following literal cycles are the seven distinct inherited profiles.
Several marked-second source boxes are relabelings of these same cycles. -/

def ws7CyclicLeft49 : List (Fin 7) := [0, 1, 4, 0, 1, 5]
def ws7CyclicRight49 : List (Fin 7) := [2, 3, 6]
def ws7CyclicSide49 (i : Fin 7) : Prop :=
  i.val = 0 ∨ i.val = 1 ∨ i.val = 4 ∨ i.val = 5
def ws7CyclicPeriod49 (i : Fin 7) : ℤ :=
  if i.val = 0 then 3 else if i.val = 1 then 3 else
  if i.val = 4 then 6 else if i.val = 5 then 6 else 3
def ws7CyclicResidue49 (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else if i.val = 1 then 1 else
  if i.val = 2 then 0 else if i.val = 3 then 1 else
  if i.val = 4 then 2 else if i.val = 5 then 5 else 2

private theorem ws7_cycle_disjoint (left right : List (Fin 7))
    (h : ∀ x, x ∈ left → x ∈ right → False) : List.Disjoint left right := by
  apply List.disjoint_left.mpr
  exact h

def ws7CyclicProfile49 : WeakSevenCyclicProfile where
  left := ws7CyclicLeft49
  right := ws7CyclicRight49
  side := ws7CyclicSide49
  period := ws7CyclicPeriod49
  residue := ws7CyclicResidue49
  left_ne := by decide
  right_ne := by decide
  disjoint := ws7_cycle_disjoint _ _ (by
    intro x hx hy
    fin_cases x <;> simp [ws7CyclicLeft49, ws7CyclicRight49] at hx hy)
  left_nonempty := ⟨0, by norm_num [ws7CyclicSide49]⟩
  right_nonempty := ⟨2, by norm_num [ws7CyclicSide49]⟩
  period_pos := by intro i; fin_cases i <;> norm_num [ws7CyclicPeriod49]
  left_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide49, ws7CyclicPeriod49, ws7CyclicResidue49,
        ws7CyclicLeft49, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide
  right_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide49, ws7CyclicPeriod49, ws7CyclicResidue49,
        ws7CyclicRight49, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide

def ws7CyclicLeft50 : List (Fin 7) :=
  [0, 2, 5, 3, 0, 4, 6, 2, 0, 3, 5, 4, 0, 2, 6, 3,
   0, 4, 5, 2, 0, 3, 6, 4]
def ws7CyclicRight50 : List (Fin 7) := [1]
def ws7CyclicSide50 (i : Fin 7) : Prop :=
  i.val = 0 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6
def ws7CyclicPeriod50 (i : Fin 7) : ℤ :=
  if i.val = 0 then 4 else if i.val = 1 then 1 else
  if i.val = 2 then 6 else if i.val = 3 then 6 else
  if i.val = 4 then 6 else if i.val = 5 then 8 else 8
def ws7CyclicResidue50 (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else if i.val = 1 then 0 else
  if i.val = 2 then 1 else if i.val = 3 then 3 else
  if i.val = 4 then 5 else if i.val = 5 then 2 else 6

def ws7CyclicProfile50 : WeakSevenCyclicProfile where
  left := ws7CyclicLeft50
  right := ws7CyclicRight50
  side := ws7CyclicSide50
  period := ws7CyclicPeriod50
  residue := ws7CyclicResidue50
  left_ne := by decide
  right_ne := by decide
  disjoint := ws7_cycle_disjoint _ _ (by
    intro x hx hy
    fin_cases x <;> simp [ws7CyclicLeft50, ws7CyclicRight50] at hx hy)
  left_nonempty := ⟨0, by norm_num [ws7CyclicSide50]⟩
  right_nonempty := ⟨1, by norm_num [ws7CyclicSide50]⟩
  period_pos := by intro i; fin_cases i <;> norm_num [ws7CyclicPeriod50]
  left_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide50, ws7CyclicPeriod50, ws7CyclicResidue50,
        ws7CyclicLeft50, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide
  right_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide50, ws7CyclicPeriod50, ws7CyclicResidue50,
        ws7CyclicRight50, SevenStreams.ListIndexPeriodic] at hi ⊢

def ws7CyclicLeft51 : List (Fin 7) :=
  [0, 1, 4, 2, 0, 3, 5, 1, 0, 2, 4, 3,
   0, 1, 5, 2, 0, 3, 4, 1, 0, 2, 5, 3]
def ws7CyclicRight51 : List (Fin 7) := [6]
def ws7CyclicSide51 (i : Fin 7) : Prop :=
  i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5
def ws7CyclicPeriod51 (i : Fin 7) : ℤ :=
  if i.val = 0 then 4 else if i.val = 1 then 6 else
  if i.val = 2 then 6 else if i.val = 3 then 6 else
  if i.val = 4 then 8 else if i.val = 5 then 8 else 1
def ws7CyclicResidue51 (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else if i.val = 1 then 1 else
  if i.val = 2 then 3 else if i.val = 3 then 5 else
  if i.val = 4 then 2 else if i.val = 5 then 6 else 0

def ws7CyclicProfile51 : WeakSevenCyclicProfile where
  left := ws7CyclicLeft51
  right := ws7CyclicRight51
  side := ws7CyclicSide51
  period := ws7CyclicPeriod51
  residue := ws7CyclicResidue51
  left_ne := by decide
  right_ne := by decide
  disjoint := ws7_cycle_disjoint _ _ (by
    intro x hx hy
    fin_cases x <;> simp [ws7CyclicLeft51, ws7CyclicRight51] at hx hy)
  left_nonempty := ⟨0, by norm_num [ws7CyclicSide51]⟩
  right_nonempty := ⟨6, by norm_num [ws7CyclicSide51]⟩
  period_pos := by intro i; fin_cases i <;> norm_num [ws7CyclicPeriod51]
  left_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide51, ws7CyclicPeriod51, ws7CyclicResidue51,
        ws7CyclicLeft51, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide
  right_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide51, ws7CyclicPeriod51, ws7CyclicResidue51,
        ws7CyclicRight51, SevenStreams.ListIndexPeriodic] at hi ⊢

def ws7CyclicLeft69 : List (Fin 7) := [0, 3, 1, 5, 0, 4, 1, 6]
def ws7CyclicRight69 : List (Fin 7) := [2]
def ws7CyclicSide69 (i : Fin 7) : Prop :=
  i.val = 0 ∨ i.val = 1 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6
def ws7CyclicPeriod69 (i : Fin 7) : ℤ :=
  if i.val = 0 then 4 else if i.val = 1 then 4 else
  if i.val = 2 then 1 else 8
def ws7CyclicResidue69 (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else if i.val = 1 then 2 else
  if i.val = 2 then 0 else if i.val = 3 then 1 else
  if i.val = 4 then 5 else if i.val = 5 then 3 else 7

def ws7CyclicProfile69 : WeakSevenCyclicProfile where
  left := ws7CyclicLeft69
  right := ws7CyclicRight69
  side := ws7CyclicSide69
  period := ws7CyclicPeriod69
  residue := ws7CyclicResidue69
  left_ne := by decide
  right_ne := by decide
  disjoint := ws7_cycle_disjoint _ _ (by
    intro x hx hy
    fin_cases x <;> simp [ws7CyclicLeft69, ws7CyclicRight69] at hx hy)
  left_nonempty := ⟨0, by norm_num [ws7CyclicSide69]⟩
  right_nonempty := ⟨2, by norm_num [ws7CyclicSide69]⟩
  period_pos := by intro i; fin_cases i <;> norm_num [ws7CyclicPeriod69]
  left_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide69, ws7CyclicPeriod69, ws7CyclicResidue69,
        ws7CyclicLeft69, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide
  right_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide69, ws7CyclicPeriod69, ws7CyclicResidue69,
        ws7CyclicRight69, SevenStreams.ListIndexPeriodic] at hi ⊢

def ws7CyclicLeft109 : List (Fin 7) :=
  [0, 1, 5, 2, 0, 3, 6, 1, 0, 2, 5, 3,
   0, 1, 6, 2, 0, 3, 5, 1, 0, 2, 6, 3]
def ws7CyclicRight109 : List (Fin 7) := [4]
def ws7CyclicSide109 (i : Fin 7) : Prop :=
  i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 6
def ws7CyclicPeriod109 (i : Fin 7) : ℤ :=
  if i.val = 0 then 4 else if i.val = 1 then 6 else
  if i.val = 2 then 6 else if i.val = 3 then 6 else
  if i.val = 4 then 1 else 8
def ws7CyclicResidue109 (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else if i.val = 1 then 1 else
  if i.val = 2 then 3 else if i.val = 3 then 5 else
  if i.val = 4 then 0 else if i.val = 5 then 2 else 6

def ws7CyclicProfile109 : WeakSevenCyclicProfile where
  left := ws7CyclicLeft109
  right := ws7CyclicRight109
  side := ws7CyclicSide109
  period := ws7CyclicPeriod109
  residue := ws7CyclicResidue109
  left_ne := by decide
  right_ne := by decide
  disjoint := ws7_cycle_disjoint _ _ (by
    intro x hx hy
    fin_cases x <;> simp [ws7CyclicLeft109, ws7CyclicRight109] at hx hy)
  left_nonempty := ⟨0, by norm_num [ws7CyclicSide109]⟩
  right_nonempty := ⟨4, by norm_num [ws7CyclicSide109]⟩
  period_pos := by intro i; fin_cases i <;> norm_num [ws7CyclicPeriod109]
  left_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide109, ws7CyclicPeriod109, ws7CyclicResidue109,
        ws7CyclicLeft109, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide
  right_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide109, ws7CyclicPeriod109, ws7CyclicResidue109,
        ws7CyclicRight109, SevenStreams.ListIndexPeriodic] at hi ⊢

def ws7CyclicLeft170 : List (Fin 7) := [0, 1, 5, 0, 1, 6]
def ws7CyclicRight170 : List (Fin 7) := [2, 3, 4]
def ws7CyclicSide170 (i : Fin 7) : Prop :=
  i.val = 0 ∨ i.val = 1 ∨ i.val = 5 ∨ i.val = 6
def ws7CyclicPeriod170 (i : Fin 7) : ℤ :=
  if i.val = 0 then 3 else if i.val = 1 then 3 else
  if i.val = 5 then 6 else if i.val = 6 then 6 else 3
def ws7CyclicResidue170 (i : Fin 7) : ℤ :=
  if i.val = 0 then 0 else if i.val = 1 then 1 else
  if i.val = 2 then 0 else if i.val = 3 then 1 else
  if i.val = 4 then 2 else if i.val = 5 then 2 else 5

def ws7CyclicProfile170 : WeakSevenCyclicProfile where
  left := ws7CyclicLeft170
  right := ws7CyclicRight170
  side := ws7CyclicSide170
  period := ws7CyclicPeriod170
  residue := ws7CyclicResidue170
  left_ne := by decide
  right_ne := by decide
  disjoint := ws7_cycle_disjoint _ _ (by
    intro x hx hy
    fin_cases x <;> simp [ws7CyclicLeft170, ws7CyclicRight170] at hx hy)
  left_nonempty := ⟨0, by norm_num [ws7CyclicSide170]⟩
  right_nonempty := ⟨2, by norm_num [ws7CyclicSide170]⟩
  period_pos := by intro i; fin_cases i <;> norm_num [ws7CyclicPeriod170]
  left_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide170, ws7CyclicPeriod170, ws7CyclicResidue170,
        ws7CyclicLeft170, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide
  right_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide170, ws7CyclicPeriod170, ws7CyclicResidue170,
        ws7CyclicRight170, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide

def ws7CyclicLeft171 : List (Fin 7) := [0, 1]
def ws7CyclicRight171 : List (Fin 7) := [2, 3, 4, 5, 6]
def ws7CyclicSide171 (i : Fin 7) : Prop := i.val = 0 ∨ i.val = 1
def ws7CyclicPeriod171 (i : Fin 7) : ℤ := if i.val ≤ 1 then 2 else 5
def ws7CyclicResidue171 (i : Fin 7) : ℤ :=
  if i.val ≤ 1 then (i.val : ℤ) else (i.val : ℤ) - 2

def ws7CyclicProfile171 : WeakSevenCyclicProfile where
  left := ws7CyclicLeft171
  right := ws7CyclicRight171
  side := ws7CyclicSide171
  period := ws7CyclicPeriod171
  residue := ws7CyclicResidue171
  left_ne := by decide
  right_ne := by decide
  disjoint := ws7_cycle_disjoint _ _ (by
    intro x hx hy
    fin_cases x <;> simp [ws7CyclicLeft171, ws7CyclicRight171] at hx hy)
  left_nonempty := ⟨0, by norm_num [ws7CyclicSide171]⟩
  right_nonempty := ⟨2, by norm_num [ws7CyclicSide171]⟩
  period_pos := by intro i; fin_cases i <;> norm_num [ws7CyclicPeriod171]
  left_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide171, ws7CyclicPeriod171, ws7CyclicResidue171,
        ws7CyclicLeft171, SevenStreams.ListIndexPeriodic] at hi ⊢
  right_periodic := by
    intro i hi
    fin_cases i <;>
      simp [ws7CyclicSide171, ws7CyclicPeriod171, ws7CyclicResidue171,
        ws7CyclicRight171, SevenStreams.ListIndexPeriodic] at hi ⊢
    all_goals
      intro k
      fin_cases k <;> norm_num <;> decide

/-! The marked-second inherited leaves use these source profiles after
inserting the mark at rank one. Their frozen caps are listed by source ID
4--14 (IDs 0--3 in that cover are literal words). -/

def ws7SecondCycleProfile (sid : Fin 15) : WeakSevenCyclicProfile :=
  match sid.val with
  | 4 => ws7CyclicProfile171
  | 5 | 6 | 7 | 9 => ws7CyclicProfile49
  | 8 | 10 => ws7CyclicProfile69
  | 11 | 12 | 13 => ws7CyclicProfile49
  | 14 => ws7CyclicProfile170
  | _ => ws7CyclicProfile49

def ws7SecondMarkRankEquiv : Fin 7 ≃ Fin 7 where
  toFun i := match i.val with
    | 2 => 4
    | 3 => 5
    | 4 => 2
    | 5 => 3
    | _ => i
  invFun i := match i.val with
    | 2 => 4
    | 3 => 5
    | 4 => 2
    | 5 => 3
    | _ => i
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp]
theorem ws7SecondMarkRankEquiv_symm_apply (i : Fin 7) :
    ws7SecondMarkRankEquiv.symm i = ws7SecondMarkRankEquiv i := rfl

def ws7SecondCycleEquiv (sid : Fin 15) : Fin 7 ≃ Fin 7 :=
  match sid.val with
  | 5 | 6 | 7 | 9 => ws7SecondMarkRankEquiv
  | _ => Equiv.refl (Fin 7)

noncomputable def ws7SecondCycleCaps (sid : Fin 15) : Fin 7 → ℝ := fun i =>
  match sid.val with
  | 4 => match i.val with
    | 0 => (162 : ℝ) / 689
    | 1 => (146 : ℝ) / 689
    | _ => (73 : ℝ) / 689
  | 5 => match i.val with
    | 0 => (124660 : ℝ) / 542367
    | 1 => (112258 : ℝ) / 542367
    | 2 => (59770 : ℝ) / 542367
    | _ => (56129 : ℝ) / 542367
  | 6 => match i.val with
    | 0 => (10857200 : ℝ) / 47230299
    | 1 => (9772466 : ℝ) / 47230299
    | 2 => (5389160 : ℝ) / 47230299
    | _ => (4886233 : ℝ) / 47230299
  | 7 => match i.val with
    | 0 => (8316733826 : ℝ) / 36179666007
    | 1 => (2495436562 : ℝ) / 12059888669
    | 2 => (1323923842 : ℝ) / 12059888669
    | 3 => (3879780526 : ℝ) / 36179666007
    | _ => (1247718281 : ℝ) / 12059888669
  | 8 => match i.val with
    | 0 | 1 => (83 : ℝ) / 379
    | 2 => (47 : ℝ) / 379
    | _ => (83 : ℝ) / 758
  | 9 => match i.val with
    | 0 => (352893426530 : ℝ) / 1586876332767
    | 1 => (1635980674 : ℝ) / 8055209811
    | 2 => (933539800 : ℝ) / 8055209811
    | _ => (817990337 : ℝ) / 8055209811
  | 10 => match i.val with
    | 0 | 1 => (10339 : ℝ) / 47807
    | 2 => (6451 : ℝ) / 47807
    | _ => (10339 : ℝ) / 95614
  | 11 => match i.val with
    | 0 | 1 => (136053119 : ℝ) / 661424034
    | 2 => (84421559 : ℝ) / 661424034
    | 3 => (294532961 : ℝ) / 2645696136
    | _ => (136053119 : ℝ) / 1322848068
  | 12 => match i.val with
    | 0 | 1 => (4318 : ℝ) / 20223
    | 2 => (2423 : ℝ) / 20223
    | 3 => (19109 : ℝ) / 161784
    | _ => (2159 : ℝ) / 20223
  | 13 => match i.val with
    | 0 | 1 => (89368829179067 : ℝ) / 428956453720962
    | 2 => (53616655394587 : ℝ) / 428956453720962
    | 3 => (24915904083856 : ℝ) / 214478226860481
    | _ => (89368829179067 : ℝ) / 857912907441924
  | 14 => match i.val with
    | 0 | 1 => (1926518 : ℝ) / 9004269
    | 2 => (1074905 : ℝ) / 9004269
    | 3 => (8475655 : ℝ) / 72034152
    | 4 => (344405 : ℝ) / 3001423
    | _ => (963259 : ℝ) / 9004269
  | _ => 0

set_option maxHeartbeats 10000000 in
set_option linter.unusedSimpArgs false in
/-- The explicit inherited cap vectors satisfy every paired load for their
assigned cyclic source. This finite rational check is independent of the
polytope tree's source selection. -/
theorem ws7SecondCycleCaps_loads (sid : Fin 15) (hsid : 4 ≤ sid.val) :
    ∀ i j, (ws7SecondCycleProfile sid).side
        ((ws7SecondCycleEquiv sid).symm i) →
      ¬ (ws7SecondCycleProfile sid).side
        ((ws7SecondCycleEquiv sid).symm j) →
      ((ws7SecondCycleProfile sid).period
          ((ws7SecondCycleEquiv sid).symm i) : ℝ) * ws7SecondCycleCaps sid i +
        ((ws7SecondCycleProfile sid).period
          ((ws7SecondCycleEquiv sid).symm j) : ℝ) * ws7SecondCycleCaps sid j ≤ 1 := by
  fin_cases sid <;> norm_num at hsid
  all_goals
    intro i j hi hj
    fin_cases i <;> fin_cases j <;>
      simp [ws7SecondCycleProfile, ws7SecondCycleEquiv, ws7SecondCycleCaps,
        ws7SecondMarkRankEquiv,
        ws7CyclicProfile49, ws7CyclicProfile69, ws7CyclicProfile170,
        ws7CyclicProfile171, ws7CyclicSide49, ws7CyclicSide69,
        ws7CyclicSide170, ws7CyclicSide171, ws7CyclicPeriod49,
        ws7CyclicPeriod69, ws7CyclicPeriod170, ws7CyclicPeriod171] at hi hj ⊢ <;>
      norm_num [ws7SecondCycleCaps, ws7CyclicPeriod49, ws7CyclicPeriod69,
        ws7CyclicPeriod170, ws7CyclicPeriod171]

/-- The checked cap source for each marked-second cyclic source ID. -/
theorem ws7SecondCycleSchedulable (sid : Fin 15) (hsid : 4 ≤ sid.val)
    {r : Fin 7 → ℝ} (hr : ∀ i, 0 < r i)
    (hcap : ∀ i, r i ≤ ws7SecondCycleCaps sid i) :
    SchedulableRates r :=
  (ws7SecondCycleProfile sid).schedulable_of_relabelled_caps
    (ws7SecondCycleEquiv sid) hr hcap (ws7SecondCycleCaps_loads sid hsid)

end RealPinwheel
