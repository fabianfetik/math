import CorralFormalization.Constructions.Optimal.Even.Prefixes

namespace CorralFormalization

/-- The smaller projection modulus in the paper's even construction. -/
def evenConstructionPeriod (k : ℕ) : ℕ := 8 * k - 2

def evenConstructionE (k j : ℕ) : ℕ := (j * (4 * k)) % evenConstructionPeriod k

def evenConstructionO (k j : ℕ) : ℕ :=
  (evenConstructionE k j + evenConstructionLowAt k j) % evenConstructionPeriod k

/-- The two displayed formulas for the pair-boundary prefixes. -/
theorem evenConstructionE_even (k r : ℕ) (hk : 1 ≤ k) (hr : r < k) :
    evenConstructionE k (2 * r) = 2 * r := by
  unfold evenConstructionE evenConstructionPeriod
  have hbase : 8 * k = (8 * k - 2) + 2 := by omega
  have heq : (2 * r) * (4 * k) = r * (8 * k - 2) + 2 * r := by
    calc
      _ = r * (8 * k) := by ring
      _ = r * ((8 * k - 2) + 2) := congrArg (fun z => r * z) hbase
      _ = _ := by ring
  rw [heq, mul_add_mod_eq r (2 * r) (8 * k - 2) (by omega)]

theorem evenConstructionE_odd (k r : ℕ) (hk : 1 ≤ k) (hr : r < k) :
    evenConstructionE k (2 * r + 1) = 4 * k + 2 * r := by
  unfold evenConstructionE evenConstructionPeriod
  have hbase : 8 * k = (8 * k - 2) + 2 := by omega
  have heq : (2 * r + 1) * (4 * k) = r * (8 * k - 2) + (4 * k + 2 * r) := by
    calc
      _ = r * (8 * k) + 4 * k := by ring
      _ = r * ((8 * k - 2) + 2) + 4 * k := congrArg (fun z => r * z + 4 * k) hbase
      _ = _ := by ring
  rw [heq, mul_add_mod_eq r (4 * k + 2 * r) (8 * k - 2) (by omega)]

/-- The two odd intermediate-prefix formulas for the first low block. -/
theorem evenConstructionO_first_even (k r : ℕ) (hk : 1 ≤ k) (hj : 2 * r < k) :
    evenConstructionO k (2 * r) = 2 * (k - 1 - r) + 1 := by
  unfold evenConstructionO evenConstructionLowAt
  rw [evenConstructionE_even k r hk (by omega), if_pos hj]
  have heq : 2 * r + (2 * k - 1 - 2 * (2 * r)) = 2 * (k - 1 - r) + 1 := by omega
  rw [heq, Nat.mod_eq_of_lt]
  unfold evenConstructionPeriod
  omega

theorem evenConstructionO_first_odd (k r : ℕ) (hk : 1 ≤ k) (hj : 2 * r + 1 < k) :
    evenConstructionO k (2 * r + 1) = 2 * (3 * k - 2 - r) + 1 := by
  unfold evenConstructionO evenConstructionLowAt
  rw [evenConstructionE_odd k r hk (by omega), if_pos hj]
  have heq : 4 * k + 2 * r + (2 * k - 1 - 2 * (2 * r + 1)) =
      2 * (3 * k - 2 - r) + 1 := by omega
  rw [heq, Nat.mod_eq_of_lt]
  unfold evenConstructionPeriod
  omega

/-- The two even intermediate-prefix formulas for the second low block. -/
theorem evenConstructionO_second_even (k r : ℕ) (hk : 1 ≤ k)
    (hj0 : k ≤ 2 * r) (hj1 : 2 * r < 2 * k - 1) :
    evenConstructionO k (2 * r) = 2 * (2 * k - 1 - r) := by
  unfold evenConstructionO evenConstructionLowAt
  rw [evenConstructionE_even k r hk (by omega), if_neg (by omega : ¬ 2 * r < k)]
  have heq : 2 * r + (4 * k - 2 - 2 * (2 * r)) = 2 * (2 * k - 1 - r) := by omega
  rw [heq, Nat.mod_eq_of_lt]
  unfold evenConstructionPeriod
  omega

theorem evenConstructionO_second_odd (k r : ℕ) (hk : 1 ≤ k)
    (hj0 : k ≤ 2 * r + 1) (hj1 : 2 * r + 1 < 2 * k - 1) :
    evenConstructionO k (2 * r + 1) = 2 * (4 * k - 2 - r) := by
  unfold evenConstructionO evenConstructionLowAt
  rw [evenConstructionE_odd k r hk (by omega), if_neg (by omega : ¬ 2 * r + 1 < k)]
  have heq : 4 * k + 2 * r + (4 * k - 2 - 2 * (2 * r + 1)) =
      2 * (4 * k - 2 - r) := by omega
  rw [heq, Nat.mod_eq_of_lt]
  unfold evenConstructionPeriod
  omega

/-- The projected proper prefix at a pair boundary. -/
theorem evenConstructionProjectedPrefix_even (k t : ℕ) (hk : 1 ≤ k)
    (ht : t ≤ 2 * k - 1) :
    evenConstructionPrefix k (2 * t) % evenConstructionPeriod k = evenConstructionE k t := by
  rw [evenConstructionPrefix_even k t hk ht]
  rfl

/-- The projected proper prefix inside a pair. -/
theorem evenConstructionProjectedPrefix_odd (k t : ℕ) (hk : 1 ≤ k)
    (ht : t < 2 * k - 1) :
    evenConstructionPrefix k (2 * t + 1) % evenConstructionPeriod k = evenConstructionO k t := by
  rw [evenConstructionPrefix_odd k t hk ht]
  unfold evenConstructionO evenConstructionE
  exact (Nat.mod_add_mod (t * (4 * k)) (evenConstructionPeriod k) (evenConstructionLowAt k t)).symm

/-- The actual projection of all proper prefixes of the printed word. -/
def evenConstructionProjectedSet (k : ℕ) : Finset ℕ :=
  (Finset.range (4 * k - 1)).image (fun j => evenConstructionPrefix k j % evenConstructionPeriod k)

/-- Every projected site is exactly one of the printed E/O families, and
every indexed family member occurs as an actual proper prefix. -/
theorem evenConstructionProjectedSet_mem (k x : ℕ) (hk : 1 ≤ k) :
    x ∈ evenConstructionProjectedSet k ↔
      (∃ t, t < 2 * k ∧ x = evenConstructionE k t) ∨
      (∃ t, t < 2 * k - 1 ∧ x = evenConstructionO k t) := by
  unfold evenConstructionProjectedSet
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hval⟩
    by_cases heven : j % 2 = 0
    · let t := j / 2
      have hjform : j = 2 * t := by dsimp [t]; omega
      have ht : t < 2 * k := by dsimp [t]; omega
      left
      refine ⟨t, ht, ?_⟩
      rw [hjform, evenConstructionProjectedPrefix_even k t hk (by omega)] at hval
      exact hval.symm
    · let t := (j - 1) / 2
      have hjform : j = 2 * t + 1 := by dsimp [t]; omega
      have ht : t < 2 * k - 1 := by dsimp [t]; omega
      right
      refine ⟨t, ht, ?_⟩
      rw [hjform, evenConstructionProjectedPrefix_odd k t hk ht] at hval
      exact hval.symm
  · rintro (⟨t, ht, hx⟩ | ⟨t, ht, hx⟩)
    · refine ⟨2 * t, by omega, ?_⟩
      rw [evenConstructionProjectedPrefix_even k t hk (by omega)]
      exact hx.symm
    · refine ⟨2 * t + 1, by omega, ?_⟩
      rw [evenConstructionProjectedPrefix_odd k t hk ht]
      exact hx.symm

/-- Normalized even and odd families appearing in the displayed E/O
calculation, before collecting their adjacent intervals. -/
def evenConstructionXFamilies (k u : ℕ) : Prop :=
  u < k ∨ (2 * k ≤ u ∧ u < 3 * k) ∨
    (∃ r, k ≤ 2 * r ∧ 2 * r < 2 * k - 1 ∧ u = 2 * k - 1 - r) ∨
    (∃ r, k ≤ 2 * r + 1 ∧ 2 * r + 1 < 2 * k - 1 ∧ u = 4 * k - 2 - r)

def evenConstructionYFamilies (k u : ℕ) : Prop :=
  (∃ r, 2 * r < k ∧ u = k - 1 - r) ∨
    (∃ r, 2 * r + 1 < k ∧ u = 3 * k - 2 - r)

/-- The actual projected prefix set has exactly the normalized even and
odd families calculated from the paper's E/O formulas. -/
theorem evenConstructionProjectedSet_normalized (k x : ℕ) (hk : 1 ≤ k) :
    x ∈ evenConstructionProjectedSet k ↔
      (∃ u, x = 2 * u ∧ evenConstructionXFamilies k u) ∨
      (∃ u, x = 2 * u + 1 ∧ evenConstructionYFamilies k u) := by
  rw [evenConstructionProjectedSet_mem k x hk]
  constructor
  · rintro (⟨t, ht, hx⟩ | ⟨t, ht, hx⟩)
    · by_cases heven : t % 2 = 0
      · let r := t / 2
        have htform : t = 2 * r := by dsimp [r]; omega
        have hr : r < k := by dsimp [r]; omega
        rw [htform, evenConstructionE_even k r hk hr] at hx
        left
        exact ⟨r, hx, Or.inl hr⟩
      · let r := (t - 1) / 2
        have htform : t = 2 * r + 1 := by dsimp [r]; omega
        have hr : r < k := by dsimp [r]; omega
        rw [htform, evenConstructionE_odd k r hk hr] at hx
        left
        refine ⟨2 * k + r, by omega, Or.inr (Or.inl (by omega))⟩
    · by_cases hfirst : t < k
      · by_cases heven : t % 2 = 0
        · let r := t / 2
          have htform : t = 2 * r := by dsimp [r]; omega
          have hr : 2 * r < k := by omega
          rw [htform, evenConstructionO_first_even k r hk hr] at hx
          right
          exact ⟨k - 1 - r, hx, Or.inl ⟨r, hr, rfl⟩⟩
        · let r := (t - 1) / 2
          have htform : t = 2 * r + 1 := by dsimp [r]; omega
          have hr : 2 * r + 1 < k := by omega
          rw [htform, evenConstructionO_first_odd k r hk hr] at hx
          right
          exact ⟨3 * k - 2 - r, hx, Or.inr ⟨r, hr, rfl⟩⟩
      · by_cases heven : t % 2 = 0
        · let r := t / 2
          have htform : t = 2 * r := by dsimp [r]; omega
          have hr0 : k ≤ 2 * r := by omega
          have hr1 : 2 * r < 2 * k - 1 := by omega
          rw [htform, evenConstructionO_second_even k r hk hr0 hr1] at hx
          left
          exact ⟨2 * k - 1 - r, hx, Or.inr (Or.inr (Or.inl ⟨r, hr0, hr1, rfl⟩))⟩
        · let r := (t - 1) / 2
          have htform : t = 2 * r + 1 := by dsimp [r]; omega
          have hr0 : k ≤ 2 * r + 1 := by omega
          have hr1 : 2 * r + 1 < 2 * k - 1 := by omega
          rw [htform, evenConstructionO_second_odd k r hk hr0 hr1] at hx
          left
          exact ⟨4 * k - 2 - r, hx, Or.inr (Or.inr (Or.inr ⟨r, hr0, hr1, rfl⟩))⟩
  · rintro (⟨u, hx, hX⟩ | ⟨u, hx, hY⟩)
    · unfold evenConstructionXFamilies at hX
      rcases hX with hr | ⟨hlo, hhi⟩ | ⟨r, hr0, hr1, hu⟩ | ⟨r, hr0, hr1, hu⟩
      · left
        refine ⟨2 * u, by omega, ?_⟩
        rw [evenConstructionE_even k u hk hr]
        exact hx
      · let r := u - 2 * k
        have hr : r < k := by dsimp [r]; omega
        left
        refine ⟨2 * r + 1, by omega, ?_⟩
        rw [evenConstructionE_odd k r hk hr]
        dsimp [r] at *
        omega
      · right
        refine ⟨2 * r, hr1, ?_⟩
        rw [evenConstructionO_second_even k r hk hr0 hr1]
        omega
      · right
        refine ⟨2 * r + 1, hr1, ?_⟩
        rw [evenConstructionO_second_odd k r hk hr0 hr1]
        omega
    · unfold evenConstructionYFamilies at hY
      rcases hY with ⟨r, hr, hu⟩ | ⟨r, hr, hu⟩
      · right
        refine ⟨2 * r, by omega, ?_⟩
        rw [evenConstructionO_first_even k r hk hr]
        omega
      · right
        refine ⟨2 * r + 1, by omega, ?_⟩
        rw [evenConstructionO_first_odd k r hk hr]
        omega

end CorralFormalization
