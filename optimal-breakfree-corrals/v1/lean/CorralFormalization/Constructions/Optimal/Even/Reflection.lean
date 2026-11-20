import CorralFormalization.Constructions.Optimal.Even.Intervals

set_option maxHeartbeats 0

namespace CorralFormalization

/-- The paper's odd reflection parameter and its normalized half. -/
def evenConstructionShift (k : ℕ) : ℕ :=
  if k % 2 = 0 then k - 1 else 5 * k - 2

def evenConstructionHalfShift (k : ℕ) : ℕ :=
  if k % 2 = 0 then k / 2 - 1 else 5 * (k / 2) + 1

theorem evenConstructionShift_eq (k : ℕ) (hk : 1 ≤ k) :
    evenConstructionShift k = 2 * evenConstructionHalfShift k + 1 := by
  unfold evenConstructionShift evenConstructionHalfShift
  split_ifs <;> omega

theorem evenConstructionHalfShift_lt (k : ℕ) (hk : 1 ≤ k) :
    evenConstructionHalfShift k < 4 * k - 1 := by
  unfold evenConstructionHalfShift
  split_ifs <;> omega

/-- Reflection of a normalized coordinate on the `4k-1` cycle. -/
def evenConstructionReflectNorm (k u : ℕ) : ℕ :=
  (evenConstructionHalfShift k + (4 * k - 1) - u) % (4 * k - 1)

theorem evenConstructionReflectNorm_formula (k u : ℕ) (hk : 1 ≤ k) (hu : u < 4 * k - 1) :
    evenConstructionReflectNorm k u =
      if u ≤ evenConstructionHalfShift k then evenConstructionHalfShift k - u
      else evenConstructionHalfShift k + (4 * k - 1) - u := by
  have hc := evenConstructionHalfShift_lt k hk
  unfold evenConstructionReflectNorm
  split_ifs with h
  · have heq : evenConstructionHalfShift k + (4 * k - 1) - u =
        (4 * k - 1) + (evenConstructionHalfShift k - u) := by omega
    rw [heq, Nat.add_mod]
    have hrem : evenConstructionHalfShift k - u < 4 * k - 1 := by omega
    simp [Nat.mod_eq_of_lt hrem]
  · have hrem : evenConstructionHalfShift k + (4 * k - 1) - u < 4 * k - 1 := by omega
    rw [Nat.mod_eq_of_lt hrem]

/-- The displayed reflection sends the odd normalized interval table to
the complement of the even table. -/
theorem evenConstructionX_reflection_complement (k u : ℕ) (hk : 1 ≤ k)
    (hu : u < 4 * k - 1) :
    evenConstructionXTable k u ↔ ¬ evenConstructionYTable k (evenConstructionReflectNorm k u) := by
  rw [evenConstructionReflectNorm_formula k u hk hu]
  unfold evenConstructionXTable evenConstructionYTable evenConstructionHalfShift
  split_ifs <;> simp_all <;> omega

/-- The same involution gives the complementary relation in the other
physical parity. -/
theorem evenConstructionY_reflection_complement (k u : ℕ) (hk : 1 ≤ k)
    (hu : u < 4 * k - 1) :
    evenConstructionYTable k u ↔ ¬ evenConstructionXTable k (evenConstructionReflectNorm k u) := by
  rw [evenConstructionReflectNorm_formula k u hk hu]
  unfold evenConstructionXTable evenConstructionYTable evenConstructionHalfShift
  split_ifs <;> simp_all <;> omega

/-- The physical reflection `x ↦ c-x` on the smaller cycle, using
canonical nonnegative representatives. -/
def evenConstructionReflect (k x : ℕ) : ℕ :=
  (evenConstructionShift k + evenConstructionPeriod k - x) % evenConstructionPeriod k

theorem evenConstructionPeriod_eq (k : ℕ) (hk : 1 ≤ k) :
    evenConstructionPeriod k = 2 * (4 * k - 1) := by
  unfold evenConstructionPeriod
  omega

theorem evenConstructionProjectedSet_even_mem (k u : ℕ) (hk : 1 ≤ k) :
    2 * u ∈ evenConstructionProjectedSet k ↔ evenConstructionXTable k u := by
  rw [evenConstructionProjectedSet_table k (2 * u) hk]
  constructor
  · rintro (⟨v, hv, hX⟩ | ⟨v, hv, hY⟩)
    · have : u = v := by omega
      simpa [this] using hX
    · omega
  · intro hX
    exact Or.inl ⟨u, rfl, hX⟩

theorem evenConstructionProjectedSet_odd_mem (k u : ℕ) (hk : 1 ≤ k) :
    2 * u + 1 ∈ evenConstructionProjectedSet k ↔ evenConstructionYTable k u := by
  rw [evenConstructionProjectedSet_table k (2 * u + 1) hk]
  constructor
  · rintro (⟨v, hv, hX⟩ | ⟨v, hv, hY⟩)
    · omega
    · have : u = v := by omega
      simpa [this] using hY
  · intro hY
    exact Or.inr ⟨u, rfl, hY⟩

/-- Reflection exchanges physical parity and acts on normalized
coordinates by `evenConstructionReflectNorm`. -/
theorem evenConstructionReflect_even (k u : ℕ) (hk : 1 ≤ k) (hu : u < 4 * k - 1) :
    evenConstructionReflect k (2 * u) = 2 * evenConstructionReflectNorm k u + 1 := by
  have hn : 0 < 4 * k - 1 := by omega
  have hp := evenConstructionPeriod_eq k hk
  have hc := evenConstructionShift_eq k hk
  have hc' := evenConstructionHalfShift_lt k hk
  unfold evenConstructionReflect evenConstructionReflectNorm
  rw [hp, hc]
  have hnum : (2 * evenConstructionHalfShift k + 1) + 2 * (4 * k - 1) - 2 * u =
      2 * (evenConstructionHalfShift k + (4 * k - 1) - u) + 1 := by omega
  rw [hnum, Nat.add_mod, Nat.mul_mod_mul_left]
  have hmod := Nat.mod_lt (evenConstructionHalfShift k + (4 * k - 1) - u) hn
  have hlt : 2 * ((evenConstructionHalfShift k + (4 * k - 1) - u) % (4 * k - 1)) + 1 <
      2 * (4 * k - 1) := by omega
  simp [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 1 < 2 * (4 * k - 1))]

theorem evenConstructionReflect_odd (k u : ℕ) (hk : 1 ≤ k) (hu : u < 4 * k - 1) :
    evenConstructionReflect k (2 * u + 1) = 2 * evenConstructionReflectNorm k u := by
  have hp := evenConstructionPeriod_eq k hk
  have hc := evenConstructionShift_eq k hk
  have hc' := evenConstructionHalfShift_lt k hk
  unfold evenConstructionReflect evenConstructionReflectNorm
  rw [hp, hc]
  have hnum : (2 * evenConstructionHalfShift k + 1) + 2 * (4 * k - 1) - (2 * u + 1) =
      2 * (evenConstructionHalfShift k + (4 * k - 1) - u) := by omega
  rw [hnum, Nat.mul_mod_mul_left]

/-- On every physical representative, membership in the actual projected
set is complementary to membership of its physical reflection. -/
theorem evenConstructionProjected_reflection_complement (k x : ℕ) (hk : 1 ≤ k)
    (hx : x < evenConstructionPeriod k) :
    x ∈ evenConstructionProjectedSet k ↔ evenConstructionReflect k x ∉ evenConstructionProjectedSet k := by
  have hp := evenConstructionPeriod_eq k hk
  have hu : x / 2 < 4 * k - 1 := by omega
  by_cases heven : x % 2 = 0
  · have hxform : x = 2 * (x / 2) := by omega
    rw [hxform, evenConstructionReflect_even k (x / 2) hk hu,
      evenConstructionProjectedSet_even_mem k (x / 2) hk,
      evenConstructionProjectedSet_odd_mem k (evenConstructionReflectNorm k (x / 2)) hk]
    exact evenConstructionX_reflection_complement k (x / 2) hk hu
  · have hxform : x = 2 * (x / 2) + 1 := by omega
    rw [hxform, evenConstructionReflect_odd k (x / 2) hk hu,
      evenConstructionProjectedSet_odd_mem k (x / 2) hk,
      evenConstructionProjectedSet_even_mem k (evenConstructionReflectNorm k (x / 2)) hk]
    exact evenConstructionY_reflection_complement k (x / 2) hk hu

theorem evenConstructionShift_lt_period (k : ℕ) (hk : 1 ≤ k) :
    evenConstructionShift k < evenConstructionPeriod k := by
  have hc := evenConstructionHalfShift_lt k hk
  rw [evenConstructionShift_eq k hk, evenConstructionPeriod_eq k hk]
  omega

theorem evenConstructionReflect_formula (k x : ℕ) (hk : 1 ≤ k)
    (hx : x < evenConstructionPeriod k) :
    evenConstructionReflect k x =
      if x ≤ evenConstructionShift k then evenConstructionShift k - x
      else evenConstructionShift k + evenConstructionPeriod k - x := by
  have hc := evenConstructionShift_lt_period k hk
  unfold evenConstructionReflect
  split_ifs with h
  · have heq : evenConstructionShift k + evenConstructionPeriod k - x =
        evenConstructionPeriod k + (evenConstructionShift k - x) := by omega
    rw [heq, Nat.add_mod]
    have hrem : evenConstructionShift k - x < evenConstructionPeriod k := by omega
    simp [Nat.mod_eq_of_lt hrem]
  · have hrem : evenConstructionShift k + evenConstructionPeriod k - x < evenConstructionPeriod k := by omega
    rw [Nat.mod_eq_of_lt hrem]

/-- The physical reflection is an involution on canonical representatives. -/
theorem evenConstructionReflect_involution (k x : ℕ) (hk : 1 ≤ k)
    (hx : x < evenConstructionPeriod k) :
    evenConstructionReflect k (evenConstructionReflect k x) = x := by
  have hc := evenConstructionShift_lt_period k hk
  have hlt : evenConstructionReflect k x < evenConstructionPeriod k := by
    unfold evenConstructionReflect
    exact Nat.mod_lt _ (by unfold evenConstructionPeriod; omega)
  rw [evenConstructionReflect_formula k (evenConstructionReflect k x) hk hlt,
    evenConstructionReflect_formula k x hk hx]
  split_ifs <;> omega

end CorralFormalization
