import CorralFormalization.Constructions.Optimal.Even.Reflection

set_option maxHeartbeats 0

namespace CorralFormalization

/-- The actual E/O prefix values written as a single index function. -/
def evenConstructionProjectedCode (k j : ℕ) : ℕ :=
  if j % 2 = 0 then
    if (j / 2) % 2 = 0 then 2 * ((j / 2) / 2)
    else 4 * k + 2 * ((j / 2) / 2)
  else if (j - 1) / 2 < k then
    if ((j - 1) / 2) % 2 = 0 then 2 * (k - 1 - ((j - 1) / 2) / 2) + 1
    else 2 * (3 * k - 2 - ((j - 1) / 2) / 2) + 1
  else if ((j - 1) / 2) % 2 = 0 then 2 * (2 * k - 1 - ((j - 1) / 2) / 2)
  else 2 * (4 * k - 2 - ((j - 1) / 2) / 2)

/-- The code is not an abstract table: it equals the projected prefix sum
of the actual gap word at every proper index. -/
theorem evenConstructionProjectedCode_actual (k j : ℕ) (hk : 1 ≤ k) (hj : j < 4 * k - 1) :
    evenConstructionPrefix k j % evenConstructionPeriod k = evenConstructionProjectedCode k j := by
  by_cases heven : j % 2 = 0
  · let t := j / 2
    have hjform : j = 2 * t := by dsimp [t]; omega
    have ht : t < 2 * k := by dsimp [t]; omega
    have hp := evenConstructionProjectedPrefix_even k t hk (by omega)
    by_cases htEven : t % 2 = 0
    · let r := t / 2
      have htform : t = 2 * r := by dsimp [r]; omega
      have hr : r < k := by dsimp [r]; omega
      rw [htform, evenConstructionE_even k r hk hr] at hp
      have hcode : evenConstructionProjectedCode k j = 2 * r := by
        unfold evenConstructionProjectedCode
        split_ifs <;> dsimp [t, r] at * <;> omega
      rw [hcode, hjform, htform]
      exact hp
    · let r := (t - 1) / 2
      have htform : t = 2 * r + 1 := by dsimp [r]; omega
      have hr : r < k := by dsimp [r]; omega
      rw [htform, evenConstructionE_odd k r hk hr] at hp
      have hcode : evenConstructionProjectedCode k j = 4 * k + 2 * r := by
        unfold evenConstructionProjectedCode
        split_ifs <;> dsimp [t, r] at * <;> omega
      rw [hcode, hjform, htform]
      exact hp
  · let t := (j - 1) / 2
    have hjform : j = 2 * t + 1 := by dsimp [t]; omega
    have ht : t < 2 * k - 1 := by dsimp [t]; omega
    have hp := evenConstructionProjectedPrefix_odd k t hk ht
    by_cases hfirst : t < k
    · by_cases htEven : t % 2 = 0
      · let r := t / 2
        have htform : t = 2 * r := by dsimp [r]; omega
        have hr : 2 * r < k := by omega
        rw [htform, evenConstructionO_first_even k r hk hr] at hp
        have hcode : evenConstructionProjectedCode k j = 2 * (k - 1 - r) + 1 := by
          unfold evenConstructionProjectedCode
          split_ifs <;> dsimp [t, r] at * <;> omega
        rw [hcode, hjform, htform]
        exact hp
      · let r := (t - 1) / 2
        have htform : t = 2 * r + 1 := by dsimp [r]; omega
        have hr : 2 * r + 1 < k := by omega
        rw [htform, evenConstructionO_first_odd k r hk hr] at hp
        have hcode : evenConstructionProjectedCode k j = 2 * (3 * k - 2 - r) + 1 := by
          unfold evenConstructionProjectedCode
          split_ifs <;> dsimp [t, r] at * <;> omega
        rw [hcode, hjform, htform]
        exact hp
    · by_cases htEven : t % 2 = 0
      · let r := t / 2
        have htform : t = 2 * r := by dsimp [r]; omega
        have hr0 : k ≤ 2 * r := by omega
        have hr1 : 2 * r < 2 * k - 1 := by omega
        rw [htform, evenConstructionO_second_even k r hk hr0 hr1] at hp
        have hcode : evenConstructionProjectedCode k j = 2 * (2 * k - 1 - r) := by
          unfold evenConstructionProjectedCode
          split_ifs <;> dsimp [t, r] at * <;> omega
        rw [hcode, hjform, htform]
        exact hp
      · let r := (t - 1) / 2
        have htform : t = 2 * r + 1 := by dsimp [r]; omega
        have hr0 : k ≤ 2 * r + 1 := by omega
        have hr1 : 2 * r + 1 < 2 * k - 1 := by omega
        rw [htform, evenConstructionO_second_odd k r hk hr0 hr1] at hp
        have hcode : evenConstructionProjectedCode k j = 2 * (4 * k - 2 - r) := by
          unfold evenConstructionProjectedCode
          split_ifs <;> dsimp [t, r] at * <;> omega
        rw [hcode, hjform, htform]
        exact hp

/-- No two actual proper prefixes have the same residue modulo the smaller
period. -/
theorem evenConstructionProjectedCode_injective (k i j : ℕ) (hk : 1 ≤ k)
    (hi : i < 4 * k - 1) (hj : j < 4 * k - 1)
    (heq : evenConstructionProjectedCode k i = evenConstructionProjectedCode k j) : i = j := by
  unfold evenConstructionProjectedCode at heq
  split_ifs at heq <;> omega

end CorralFormalization
