import CorralFormalization.Constructions.Optimal.Even.Rows
import CorralFormalization.ReverseGapWord

namespace CorralFormalization

/-- The full physical clock used by the even construction. -/
def evenConstructionClock (k : ℕ) : ℕ := k * evenConstructionPeriod k

theorem evenConstructionClock_eq_sum (k : ℕ) (hk : 1 ≤ k) :
    evenConstructionClock k = (evenConstructionGapWord k).sum := by
  rw [evenConstructionGapWord_sum k hk]
  unfold evenConstructionClock
  rw [evenConstructionPeriod_eq k hk]
  ring

theorem evenConstructionClock_pos (k : ℕ) (hk : 1 ≤ k) : 0 < evenConstructionClock k := by
  unfold evenConstructionClock evenConstructionPeriod
  exact Nat.mul_pos (by omega) (by omega)

theorem evenConstructionRawPrefixSet_clock_bound (k q : ℕ) (hk : 1 ≤ k)
    (hq : q ∈ evenConstructionRawPrefixSet k) : q < evenConstructionClock k := by
  rw [evenConstructionClock_eq_sum k hk, evenConstructionGapWord_sum k hk]
  exact evenConstructionRawPrefixSet_bound k q hk hq

/-- Actual physical reflection of the proper-prefix set, before translation
by whole periods. -/
def evenConstructionReflectedSet (k : ℕ) : Finset ℕ :=
  (evenConstructionRawPrefixSet k).image
    (fun q => (evenConstructionShift k + evenConstructionClock k - q) % evenConstructionClock k)

theorem evenConstructionPhysicalReflect_projection (k q : ℕ) (hk : 1 ≤ k)
    (hq : q < evenConstructionClock k) :
    ((evenConstructionShift k + evenConstructionClock k - q) % evenConstructionClock k) % evenConstructionPeriod k =
      evenConstructionReflect k (q % evenConstructionPeriod k) := by
  have hp : 0 < evenConstructionPeriod k := by unfold evenConstructionPeriod; omega
  have hrem : q % evenConstructionPeriod k < evenConstructionPeriod k := Nat.mod_lt _ hp
  have hbase : evenConstructionShift k + evenConstructionClock k ≡
      evenConstructionShift k + evenConstructionPeriod k [MOD evenConstructionPeriod k] := by
    change (evenConstructionShift k + evenConstructionClock k) % evenConstructionPeriod k =
      (evenConstructionShift k + evenConstructionPeriod k) % evenConstructionPeriod k
    simp [evenConstructionClock, Nat.add_mod]
  have hqmod : q ≡ q % evenConstructionPeriod k [MOD evenConstructionPeriod k] := by
    change q % evenConstructionPeriod k = (q % evenConstructionPeriod k) % evenConstructionPeriod k
    simp
  have hsub := Nat.ModEq.sub (by omega : q ≤ evenConstructionShift k + evenConstructionClock k)
    (by omega : q % evenConstructionPeriod k ≤ evenConstructionShift k + evenConstructionPeriod k) hbase hqmod
  change (evenConstructionShift k + evenConstructionClock k - q) % evenConstructionPeriod k =
    (evenConstructionShift k + evenConstructionPeriod k - q % evenConstructionPeriod k) % evenConstructionPeriod k at hsub
  unfold evenConstructionReflect evenConstructionClock at *
  rw [Nat.mod_mul_left_mod]
  exact hsub

theorem evenConstructionRawPrefix_projected_mem (k q : ℕ) (hk : 1 ≤ k)
    (hq : q ∈ evenConstructionRawPrefixSet k) : q % evenConstructionPeriod k ∈ evenConstructionProjectedSet k := by
  rw [← evenConstructionRawPrefixSet_projection k hk]
  exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

theorem evenConstructionReflectedSet_bound (k q : ℕ) (hk : 1 ≤ k)
    (hq : q ∈ evenConstructionReflectedSet k) : q < evenConstructionClock k := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
  exact Nat.mod_lt _ (evenConstructionClock_pos k hk)

/-- The projection of each reflected actual point is outside the original
projected prefix set. -/
theorem evenConstructionReflectedSet_projected_complement (k q : ℕ) (hk : 1 ≤ k)
    (hq : q ∈ evenConstructionReflectedSet k) : q % evenConstructionPeriod k ∉ evenConstructionProjectedSet k := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  rw [evenConstructionPhysicalReflect_projection k p hk (evenConstructionRawPrefixSet_clock_bound k p hk hp)]
  apply (evenConstructionProjected_reflection_complement k (p % evenConstructionPeriod k) hk
    (Nat.mod_lt _ (by unfold evenConstructionPeriod; omega))).1
  exact evenConstructionRawPrefix_projected_mem k p hk hp

/-- The projection of the reflected actual points is injective. -/
theorem evenConstructionReflectedSet_projection_injective (k p q : ℕ) (hk : 1 ≤ k)
    (hp : p ∈ evenConstructionReflectedSet k) (hq : q ∈ evenConstructionReflectedSet k)
    (heq : p % evenConstructionPeriod k = q % evenConstructionPeriod k) : p = q := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
  rw [evenConstructionPhysicalReflect_projection k a hk (evenConstructionRawPrefixSet_clock_bound k a hk ha),
    evenConstructionPhysicalReflect_projection k b hk (evenConstructionRawPrefixSet_clock_bound k b hk hb)] at heq
  have hp : 0 < evenConstructionPeriod k := by unfold evenConstructionPeriod; omega
  have hreflect := congrArg (evenConstructionReflect k) heq
  rw [evenConstructionReflect_involution k (a % evenConstructionPeriod k) hk (Nat.mod_lt _ hp),
    evenConstructionReflect_involution k (b % evenConstructionPeriod k) hk (Nat.mod_lt _ hp)] at hreflect
  have hab := evenConstructionRawPrefixSet_projection_injective k a b hk ha hb hreflect
  rw [hab]

/-- The two actual prefix families together contain exactly one physical
representative of every smaller-period residue. -/
theorem evenConstructionTwoPrefixes_transversal (k : ℕ) (hk : 1 ≤ k)
    (r : ℕ) (hr : r < evenConstructionPeriod k) :
    ∃! q, q ∈ evenConstructionRawPrefixSet k ∪ evenConstructionReflectedSet k ∧
      q % evenConstructionPeriod k = r := by
  have hp : 0 < evenConstructionPeriod k := by unfold evenConstructionPeriod; omega
  have hreflectlt : evenConstructionReflect k r < evenConstructionPeriod k := by
    unfold evenConstructionReflect
    exact Nat.mod_lt _ hp
  by_cases hrmem : r ∈ evenConstructionProjectedSet k
  · have himage : r ∈ (evenConstructionRawPrefixSet k).image (fun q => q % evenConstructionPeriod k) := by
      rw [evenConstructionRawPrefixSet_projection k hk]
      exact hrmem
    obtain ⟨q, hq, hqr⟩ := Finset.mem_image.mp himage
    refine ⟨q, ⟨Finset.mem_union.mpr (Or.inl hq), hqr⟩, ?_⟩
    intro x ⟨hx, hxr⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact evenConstructionRawPrefixSet_projection_injective k x q hk hx hq (hxr.trans hqr.symm)
    · have hn := evenConstructionReflectedSet_projected_complement k x hk hx
      rw [hxr] at hn
      exact False.elim (hn hrmem)
  · have hmirror : evenConstructionReflect k r ∈ evenConstructionProjectedSet k := by
      apply (evenConstructionProjected_reflection_complement k (evenConstructionReflect k r) hk hreflectlt).2
      rw [evenConstructionReflect_involution k r hk hr]
      exact hrmem
    have himage : evenConstructionReflect k r ∈
        (evenConstructionRawPrefixSet k).image (fun q => q % evenConstructionPeriod k) := by
      rw [evenConstructionRawPrefixSet_projection k hk]
      exact hmirror
    obtain ⟨a, ha, har⟩ := Finset.mem_image.mp himage
    let q := (evenConstructionShift k + evenConstructionClock k - a) % evenConstructionClock k
    have hq : q ∈ evenConstructionReflectedSet k := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hqr : q % evenConstructionPeriod k = r := by
      dsimp [q]
      rw [evenConstructionPhysicalReflect_projection k a hk (evenConstructionRawPrefixSet_clock_bound k a hk ha),
        har, evenConstructionReflect_involution k r hk hr]
    refine ⟨q, ⟨Finset.mem_union.mpr (Or.inr hq), hqr⟩, ?_⟩
    intro x ⟨hx, hxr⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · have hm := evenConstructionRawPrefix_projected_mem k x hk hx
      rw [hxr] at hm
      exact False.elim (hrmem hm)
    · exact evenConstructionReflectedSet_projection_injective k x q hk hx hq (hxr.trans hqr.symm)

end CorralFormalization
