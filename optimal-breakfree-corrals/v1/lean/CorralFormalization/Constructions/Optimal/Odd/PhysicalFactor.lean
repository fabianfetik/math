import CorralFormalization.Constructions.Optimal.Odd.Assignment
import CorralFormalization.OrderedGaps
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

namespace CorralFormalization.OddCorePhysicalRows

/-! This module uses the earlier two-swap odd construction. References to
the paper and its numbered equations below concern that earlier manuscript,
not the one-swap odd construction printed in the manuscript. -/

open CorralFormalization.OddSeamAssignment

/-- The two literal sites in equation (7), in canonical representatives of
`Z_(2h)`. The second coordinate is reduced exactly as printed. -/
def physicalPoint (A : ℕ) (t : Fin (h A)) (slot : Fin 2) : Fin (2 * h A) :=
  if slot.val = 0 then
    ⟨2 * t.val + 1, by dsimp [h]; omega⟩
  else
    ⟨(2 * t.val + 4) % (2 * h A), Nat.mod_lt _ (by dsimp [h]; omega)⟩

/-- The even site in equation (7) is twice the shifted residue modulo `h`. -/
theorem physicalSecond_eq_shifted (A : ℕ) (t : Fin (h A)) :
    (2 * t.val + 4) % (2 * h A) = 2 * ((t.val + 2) % h A) := by
  calc
    (2 * t.val + 4) % (2 * h A) = (2 * (t.val + 2)) % (2 * h A) := by
      congr 1
    _ = 2 * ((t.val + 2) % h A) := by
      exact Nat.mul_mod_mul_left 2 (t.val + 2) (h A)

/-- Translation by two is injective in the additive group `Fin (h A)`. -/
theorem shiftedResidue_injective (A : ℕ) (hA : 2 ≤ A) :
    Function.Injective (fun t : Fin (h A) => (t.val + 2) % h A) := by
  letI : NeZero (h A) := ⟨by dsimp [h]; omega⟩
  let shift : Fin (h A) := ⟨2, by dsimp [h]; omega⟩
  intro t u huv
  have hshift : t + shift = u + shift := by
    apply Fin.ext
    simpa [shift, Fin.val_add] using huv
  exact add_right_cancel hshift

/-- The literal two-point factor has no repeated site, for every paper
parameter `A ≥ 2`. -/
theorem physicalPoint_injective (A : ℕ) (hA : 2 ≤ A) :
    Function.Injective (fun p : Fin (h A) × Fin 2 =>
      physicalPoint A p.1 p.2) := by
  intro p q hpq
  rcases p with ⟨pt, ps⟩
  rcases q with ⟨qt, qs⟩
  change physicalPoint A pt ps = physicalPoint A qt qs at hpq
  have hval := congrArg Fin.val hpq
  have hp0 : ps.val = 0 ∨ ps.val = 1 := by omega
  have hq0 : qs.val = 0 ∨ qs.val = 1 := by omega
  rcases hp0 with hp0 | hp0 <;> rcases hq0 with hq0 | hq0
  · have hps : ps = 0 := Fin.ext hp0
    have hqs : qs = 0 := Fin.ext hq0
    subst ps
    subst qs
    simp [physicalPoint] at hval
    have ht : pt.val = qt.val := by omega
    apply Prod.ext
    · exact Fin.ext ht
    · rfl
  · have hps : ps = 0 := Fin.ext hp0
    have hqs : qs = 1 := Fin.ext hq0
    subst ps
    subst qs
    change 2 * pt.val + 1 = (2 * qt.val + 4) % (2 * h A) at hval
    rw [physicalSecond_eq_shifted A qt] at hval
    omega
  · have hps : ps = 1 := Fin.ext hp0
    have hqs : qs = 0 := Fin.ext hq0
    subst ps
    subst qs
    change (2 * pt.val + 4) % (2 * h A) = 2 * qt.val + 1 at hval
    rw [physicalSecond_eq_shifted A pt] at hval
    omega
  · have hps : ps = 1 := Fin.ext hp0
    have hqs : qs = 1 := Fin.ext hq0
    subst ps
    subst qs
    change (2 * pt.val + 4) % (2 * h A) =
      (2 * qt.val + 4) % (2 * h A) at hval
    rw [physicalSecond_eq_shifted A pt, physicalSecond_eq_shifted A qt] at hval
    have hmod' : (pt.val + 2) % h A = (qt.val + 2) % h A := by omega
    have ht : pt = qt := shiftedResidue_injective A hA hmod'
    subst qt
    rfl

/-- The literal row-site map is a bijection from row-slot pairs to all
canonical representatives of `Z_(2h)`. Thus the sets in equation (7)
partition the physical cycle, with one occurrence per row slot. -/
theorem physicalPoint_bijective (A : ℕ) (hA : 2 ≤ A) :
    Function.Bijective (fun p : Fin (h A) × Fin 2 =>
      physicalPoint A p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact physicalPoint_injective A hA
  · simp [Fintype.card_prod, Nat.mul_comm]

/-- The row `D_t` as an actual two-point finite set of canonical physical
representatives. -/
def physicalRow (A : ℕ) (t : Fin (h A)) : Finset (Fin (2 * h A)) :=
  {physicalPoint A t 0, physicalPoint A t 1}

/-- Every physical site belongs to exactly one literal row `D_t`. -/
theorem physicalRows_partition (A : ℕ) (hA : 2 ≤ A)
    (x : Fin (2 * h A)) :
    ∃! t : Fin (h A), x ∈ physicalRow A t := by
  obtain ⟨⟨t, slot⟩, hslotx⟩ := (physicalPoint_bijective A hA).2 x
  refine ⟨t, ?_, ?_⟩
  · have hslot : slot = 0 ∨ slot = 1 := by
      have hv : slot.val = 0 ∨ slot.val = 1 := by omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    rcases hslot with hzero | hone
    · subst slot
      simp only [physicalRow, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hslotx.symm
    · subst slot
      simp only [physicalRow, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr hslotx.symm
  · intro u hu
    have hu' : x = physicalPoint A u 0 ∨ x = physicalPoint A u 1 := by
      simpa [physicalRow] using hu
    rcases hu' with hu0 | hu1
    · have hpair : (t, slot) = (u, 0) :=
        (physicalPoint_injective A hA) (hslotx.trans hu0)
      exact (congrArg Prod.fst hpair).symm
    · have hpair : (t, slot) = (u, 1) :=
        (physicalPoint_injective A hA) (hslotx.trans hu1)
      exact (congrArg Prod.fst hpair).symm

/-- The two natural coordinates in the physical row are exactly the values
printed in equation (7), rather than a separately chosen pair. -/
def physicalRowSites (A : ℕ) (t : Fin (h A)) : Finset ℕ :=
  {dFirst A t.val, dSecond A t.val}

theorem physicalPoint_first_val (A : ℕ) (t : Fin (h A)) :
    (physicalPoint A t 0).val = dFirst A t.val := by
  simp [physicalPoint, dFirst]

theorem physicalPoint_second_val (A : ℕ) (t : Fin (h A)) :
    (physicalPoint A t 1).val = dSecond A t.val := by
  simp [physicalPoint, dSecond]

theorem physicalRowSites_eq_physicalPoints (A : ℕ) (t : Fin (h A)) :
    physicalRowSites A t =
      {(physicalPoint A t 0).val, (physicalPoint A t 1).val} := by
  simp [physicalRowSites, physicalPoint_first_val, physicalPoint_second_val]

theorem physicalRowSites_mem_iff (A : ℕ) (t : Fin (h A))
    (x : ℕ) (hx : x < 2 * h A) :
    x ∈ physicalRowSites A t ↔
      (⟨x, hx⟩ : Fin (2 * h A)) ∈ physicalRow A t := by
  rw [physicalRowSites_eq_physicalPoints]
  simp only [physicalRow, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h0 | h1)
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)
  · rintro (h0 | h1)
    · exact Or.inl (congrArg Fin.val h0)
    · exact Or.inr (congrArg Fin.val h1)

/-- The natural representative version of the same partition, matching the
finite-set interface used in physical assembly. -/
theorem physicalRowSites_partition_nat (A : ℕ) (hA : 2 ≤ A)
    (x : ℕ) (hx : x < 2 * h A) :
    ∃! t : Fin (h A), x ∈ physicalRowSites A t := by
  let xFin : Fin (2 * h A) := ⟨x, hx⟩
  obtain ⟨t, ht, htunique⟩ := physicalRows_partition A hA xFin
  refine ⟨t, ?_, ?_⟩
  · exact (physicalRowSites_mem_iff A t x hx).mpr (by simpa [xFin] using ht)
  · intro u hu
    apply htunique u
    exact (physicalRowSites_mem_iff A u x hx).mp hu

/-- For two ordered sites in a clock, the sorted finite-set inventory is the
interior gap followed by the wrap gap. -/
theorem finiteCyclicGapInventory_pair (W a b : ℕ) (hab : a < b) (hb : b < W) :
    finiteCyclicGapInventory W ({a, b} : Finset ℕ) =
      Multiset.ofList [b - a, W + a - b] := by
  have hnd : ([a, b] : List ℕ).Nodup := by simp [hab.ne]
  have hpair : ([a, b] : List ℕ).Pairwise (· < ·) := by simp [hab]
  have hto : ([a, b] : List ℕ).toFinset = ({a, b} : Finset ℕ) := by
    simp
  have hsort : ({a, b} : Finset ℕ).sort (· ≤ ·) = [a, b] := by
    rw [← hto]
    exact (List.toFinset_sort (· ≤ ·) hnd).2
      (hpair.imp (by intro x y hxy; exact le_of_lt hxy))
  rw [finiteCyclicGapInventory, hsort]
  simp [cyclicGaps, adjacentGaps]
  omega

/-- The generic two-site gap formula without assuming which printed point is
the smaller representative. -/
theorem finiteCyclicGapInventory_two_sites (W a b : ℕ)
    (ha : a < W) (hb : b < W) (hne : a ≠ b) :
    finiteCyclicGapInventory W ({a, b} : Finset ℕ) =
      Multiset.ofList [max a b - min a b, W + min a b - max a b] := by
  by_cases hab : a < b
  · rw [finiteCyclicGapInventory_pair W a b hab hb]
    simp [Nat.min_eq_left (Nat.le_of_lt hab), Nat.max_eq_right (Nat.le_of_lt hab)]
  · have hba : b < a := by omega
    have hset : ({a, b} : Finset ℕ) = {b, a} := by
      ext x
      simp
      tauto
    rw [hset, finiteCyclicGapInventory_pair W b a hba ha]
    simp [Nat.max_eq_left (Nat.le_of_lt hba), Nat.min_eq_right (Nat.le_of_lt hba)]

/-- The natural representatives of equation (7) are within the physical
clock and are distinct (one is odd and one is even). -/
theorem physicalRowSites_bounds_distinct (A : ℕ) (hA : 2 ≤ A)
    (t : Fin (h A)) :
    dFirst A t.val < 2 * h A ∧ dSecond A t.val < 2 * h A ∧
      dFirst A t.val ≠ dSecond A t.val := by
  have hfirst : dFirst A t.val < 2 * h A := by
    dsimp [dFirst, h]
    omega
  have hsecond : dSecond A t.val < 2 * h A := by
    exact Nat.mod_lt _ (by dsimp [h]; omega)
  have hneq : dFirst A t.val ≠ dSecond A t.val := by
    intro heq
    have heven : dSecond A t.val = 2 * ((t.val + 2) % h A) := by
      dsimp [dSecond]
      exact physicalSecond_eq_shifted A t
    rw [heven] at heq
    dsimp [dFirst] at heq
    omega
  exact ⟨hfirst, hsecond, hneq⟩

/-- The sorted-coordinate gaps of the actual two points in `D_t`, expressed
through the manuscript's head and tail values. -/
def physicalGapShort (A : ℕ) (t : Fin (h A)) : ℕ :=
  2 * h A - dTail A t - dHead A t

def physicalGapWrap (A : ℕ) (t : Fin (h A)) : ℕ :=
  dTail A t + dHead A t

theorem physicalGaps_eq_sorted (A : ℕ) (hA : 2 ≤ A)
    (t : Fin (h A)) :
    physicalGapShort A t =
        max (dFirst A t.val) (dSecond A t.val) -
          min (dFirst A t.val) (dSecond A t.val) ∧
      physicalGapWrap A t =
        2 * h A + min (dFirst A t.val) (dSecond A t.val) -
          max (dFirst A t.val) (dSecond A t.val) := by
  obtain ⟨hfirst, hsecond, _⟩ := physicalRowSites_bounds_distinct A hA t
  have hmax : max (dFirst A t.val) (dSecond A t.val) < 2 * h A := by
    exact max_lt_iff.mpr ⟨hfirst, hsecond⟩
  unfold physicalGapShort physicalGapWrap dHead dTail
  omega

/-- The two positive cyclic gaps of the literal two-point factor are `3` and
`2h-3`; the disjunction records which is the interior and which the wrap. -/
theorem physicalGapPair_inventory (A : ℕ) (hA : 2 ≤ A)
    (t : Fin (h A)) :
    (physicalGapShort A t = 3 ∧ physicalGapWrap A t = 2 * h A - 3) ∨
    (physicalGapShort A t = 2 * h A - 3 ∧ physicalGapWrap A t = 3) := by
  unfold physicalGapShort physicalGapWrap
  rw [dTail_eq_endpoint_formula A t, dHead_eq_endpoint_formula A t]
  by_cases hregular : t.val ≤ h A - 3
  · have hregular' : t.val ≤ 2 * A := by simpa [h] using hregular
    simp [hregular', h]
    omega
  · by_cases hfirstWrap : t.val = h A - 2
    · have hfirstWrap' : t.val = 2 * A + 1 := by simpa [h] using hfirstWrap
      simp [hfirstWrap', h]
    · have hlast : t.val = h A - 1 := by
        have ht : t.val < 2 * A + 3 := by simpa [h] using t.isLt
        dsimp [h] at hregular hfirstWrap ⊢
        omega
      have hlast' : t.val = 2 * A + 2 := by simpa [h] using hlast
      simp [hlast', h]
      omega

/-- The sorted cyclic-gap inventory of the actual finite set `D_t` is
exactly `{3, 2h-3}`. This explicitly connects equation (7) to the finite-set
representation used by `finiteCyclicGapInventory`. -/
theorem physicalRow_finiteCyclicGapInventory (A : ℕ) (hA : 2 ≤ A)
    (t : Fin (h A)) :
    finiteCyclicGapInventory (2 * h A) (physicalRowSites A t) =
      Multiset.ofList [3, 2 * h A - 3] := by
  obtain ⟨hfirst, hsecond, hneq⟩ := physicalRowSites_bounds_distinct A hA t
  have hinv := finiteCyclicGapInventory_two_sites (2 * h A)
    (dFirst A t.val) (dSecond A t.val) hfirst hsecond hneq
  change finiteCyclicGapInventory (2 * h A)
      ({dFirst A t.val, dSecond A t.val} : Finset ℕ) = _ at ⊢
  rw [hinv]
  have hsorted := physicalGaps_eq_sorted A hA t
  have hpair := physicalGapPair_inventory A hA t
  rw [← hsorted.1, ← hsorted.2]
  rcases hpair with ⟨hshort, hwrap⟩ | ⟨hshort, hwrap⟩
  · simp [hshort, hwrap]
  · rw [hshort, hwrap]
    simpa using (List.Perm.swap (2 * h A - 3) 3 []).symm

#print axioms physicalPoint_bijective
#print axioms physicalRows_partition
#print axioms physicalRowSites_partition_nat
#print axioms finiteCyclicGapInventory_pair
#print axioms physicalGaps_eq_sorted
#print axioms physicalGapPair_inventory
#print axioms physicalRow_finiteCyclicGapInventory

end CorralFormalization.OddCorePhysicalRows
