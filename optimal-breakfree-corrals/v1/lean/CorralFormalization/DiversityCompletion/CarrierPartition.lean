import CorralFormalization.DiversityCompletion.SeedASeparation
import CorralFormalization.DiversityCompletion.EvenSwitchesB

namespace CorralFormalization.EvenSupportPartition

open Finset EvenSwitches PhysicalCorral DiversitySymmetry

def baseRow (m : ℕ) : Finset (ZMod (clock m)) :=
  physicalSites (clock m) (evenConstructionRawPrefixSet (2 * m + 1))

def oldCarrier (m : ℕ) : Finset (ZMod (clock m)) :=
  baseRow m ∪ (Motion.reflection (((height m) ^ 2 - 1 : ℕ) : ZMod (clock m))).onRow (baseRow m)

def natCarrier (m : ℕ) (a : Choices m) : Finset ℕ := rowA m a ∪ rowB m a

def newCarrier (m : ℕ) (a : Choices m) : Finset (ZMod (clock m)) :=
  physicalSites (clock m) (natCarrier m a)

theorem cast_mem_newCarrier {m : ℕ} {a : Choices m} {x : ℕ}
    (hx : x ∈ natCarrier m a) : (x : ZMod (clock m)) ∈ newCarrier m a :=
  Finset.mem_image_of_mem _ hx

theorem special_subset (m : ℕ) (a : Choices m) :
    ({0, (height m)^2-1, (height m)^2, clock m-1} : Finset ℕ) ⊆ natCarrier m a := by
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  unfold natCarrier rowA rowB
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

theorem lower_pair_subset (m : ℕ) (a : Choices m) (j : ℕ) (hj : j < halfHeight m) :
    ({(2*j+1)*(height m-1), (2*j+2)*(height m-1)} : Finset ℕ) ⊆ natCarrier m a := by
  rw [← complementary_lower_pair m a.1 j]
  have hA : lowerA m a.1 j ∈ (range (halfHeight m)).image (lowerA m a.1) :=
    mem_image_of_mem _ (mem_range.mpr hj)
  have hB : lowerB m a.1 j ∈ (range (halfHeight m)).image (lowerB m a.1) :=
    mem_image_of_mem _ (mem_range.mpr hj)
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl <;> unfold natCarrier rowA rowB <;> simp only [mem_union] <;> tauto

theorem upper_pair_subset (m : ℕ) (a : Choices m) (j : ℕ) (hj : j < halfHeight m) :
    ({(height m+2+2*j)*(height m-1), (height m+2+2*j)*(height m-1)+1} : Finset ℕ) ⊆
      natCarrier m a := by
  rw [← complementary_upper_pair m a.2 j]
  have hA : upperA m a.2 j ∈ (range (halfHeight m)).image (upperA m a.2) :=
    mem_image_of_mem _ (mem_range.mpr hj)
  have hB : upperB m a.2 j ∈ (range (halfHeight m)).image (upperB m a.2) :=
    mem_image_of_mem _ (mem_range.mpr hj)
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl <;> unfold natCarrier rowA rowB <;> simp only [mem_union] <;> tauto

theorem complementary_middle_pair (m i : ℕ) :
    ({middleA m i, middleB m i} : Finset ℕ) = {2*height m*i-1, 2*height m*i} := by
  have hmod : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [middleA, middleB, hmod, Finset.pair_comm]

theorem middle_pair_subset (m : ℕ) (a : Choices m) (i : ℕ)
    (hi0 : 1 ≤ i) (hi : i < halfHeight m) :
    ({2*height m*i-1, 2*height m*i} : Finset ℕ) ⊆ natCarrier m a := by
  rw [← complementary_middle_pair]
  have hA : middleA m i ∈ (Ico 1 (halfHeight m)).image (middleA m) :=
    mem_image_of_mem _ (mem_Ico.mpr ⟨hi0, hi⟩)
  have hB : middleB m i ∈ (Ico 1 (halfHeight m)).image (middleB m) :=
    mem_image_of_mem _ (mem_Ico.mpr ⟨hi0, hi⟩)
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl <;> unfold natCarrier rowA rowB <;> simp only [mem_union] <;> tauto

theorem fixedA_pair_subset (m : ℕ) (a : Choices m) (r : ℕ) (hr : r < m) :
    ({fixedA m r, fixedA m r+height m-1} : Finset ℕ) ⊆ natCarrier m a := by
  intro x hx
  have h : x ∈ (range m).biUnion (fun r => {fixedA m r, fixedA m r+height m-1}) :=
    mem_biUnion.mpr ⟨r, mem_range.mpr hr, hx⟩
  unfold natCarrier rowA
  simp only [mem_union]
  tauto

theorem fixedB_pair_subset (m : ℕ) (a : Choices m) (r : ℕ) (hr : r < m-1) :
    ({fixedB m r, fixedB m r+height m-1} : Finset ℕ) ⊆ natCarrier m a := by
  intro x hx
  have h : x ∈ (range (m-1)).biUnion (fun r => {fixedB m r, fixedB m r+height m-1}) :=
    mem_biUnion.mpr ⟨r, mem_range.mpr hr, hx⟩
  unfold natCarrier rowB
  simp only [mem_union]
  tauto

/-- All original pair-boundary points strictly after the central point and
before the final pair belong to the fixed A/B pools, with their companions. -/
theorem fixed_slot_pair_subset (m : ℕ) (a : Choices m) (i : ℕ)
    (hlo : halfHeight m+1 ≤ i) (hhi : i < height m-1) :
    ({2*height m*i, 2*height m*i+height m-1} : Finset ℕ) ⊆ natCarrier m a := by
  let r := (i-(halfHeight m+1))/2
  by_cases heven : (i-(halfHeight m+1)) % 2 = 0
  · have hi : i = halfHeight m+1+2*r := by dsimp [r]; omega
    have hr : r < m := by unfold halfHeight height at *; dsimp [r]; omega
    simpa only [fixedA, ← hi] using fixedA_pair_subset m a r hr
  · have hi : i = halfHeight m+2+2*r := by dsimp [r]; omega
    have hr : r < m-1 := by unfold halfHeight height at *; dsimp [r]; omega
    simpa only [fixedB, ← hi] using fixedB_pair_subset m a r hr

/-- Elementary cardinality upper bound from the literal B coordinate pools.
It does not use B's gap palette or its one-winding proof. -/
theorem rowB_card_le (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (rowB m a).card ≤ order m := by
  let X0 : Finset ℕ := {(height m)^2-1, (height m)^2, clock m-1}
  let X1 := (range (halfHeight m)).image (lowerB m a.1)
  let X2 := (Ico 1 (halfHeight m)).image (middleB m)
  let X3 := (range (halfHeight m)).image (upperB m a.2)
  let X4 := (range (m-1)).biUnion (fun r => {fixedB m r, fixedB m r+height m-1})
  have h0 : X0.card ≤ 3 := card_le_three
  have h1 : X1.card ≤ halfHeight m := card_image_le.trans_eq (card_range _)
  have h2 : X2.card ≤ halfHeight m-1 := card_image_le.trans_eq (by simp)
  have h3 : X3.card ≤ halfHeight m := card_image_le.trans_eq (card_range _)
  have h4 : X4.card ≤ 2*(m-1) := by
    calc
      X4.card ≤ ∑ r ∈ range (m-1), ({fixedB m r, fixedB m r+height m-1} : Finset ℕ).card := card_biUnion_le
      _ ≤ ∑ _r ∈ range (m-1), 2 := sum_le_sum fun _ _ => card_le_two
      _ = 2*(m-1) := by simp [Nat.mul_comm]
  have hu1 := card_union_le X0 X1
  have hu2 := card_union_le (X0 ∪ X1) X2
  have hu3 := card_union_le (X0 ∪ X1 ∪ X2) X3
  have hu4 := card_union_le (X0 ∪ X1 ∪ X2 ∪ X3) X4
  change (X0 ∪ X1 ∪ X2 ∪ X3 ∪ X4).card ≤ _
  unfold halfHeight order at *
  omega

theorem rowA_card (m : ℕ) (hm : 1 ≤ m) (a : Choices m) : (rowA m a).card = order m := by
  have h := congrArg Multiset.card (rowA_gap_inventory m hm a)
  rw [finiteCyclicGapInventory_card] at h
  simpa [fullGapList] using h

theorem newCarrier_card_le (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (newCarrier m a).card ≤ 2*order m := by
  have himage : (newCarrier m a).card ≤ (natCarrier m a).card := card_image_le
  have hunion := card_union_le (rowA m a) (rowB m a)
  have hA := rowA_card m hm a
  have hB := rowB_card_le m hm a
  unfold natCarrier at himage
  omega

theorem old_seed_reflection_disjoint (m : ℕ) :
    Disjoint (baseRow m)
      ((Motion.reflection (((height m)^2-1 : ℕ) : ZMod (clock m))).onRow (baseRow m)) := by
  unfold baseRow
  rw [switchClock_eq_evenConstructionClock m]
  let k := 2*m+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  let z : Fin k := ⟨0, by omega⟩
  let t : Fin k := ⟨m, by dsimp [k]; omega⟩
  have hheight : height m = 2*k := by dsimp [height, k]; ring
  have hnat : evenConstructionPeriod k*m + evenConstructionShift k = (height m)^2-1 := by
    calc
      _ = evenConstructionShift k + m*evenConstructionPeriod k := by ring
      _ = (2*k)^2-1 := by simpa only [k] using (diversity_reflection_parameter m).symm
      _ = (height m)^2-1 := by rw [hheight]
  have hR : evenPhysicalRow k 0 z = evenConstructionSeed k := by
    rw [evenPhysicalRow_translation]
    simp [evenConstructionRowSource, z, evenConstructionSeed]
  have hG : evenPhysicalRow k 1 t =
      (Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock k))).onRow (evenConstructionSeed k) := by
    rw [evenPhysicalRow_translation]
    simp only [evenConstructionRowSource, Fin.val_one, one_ne_zero, if_false]
    rw [evenPhysical_reflection k hk, ← Motion.onRow_compose]
    change (Motion.reflection (((evenConstructionPeriod k*m : ℕ) : ZMod (evenConstructionClock k)) +
      (evenConstructionShift k : ZMod (evenConstructionClock k)))).onRow (evenConstructionSeed k) = _
    rw [← Nat.cast_add, hnat]
  change Disjoint (evenConstructionSeed k)
    ((Motion.reflection (((height m)^2-1 : ℕ) : ZMod (evenConstructionClock k))).onRow (evenConstructionSeed k))
  apply disjoint_left.mpr
  intro x hx hy
  have hx' : x ∈ evenPhysicalRow k 0 z := by rw [hR]; exact hx
  have hy' : x ∈ evenPhysicalRow k 1 t := by rw [hG]; exact hy
  obtain ⟨bj, _, huniq⟩ := evenPhysicalRow_partition k hk x
  have heq := (huniq (0, z) hx').trans (huniq (1, t) hy').symm
  have hbad := congrArg (fun p : Fin 2 × Fin k => p.1.val) heq
  simp at hbad

theorem baseRow_card (m : ℕ) : (baseRow m).card = order m := by
  unfold baseRow
  rw [switchClock_eq_evenConstructionClock m]
  let k := 2*m+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  let : NeZero (evenConstructionClock k) := ⟨Nat.ne_of_gt (evenConstructionClock_pos k hk)⟩
  change (evenConstructionSeed k).card = order m
  have h := congrArg Multiset.card (evenConstructionSeed_inventory k hk)
  rw [finiteCyclicGapInventory_card, card_image_of_injective _ (ZMod.val_injective _)] at h
  have horder : 4*k-1 = order m := by
    have heq : 4*k = 8*m+4 := by dsimp [k]; ring
    unfold order
    omega
  simpa [fullGapList, horder] using h

theorem oldCarrier_card (m : ℕ) : (oldCarrier m).card = 2*order m := by
  rw [oldCarrier, card_union_of_disjoint (old_seed_reflection_disjoint m),
    Motion.onRow, card_image_of_injective _ (Motion.act_injective _), baseRow_card]
  omega

/-- Converting either exact ordinary sum relation into literal reflection
on the physical clock avoids any unproved modular representative formula. -/
theorem reflected_cast_of_sum (M C x y : ℕ) (hsum : x+y=C ∨ x+y=C+M) :
    (C : ZMod M) - (x : ZMod M) = (y : ZMod M) := by
  rcases hsum with hs | hs
  · have h := congrArg (fun z : ℕ => (z : ZMod M)) hs
    push_cast at h
    linear_combination -h
  · have h := congrArg (fun z : ℕ => (z : ZMod M)) hs
    push_cast at h
    simp only [ZMod.natCast_self, add_zero] at h
    linear_combination -h

theorem height_half (m : ℕ) : height m = 2*halfHeight m := by
  unfold height halfHeight
  ring

theorem height_square_pos (m : ℕ) : 0 < (height m)^2 := by
  unfold height
  positivity

theorem complement_factor (m : ℕ) :
    (height m+1)*(height m-1) = (height m)^2-1 := by
  have h1 : height m-1+1 = height m := by unfold height; omega
  have h2 := congrArg (fun x => (height m+1)*x) h1
  have h3 : (height m)^2-1+1 = (height m)^2 := by
    apply Nat.sub_add_cancel
    exact height_square_pos m
  nlinarith

theorem complement_factor_wrap (m : ℕ) :
    (3*height m+2)*(height m-1)+1 = (height m)^2-1+clock m := by
  have h1 : height m-1+1 = height m := by unfold height; omega
  have h2 := congrArg (fun x => (3*height m+2)*x) h1
  have h3 : (height m)^2-1+1 = (height m)^2 := by
    apply Nat.sub_add_cancel
    exact height_square_pos m
  have hM : clock m+height m = 2*(height m)^2 := by unfold clock height order; ring
  nlinarith

theorem lower_reflection_sum (m j t : ℕ) (hjt : j+t+1 = halfHeight m) :
    (2*j+1)*(height m-1)+(2*t+2)*(height m-1) = (height m)^2-1 := by
  calc
    _ = (2*(j+t+1)+1)*(height m-1) := by ring
    _ = (2*halfHeight m+1)*(height m-1) := by rw [hjt]
    _ = (height m+1)*(height m-1) := by rw [← height_half]
    _ = _ := complement_factor m

theorem upper_reflection_sum (m j t : ℕ) (hjt : j+t+1 = halfHeight m) :
    (height m+2+2*j)*(height m-1)+
      ((height m+2+2*t)*(height m-1)+1) = (height m)^2-1+clock m := by
  calc
    _ = (2*height m+2+2*(j+t+1))*(height m-1)+1 := by ring
    _ = (2*height m+2+2*halfHeight m)*(height m-1)+1 := by rw [hjt]
    _ = (3*height m+2)*(height m-1)+1 := by rw [← height_half]; ring
    _ = _ := complement_factor_wrap m

theorem middle_reflection_sum (m i j : ℕ) (hj : 0 < j) (hij : i+j = halfHeight m) :
    2*height m*i+(2*height m*j-1) = (height m)^2-1 := by
  have hp : 0 < 2*height m*j := by unfold height; positivity
  have hcancel := Nat.sub_add_cancel (show 1 ≤ 2*height m*j by omega)
  have hsum : 2*height m*i+(2*height m*j-1)+1 = (height m)^2 := by
    calc
      _ = 2*height m*i+2*height m*j := by omega
      _ = height m*(2*(i+j)) := by ring
      _ = height m*(2*halfHeight m) := by rw [hij]
      _ = (height m)^2 := by rw [← height_half]; ring
  omega

theorem fixed_reflection_sum (m i j : ℕ) (hij : i+j+1 = 3*halfHeight m) :
    2*height m*i+(2*height m*j+height m-1) = (height m)^2-1+clock m := by
  have hp : 0 < 2*height m*j+height m := by unfold height; positivity
  have hcancel := Nat.sub_add_cancel (show 1 ≤ 2*height m*j+height m by omega)
  have hsum : (2*height m*i+(2*height m*j+height m-1))+1+height m = 3*(height m)^2 := by
    calc
      _ = 2*height m*(i+j+1) := by nlinarith
      _ = 2*height m*(3*halfHeight m) := by rw [hij]
      _ = 3*(height m*(2*halfHeight m)) := by ring
      _ = 3*(height m)^2 := by rw [← height_half]; ring
  have hC : (height m)^2-1+1 = (height m)^2 := by
    apply Nat.sub_add_cancel
    exact height_square_pos m
  have hM : clock m+height m = 2*(height m)^2 := by unfold clock height order; ring
  omega

theorem lower_with_reflection (m : ℕ) (a : Choices m) (j : ℕ) (hj : j < halfHeight m) :
    (((2*j+1)*(height m-1) : ℕ) : ZMod (clock m)) ∈ newCarrier m a ∧
    ((height m)^2-1 : ℕ) - (((2*j+1)*(height m-1) : ℕ) : ZMod (clock m)) ∈ newCarrier m a := by
  let t := halfHeight m-1-j
  have ht : t < halfHeight m := by dsimp [t]; unfold halfHeight at *; omega
  have hjt : j+t+1 = halfHeight m := by dsimp [t]; omega
  have hx : (((2*j+1)*(height m-1) : ℕ) : ZMod (clock m)) ∈ newCarrier m a :=
    cast_mem_newCarrier (lower_pair_subset m a j hj (by simp))
  have hy : (((2*t+2)*(height m-1) : ℕ) : ZMod (clock m)) ∈ newCarrier m a :=
    cast_mem_newCarrier (lower_pair_subset m a t ht (by simp))
  have href := reflected_cast_of_sum (clock m) ((height m)^2-1)
    ((2*j+1)*(height m-1)) ((2*t+2)*(height m-1)) (Or.inl (lower_reflection_sum m j t hjt))
  exact ⟨hx, by rw [href]; exact hy⟩

theorem upper_with_reflection (m : ℕ) (a : Choices m) (j : ℕ) (hj : j < halfHeight m) :
    (((height m+2+2*j)*(height m-1) : ℕ) : ZMod (clock m)) ∈ newCarrier m a ∧
    ((height m)^2-1 : ℕ) - (((height m+2+2*j)*(height m-1) : ℕ) : ZMod (clock m)) ∈ newCarrier m a := by
  let t := halfHeight m-1-j
  have ht : t < halfHeight m := by dsimp [t]; unfold halfHeight at *; omega
  have hjt : j+t+1 = halfHeight m := by dsimp [t]; omega
  have hx : (((height m+2+2*j)*(height m-1) : ℕ) : ZMod (clock m)) ∈ newCarrier m a :=
    cast_mem_newCarrier (upper_pair_subset m a j hj (by simp))
  have hy : (((height m+2+2*t)*(height m-1)+1 : ℕ) : ZMod (clock m)) ∈ newCarrier m a :=
    cast_mem_newCarrier (upper_pair_subset m a t ht (by simp))
  have href := reflected_cast_of_sum (clock m) ((height m)^2-1)
    ((height m+2+2*j)*(height m-1)) ((height m+2+2*t)*(height m-1)+1)
    (Or.inr (upper_reflection_sum m j t hjt))
  exact ⟨hx, by rw [href]; exact hy⟩

/-- Every original complete-pair boundary and its literal reflection are
present in the new coordinate union. This includes zero, the central
boundary, the alternating fixed pools, and the final boundary. -/
theorem boundary_with_reflection (m : ℕ) (a : Choices m) (i : ℕ) (hi : i < height m) :
    (((2*height m*i) : ℕ) : ZMod (clock m)) ∈ newCarrier m a ∧
    ((height m)^2-1 : ℕ) - (((2*height m*i) : ℕ) : ZMod (clock m)) ∈ newCarrier m a := by
  by_cases hi0 : i = 0
  · subst i
    have hx := cast_mem_newCarrier (x := 0) (special_subset m a (by simp))
    have hy := cast_mem_newCarrier (x := (height m)^2-1) (special_subset m a (by simp))
    simpa using And.intro hx hy
  by_cases hlow : i < halfHeight m
  · let j := halfHeight m-i
    have hj0 : 0 < j := by dsimp [j]; omega
    have hj : j < halfHeight m := by dsimp [j]; omega
    have hij : i+j = halfHeight m := by dsimp [j]; omega
    have hx := cast_mem_newCarrier (x := 2*height m*i)
      (middle_pair_subset m a i (by omega) hlow (by simp))
    have hy := cast_mem_newCarrier (x := 2*height m*j-1)
      (middle_pair_subset m a j (by omega) hj (by simp))
    have href := reflected_cast_of_sum (clock m) ((height m)^2-1)
      (2*height m*i) (2*height m*j-1) (Or.inl (middle_reflection_sum m i j hj0 hij))
    exact ⟨hx, by rw [href]; exact hy⟩
  by_cases hcentral : i = halfHeight m
  · subst i
    have hcenter : 2*height m*halfHeight m = (height m)^2 := by
      calc
        _ = height m*(2*halfHeight m) := by ring
        _ = _ := by rw [← height_half]; ring
    have hx := cast_mem_newCarrier (x := (height m)^2) (special_subset m a (by simp))
    have hy := cast_mem_newCarrier (x := clock m-1) (special_subset m a (by simp))
    have hC : (height m)^2-1+1 = (height m)^2 := by
      apply Nat.sub_add_cancel
      exact height_square_pos m
    have hM : clock m-1+1 = clock m := by
      apply Nat.sub_add_cancel
      unfold clock height order
      nlinarith
    have href := reflected_cast_of_sum (clock m) ((height m)^2-1)
      ((height m)^2) (clock m-1) (Or.inr (by omega))
    simpa only [hcenter] using And.intro hx (by rw [href]; exact hy)
  by_cases hlast : i = height m-1
  · subst i
    have hj : halfHeight m-1 < halfHeight m := by unfold halfHeight; omega
    have hcoef : height m+2+2*(halfHeight m-1) = 2*height m := by
      unfold height halfHeight
      omega
    have hp := upper_with_reflection m a (halfHeight m-1) hj
    simpa only [hcoef] using hp
  · let j := 3*halfHeight m-1-i
    have hilo : halfHeight m+1 ≤ i := by omega
    have hihi : i < height m-1 := by omega
    have hjlo : halfHeight m+1 ≤ j := by
      dsimp [j]
      have hh := height_half m
      omega
    have hjhi : j < height m-1 := by
      dsimp [j]
      have hh := height_half m
      omega
    have hij : i+j+1 = 3*halfHeight m := by
      dsimp [j]
      have hh := height_half m
      omega
    have hx := cast_mem_newCarrier (x := 2*height m*i)
      (fixed_slot_pair_subset m a i hilo hihi (by simp))
    have hy := cast_mem_newCarrier (x := 2*height m*j+height m-1)
      (fixed_slot_pair_subset m a j hjlo hjhi (by simp))
    have href := reflected_cast_of_sum (clock m) ((height m)^2-1)
      (2*height m*i) (2*height m*j+height m-1) (Or.inr (fixed_reflection_sum m i j hij))
    exact ⟨hx, by rw [href]; exact hy⟩

/-- Every actual old prefix point, and its actual physical reflection, is
in the literal A/B union. The proof uses the old even/odd prefix formulas,
not an assumed D1/D5 support equality. -/
theorem baseRow_with_reflection (m : ℕ) (a : Choices m) (x : ZMod (clock m))
    (hx : x ∈ baseRow m) :
    x ∈ newCarrier m a ∧ ((height m)^2-1 : ℕ) - x ∈ newCarrier m a := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
  let k := 2*m+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hheight : height m = 2*k := by dsimp [height, k]; ring
  obtain ⟨j, hj, hpref⟩ := (evenConstructionRawPrefixSet_mem k p hk).mp hp
  rw [← hpref]
  let t := j/2
  have hpar : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hpar with hpar | hpar
  · have hform : j = 2*t := by dsimp [t]; omega
    have ht : t ≤ 2*k-1 := by dsimp [t]; omega
    rw [hform, evenConstructionPrefix_even k t hk ht]
    have hcoord : t*(4*k) = 2*height m*t := by rw [hheight]; ring
    rw [hcoord]
    exact boundary_with_reflection m a t (by omega)
  · have hform : j = 2*t+1 := by dsimp [t]; omega
    have ht : t < 2*k-1 := by dsimp [t]; omega
    rw [hform, evenConstructionPrefix_odd k t hk ht]
    unfold evenConstructionLowAt
    by_cases htk : t < k
    · rw [if_pos htk]
      have hd : height m-1+1 = 2*k := by rw [hheight]; omega
      have hlo : (2*k-1-2*t)+2*t+1 = 2*k := by omega
      have hmul := congrArg (fun z : ℕ => (2*t+1)*z) hd
      have hcoord : t*(4*k)+(2*k-1-2*t) = (2*t+1)*(height m-1) := by nlinarith
      rw [hcoord]
      exact lower_with_reflection m a t (by simpa only [halfHeight, k] using htk)
    · rw [if_neg htk]
      let u := t-k
      have hu : u < halfHeight m := by dsimp [u]; dsimp [halfHeight, k] at *; omega
      have htu : t = k+u := by dsimp [u]; omega
      have hd : height m-1+1 = 2*k := by rw [hheight]; omega
      have hlo : (4*k-2-2*t)+2*t+2 = 4*k := by omega
      have hmul := congrArg (fun z : ℕ => (2*(t+1))*z) hd
      have hcoord : t*(4*k)+(4*k-2-2*t) = 2*(t+1)*(height m-1) := by nlinarith
      have hcoef : 2*(t+1) = height m+2+2*u := by omega
      rw [hcoord, hcoef]
      exact upper_with_reflection m a u hu

theorem oldCarrier_subset_new (m : ℕ) (a : Choices m) : oldCarrier m ⊆ newCarrier m a := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · exact (baseRow_with_reflection m a x hx).1
  · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact (baseRow_with_reflection m a y hy).2

/-- The literal two new rows use exactly the actual old physical support.
This proof is independent of the B palette theorem. -/
theorem newCarrier_eq_old (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    newCarrier m a = oldCarrier m := by
  symm
  apply eq_of_subset_of_card_le (oldCarrier_subset_new m a)
  rw [oldCarrier_card]
  exact newCarrier_card_le m hm a

theorem physical_rows_partition_old (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    Disjoint (physicalSites (clock m) (rowA m a)) (physicalSites (clock m) (rowB m a)) ∧
    physicalSites (clock m) (rowA m a) ∪ physicalSites (clock m) (rowB m a) = oldCarrier m := by
  let A := physicalSites (clock m) (rowA m a)
  let B := physicalSites (clock m) (rowB m a)
  have hA : A.card ≤ order m := card_image_le.trans_eq (rowA_card m hm a)
  have hB : B.card ≤ order m := card_image_le.trans (rowB_card_le m hm a)
  have hsame : A ∪ B = oldCarrier m := by
    simpa only [A, B, newCarrier, natCarrier, physicalSites, image_union] using newCarrier_eq_old m hm a
  have hcard : (A ∪ B).card = 2*order m := by rw [hsame, oldCarrier_card]
  have hle := card_union_le A B
  constructor
  · exact (card_union_eq_card_add_card (s := A) (t := B)).mp (by omega)
  · exact hsame

theorem natural_rows_disjoint (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    Disjoint (rowA m a) (rowB m a) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact disjoint_left.mp (physical_rows_partition_old m hm a).1
    (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)

end CorralFormalization.EvenSupportPartition
