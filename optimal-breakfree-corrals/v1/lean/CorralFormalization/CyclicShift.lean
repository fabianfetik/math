import CorralFormalization.OrderedGaps

namespace CorralFormalization

/-- Cutting the same cycle at the other boundary exchanges the two site
blocks and their two seam gaps. -/
theorem cyclic_gaps_join_swap
    (U V c d : ℕ) (cs ds : List ℕ)
    (hC : (c :: cs).getLast (by simp) < U)
    (hD : (d :: ds).getLast (by simp) < V) :
    Multiset.ofList
        (cyclicGaps (U + V) c (cs ++ (d :: ds).map (fun x => U + x))) =
      Multiset.ofList
        (cyclicGaps (V + U) d (ds ++ (c :: cs).map (fun x => V + x))) := by
  rw [cyclic_gaps_join_formula U V c d cs ds hC hD,
    cyclic_gaps_join_formula V U d c ds cs hD hC]
  simp only [← Multiset.coe_add, Multiset.coe_singleton]
  ac_rfl

/-- Cutting between two nonempty physical blocks and moving the second
block first preserves the cyclic-gap multiset of their finite site set. -/
theorem finite_set_cyclic_gap_swap (U V : ℕ) (C D : Finset ℕ)
    (hneC : C.Nonempty) (hneD : D.Nonempty)
    (hCbound : ∀ x ∈ C, x < U) (hDbound : ∀ y ∈ D, y < V) :
    finiteCyclicGapInventory (U + V) (C ∪ D.image (fun y => U + y)) =
      finiteCyclicGapInventory (V + U) (D ∪ C.image (fun x => V + x)) := by
  obtain ⟨c, cs, hCorder, hCset⟩ := nonempty_finite_sites_have_ordered_list C hneC
  obtain ⟨d, ds, hDorder, hDset⟩ := nonempty_finite_sites_have_ordered_list D hneD
  have hCbound' : ∀ x ∈ c :: cs, x < U := by
    intro x hx
    apply hCbound x
    rw [← hCset]
    exact List.mem_toFinset.mpr hx
  have hDbound' : ∀ y ∈ d :: ds, y < V := by
    intro y hy
    apply hDbound y
    rw [← hDset]
    exact List.mem_toFinset.mpr hy
  have hC : (c :: cs).getLast (by simp) < U :=
    hCbound' _ (List.getLast_mem (by simp))
  have hD : (d :: ds).getLast (by simp) < V :=
    hDbound' _ (List.getLast_mem (by simp))
  have hJorder := ordered_joined_sites U (c :: cs) (d :: ds)
    hCorder hDorder hCbound'
  have hKorder := ordered_joined_sites V (d :: ds) (c :: cs)
    hDorder hCorder hDbound'
  have hJset : (c :: cs ++ (d :: ds).map (fun x => U + x)).toFinset =
      C ∪ D.image (fun y => U + y) := by
    ext x
    simp [← hCset, ← hDset]
    tauto
  have hKset : (d :: ds ++ (c :: cs).map (fun x => V + x)).toFinset =
      D ∪ C.image (fun y => V + y) := by
    ext x
    simp [← hCset, ← hDset]
    tauto
  have hJnodup : (c :: cs ++ (d :: ds).map (fun x => U + x)).Nodup :=
    hJorder.imp (by intro a b hab; omega)
  have hKnodup : (d :: ds ++ (c :: cs).map (fun x => V + x)).Nodup :=
    hKorder.imp (by intro a b hab; omega)
  have hJsort : (C ∪ D.image (fun y => U + y)).sort (· ≤ ·) =
      c :: cs ++ (d :: ds).map (fun x => U + x) := by
    rw [← hJset]
    exact (List.toFinset_sort (· ≤ ·) hJnodup).2
      (hJorder.imp (by intro a b hab; omega))
  have hKsort : (D ∪ C.image (fun y => V + y)).sort (· ≤ ·) =
      d :: ds ++ (c :: cs).map (fun x => V + x) := by
    rw [← hKset]
    exact (List.toFinset_sort (· ≤ ·) hKnodup).2
      (hKorder.imp (by intro a b hab; omega))
  simpa [finiteCyclicGapInventory, hJsort, hKsort] using
    cyclic_gaps_join_swap U V c d cs ds hC hD

/-- Translating all representatives by the same amount preserves the gap
list, provided the same translated ordering is used. -/
theorem cyclic_gaps_translate (W T c : ℕ) (cs : List ℕ) :
    cyclicGaps W (T + c) (cs.map (fun x => T + x)) = cyclicGaps W c cs := by
  have hgap : adjacentGaps ((T + c) :: cs.map (fun x => T + x)) =
      adjacentGaps (c :: cs) := by
    simpa only [List.map_cons] using adjacent_gaps_translate T (c :: cs)
  have hlast : ((T + c) :: cs.map (fun x => T + x)).getLast (by simp) =
      T + (c :: cs).getLast (by simp) := by
    simpa only [List.map_cons] using
      (List.getLast_map (f := fun x => T + x) (l := c :: cs) (by simp))
  simp only [cyclicGaps, hgap, hlast]
  have heq : T + c + W - (T + (c :: cs).getLast (by simp)) =
      c + W - (c :: cs).getLast (by simp) := by omega
  rw [heq]

/-- Ordinary translation of a finite set preserves the cyclic-gap inventory
when the translated representatives retain their order. -/
theorem finite_set_cyclic_gap_translate (W T : ℕ) (S : Finset ℕ) :
    finiteCyclicGapInventory W (S.image (fun x => T + x)) =
      finiteCyclicGapInventory W S := by
  by_cases hne : S.Nonempty
  · obtain ⟨c, cs, horder, hset⟩ := nonempty_finite_sites_have_ordered_list S hne
    have hmaporder : ((c :: cs).map (fun x => T + x)).Pairwise (· < ·) := by
      rw [List.pairwise_map]
      exact horder.imp (by intro a b hab; omega)
    have hnodup : (c :: cs).Nodup := horder.imp (by intro a b hab; omega)
    have hmapnodup : ((c :: cs).map (fun x => T + x)).Nodup :=
      hmaporder.imp (by intro a b hab; omega)
    have hmapset : ((c :: cs).map (fun x => T + x)).toFinset =
        S.image (fun x => T + x) := by
      ext x
      simp [← hset]
    have hsort : S.sort (· ≤ ·) = c :: cs := by
      rw [← hset]
      exact (List.toFinset_sort (· ≤ ·) hnodup).2
        (horder.imp (by intro a b hab; omega))
    have hmapsort : (S.image (fun x => T + x)).sort (· ≤ ·) =
        (c :: cs).map (fun x => T + x) := by
      rw [← hmapset]
      exact (List.toFinset_sort (· ≤ ·) hmapnodup).2
        (hmaporder.imp (by intro a b hab; omega))
    simpa [finiteCyclicGapInventory, hsort, hmapsort] using
      congrArg Multiset.ofList (cyclic_gaps_translate W T c cs)
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty, finiteCyclicGapInventory]

/-- Translation around a positive clock preserves the finite-set cyclic gap
inventory. The proof splits the actual representatives at the wrap point,
then swaps the two nonempty pieces; the empty-piece cases are ordinary
translations. -/
theorem finite_set_cyclic_gap_rotate_small (W t : ℕ) (S : Finset ℕ)
    (hW : 0 < W) (ht : t < W) (hS : ∀ x ∈ S, x < W) :
    finiteCyclicGapInventory W (S.image (fun x => (x + t) % W)) =
      finiteCyclicGapInventory W S := by
  let cut := W - t
  let C := S.filter (fun x => x < cut)
  let D := (S.filter (fun x => cut ≤ x)).image (fun x => x - cut)
  have hcut : cut + t = W := by dsimp [cut]; omega
  have hCbound : ∀ x ∈ C, x < cut := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hDbound : ∀ y ∈ D, y < t := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxS, hxcut⟩ := Finset.mem_filter.mp hx
    have hxW := hS x hxS
    omega
  have hsplit : S = C ∪ D.image (fun y => cut + y) := by
    ext x
    constructor
    · intro hx
      by_cases hxcut : x < cut
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, hxcut⟩))
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨x - cut, ?_, by omega⟩
        apply Finset.mem_image.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, by omega⟩, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hxC | hxD
      · exact (Finset.mem_filter.mp hxC).1
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxD
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hzS, hzcut⟩ := Finset.mem_filter.mp hz
        simpa [Nat.add_sub_of_le hzcut] using hzS
  have hpartC : C.image (fun x => (x + t) % W) =
      C.image (fun x => t + x) := by
    apply Finset.image_congr
    intro x hx
    dsimp only
    have hxt : x + t < W := by have := hCbound x hx; omega
    rw [Nat.mod_eq_of_lt hxt]
    omega
  have hpartD : D.image (fun y => (cut + y + t) % W) = D := by
    calc
      _ = D.image id := by
        apply Finset.image_congr
        intro y hy
        dsimp only
        have hylt := hDbound y hy
        have hyt : y < W := by omega
        have heq : cut + y + t = W + y := by omega
        rw [heq, Nat.add_mod]
        simp [Nat.mod_eq_of_lt hyt]
      _ = D := Finset.image_id
  have hrot : S.image (fun x => (x + t) % W) =
      D ∪ C.image (fun x => t + x) := by
    rw [hsplit, Finset.image_union, Finset.image_image, hpartC]
    have hD' : D.image ((fun x => (x + t) % W) ∘ (fun y => cut + y)) = D := by
      change D.image (fun y => (cut + y + t) % W) = D
      exact hpartD
    rw [hD', Finset.union_comm]
  by_cases hC : C.Nonempty
  · by_cases hD : D.Nonempty
    · have hswap := finite_set_cyclic_gap_swap cut t C D hC hD hCbound hDbound
      have hsize : t + cut = W := by omega
      rw [hcut, hsize] at hswap
      rw [hrot, hsplit]
      exact hswap.symm
    · have hDempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
      rw [hrot, hsplit, hDempty]
      simpa using finite_set_cyclic_gap_translate W t C
  · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    rw [hrot, hsplit, hCempty]
    simpa using (finite_set_cyclic_gap_translate W cut D).symm

/-- Arbitrary integer-sized natural translations are reduced modulo the
clock before applying the one-cut result. -/
theorem finite_set_cyclic_gap_rotate (W T : ℕ) (S : Finset ℕ)
    (hW : 0 < W) (hS : ∀ x ∈ S, x < W) :
    finiteCyclicGapInventory W (S.image (fun x => (x + T) % W)) =
      finiteCyclicGapInventory W S := by
  have hmap : S.image (fun x => (x + T) % W) =
      S.image (fun x => (x + T % W) % W) := by
    apply Finset.image_congr
    intro x hx
    exact (Nat.add_mod_mod x T W).symm
  rw [hmap]
  exact finite_set_cyclic_gap_rotate_small W (T % W) S hW (Nat.mod_lt _ hW) hS

end CorralFormalization
