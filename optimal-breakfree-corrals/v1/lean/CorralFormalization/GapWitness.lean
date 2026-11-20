import CorralFormalization.GapPermutation

namespace CorralFormalization

/-- Adjacent distances of an ordered list telescope from its first to its
last site. -/
theorem adjacentGaps_sum (c : ℕ) (cs : List ℕ)
    (horder : (c :: cs).Pairwise (· ≤ ·)) :
    (adjacentGaps (c :: cs)).sum = (c :: cs).getLast (by simp) - c := by
  induction cs generalizing c with
  | nil => simp [adjacentGaps]
  | cons d ds ih =>
    have hcd : c ≤ d := (List.pairwise_cons.mp horder).1 d (by simp)
    have htail : (d :: ds).Pairwise (· ≤ ·) := (List.pairwise_cons.mp horder).2
    have hdlast : d ≤ (d :: ds).getLast (by simp) := by
      simpa using htail.rel_getLast (by simp : d ∈ d :: ds)
    simp only [adjacentGaps, List.sum_cons, List.getLast_cons_cons]
    rw [ih d htail]
    omega

/-- The ordered cyclic gap list makes exactly one complete winding. -/
theorem cyclicGaps_sum (W c : ℕ) (cs : List ℕ)
    (horder : (c :: cs).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ c :: cs, x < W) : (cyclicGaps W c cs).sum = W := by
  have hclast : c ≤ (c :: cs).getLast (by simp) := by
    simpa using horder.rel_getLast (by simp : c ∈ c :: cs)
  have hlast : (c :: cs).getLast (by simp) < W :=
    hbound _ (List.getLast_mem (by simp))
  simp only [cyclicGaps, List.sum_append, List.sum_cons, List.sum_nil,
    adjacentGaps_sum c cs horder]
  omega

/-- Strict positivity makes proper prefix sums strictly increase. -/
theorem positive_take_sum_strict (g : List ℕ) (hpos : ∀ x ∈ g, 0 < x)
    (a b : ℕ) (hab : a < b) (hb : b ≤ g.length) :
    (g.take a).sum < (g.take b).sum := by
  have ha : a < g.length := by omega
  have hg : 0 < g[a] := hpos _ (List.getElem_mem ha)
  have hsucc : (g.take a).sum < (g.take (a + 1)).sum := by
    rw [List.sum_take_succ g a ha]
    omega
  exact lt_of_lt_of_le hsucc (List.monotone_sum_take g (by omega : a + 1 ≤ b))

/-- The physical representative of the `j`th nonempty partial sum after
starting at `c`. -/
def gapArrival (W c : ℕ) (g : List ℕ) {n : ℕ} (j : Fin n) : ℕ :=
  (c + (g.take (j.val + 1)).sum) % W

/-- Every partial-sum arrival of the ordered gap list is one of the actual
row's sites. This includes the final return to the first site. -/
theorem gapArrival_mem_sites (W c : ℕ) (cs : List ℕ) {n : ℕ}
    (hW : 0 < W) (horder : (c :: cs).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ c :: cs, x < W)
    (hlen : (cyclicGaps W c cs).length = n) (j : Fin n) :
    gapArrival W c (cyclicGaps W c cs) j ∈ c :: cs := by
  let g := cyclicGaps W c cs
  have hlen' : g.length = n := hlen
  have hcle : c < W := hbound c (by simp)
  have hsum : g.sum = W := cyclicGaps_sum W c cs horder hbound
  by_cases hproper : j.val + 1 < g.length
  · have hp : (g.take (j.val + 1)).sum ∈ properPrefixSites g :=
      (mem_properPrefixSites_iff g _).2 ⟨j.val + 1, hproper, rfl⟩
    have hin : c + (g.take (j.val + 1)).sum ∈
        (properPrefixSites g).map (fun p => c + p) :=
      List.mem_map.mpr ⟨_, hp, rfl⟩
    rw [properPrefixSites_cyclic_inverse W c cs horder] at hin
    have hlt : c + (g.take (j.val + 1)).sum < W := hbound _ hin
    unfold gapArrival
    rw [Nat.mod_eq_of_lt hlt]
    exact hin
  · have hlast : j.val + 1 = g.length := by omega
    unfold gapArrival
    rw [hlast, List.take_of_length_le (by omega), hsum, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hcle]

/-- A non-final arrival has not crossed the chosen cut. -/
theorem gapArrival_proper_value (W c : ℕ) (cs : List ℕ) {n : ℕ}
    (horder : (c :: cs).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ c :: cs, x < W)
    (j : Fin n) (hproper : j.val + 1 < (cyclicGaps W c cs).length) :
    gapArrival W c (cyclicGaps W c cs) j =
      c + ((cyclicGaps W c cs).take (j.val + 1)).sum := by
  let g := cyclicGaps W c cs
  have hp : (g.take (j.val + 1)).sum ∈ properPrefixSites g :=
    (mem_properPrefixSites_iff g _).2 ⟨j.val + 1, hproper, rfl⟩
  have hin : c + (g.take (j.val + 1)).sum ∈
      (properPrefixSites g).map (fun p => c + p) :=
    List.mem_map.mpr ⟨_, hp, rfl⟩
  rw [properPrefixSites_cyclic_inverse W c cs horder] at hin
  have hlt : c + (g.take (j.val + 1)).sum < W := hbound _ hin
  exact Nat.mod_eq_of_lt hlt

/-- The final partial sum returns to the first site. -/
theorem gapArrival_final_value (W c : ℕ) (cs : List ℕ) {n : ℕ}
    (horder : (c :: cs).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ c :: cs, x < W)
    (j : Fin n) (hfinal : j.val + 1 = (cyclicGaps W c cs).length) :
    gapArrival W c (cyclicGaps W c cs) j = c := by
  have hcle : c < W := hbound c (by simp)
  have hsum := cyclicGaps_sum W c cs horder hbound
  unfold gapArrival
  rw [hfinal, List.take_of_length_le (by omega), hsum, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hcle]

/-- For a positive cyclic gap list, the full sequence of partial-sum
arrivals is injective, including the final return. -/
theorem gapArrival_injective (W c : ℕ) (cs : List ℕ) {n : ℕ}
    (horder : (c :: cs).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ c :: cs, x < W)
    (hlen : (cyclicGaps W c cs).length = n)
    (hpos : ∀ x ∈ cyclicGaps W c cs, 0 < x) :
    Function.Injective (gapArrival W c (cyclicGaps W c cs) (n := n)) := by
  intro i j hij
  let g := cyclicGaps W c cs
  have hlen' : g.length = n := hlen
  by_cases hi : i.val + 1 < g.length
  · have hival := gapArrival_proper_value W c cs horder hbound i hi
    by_cases hj : j.val + 1 < g.length
    · have hjval := gapArrival_proper_value W c cs horder hbound j hj
      rw [hival, hjval] at hij
      apply Fin.ext
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have hs := positive_take_sum_strict g hpos (i.val + 1) (j.val + 1)
          (by omega) (by omega)
        dsimp [g] at hs
        omega
      · have hs := positive_take_sum_strict g hpos (j.val + 1) (i.val + 1)
          (by omega) (by omega)
        dsimp [g] at hs
        omega
    · have hjlast : j.val + 1 = g.length := by omega
      have hjval := gapArrival_final_value W c cs horder hbound j hjlast
      have hs := positive_take_sum_strict g hpos 0 (i.val + 1) (by omega) (by omega)
      simp only [List.take_zero, List.sum_nil] at hs
      dsimp [g] at hs
      rw [hival, hjval] at hij
      omega
  · have hilast : i.val + 1 = g.length := by omega
    have hival := gapArrival_final_value W c cs horder hbound i hilast
    by_cases hj : j.val + 1 < g.length
    · have hjval := gapArrival_proper_value W c cs horder hbound j hj
      have hs := positive_take_sum_strict g hpos 0 (j.val + 1) (by omega) (by omega)
      simp only [List.take_zero, List.sum_nil] at hs
      dsimp [g] at hs
      rw [hival, hjval] at hij
      omega
    · have hjlast : j.val + 1 = g.length := by omega
      apply Fin.ext
      omega

end CorralFormalization
