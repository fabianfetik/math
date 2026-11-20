import CorralFormalization.CyclicShift

namespace CorralFormalization

/-- The proper prefix sums of a gap word in their natural chronological
order. A nonempty word contributes the initial site zero. -/
def properPrefixSites : List ℕ → List ℕ
  | [] => []
  | x :: xs => 0 :: (properPrefixSites xs).map (fun y => x + y)

theorem properPrefixSites_length (g : List ℕ) :
    (properPrefixSites g).length = g.length := by
  induction g with
  | nil => rfl
  | cons x xs ih => simp [properPrefixSites, ih]

/-- The recursive list is exactly the set of sums of the proper prefixes. -/
theorem mem_properPrefixSites_iff (g : List ℕ) (p : ℕ) :
    p ∈ properPrefixSites g ↔ ∃ j, j < g.length ∧ (g.take j).sum = p := by
  induction g generalizing p with
  | nil => simp [properPrefixSites]
  | cons a xs ih =>
    simp only [properPrefixSites, List.mem_cons, List.mem_map]
    constructor
    · intro hp
      rcases hp with hp | ⟨q, hq, hpoint⟩
      · subst p
        exact ⟨0, by simp, by simp⟩
      · obtain ⟨j, hj, hqj⟩ := (ih q).1 hq
        refine ⟨j + 1, by simp; omega, ?_⟩
        simp only [List.take_succ_cons, List.sum_cons]
        rw [hqj]
        exact hpoint
    · rintro ⟨j, hj, hp⟩
      cases j with
      | zero =>
        left
        simpa using hp.symm
      | succ k =>
        right
        refine ⟨(xs.take k).sum, ?_, ?_⟩
        · apply (ih _).2
          exact ⟨k, by simp at hj; omega, rfl⟩
        · simpa only [List.take_succ_cons, List.sum_cons] using hp

/-- Positive gap words have strictly increasing proper prefix sites. -/
theorem properPrefixSites_strict (g : List ℕ)
    (hpos : ∀ x ∈ g, 0 < x) : (properPrefixSites g).Pairwise (· < ·) := by
  induction g with
  | nil => simp [properPrefixSites]
  | cons a xs ih =>
    have ha : 0 < a := hpos a (by simp)
    have htail : ∀ x ∈ xs, 0 < x := by
      intro x hx
      exact hpos x (by simp [hx])
    simp only [properPrefixSites, List.pairwise_cons, List.pairwise_map]
    constructor
    · intro y hy
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
      omega
    · exact (ih htail).imp (by intro a b hab; omega)

/-- The cyclic gaps of the chronological prefix sites are exactly the gap
word, including the final wrap. -/
theorem properPrefixSites_cyclic_gaps (x : ℕ) (xs : List ℕ) :
    cyclicGaps (x :: xs).sum 0 ((properPrefixSites xs).map (fun y => x + y)) =
      x :: xs := by
  induction xs generalizing x with
  | nil => simp [properPrefixSites, cyclicGaps, adjacentGaps]
  | cons y ys ih =>
    have hlast : (0 :: (properPrefixSites (y :: ys)).map (fun z => x + z)).getLast (by simp) =
        x + (properPrefixSites (y :: ys)).getLast (by simp [properPrefixSites]) := by
      have hne : (properPrefixSites (y :: ys)).map (fun z => x + z) ≠ [] := by
        simp [properPrefixSites]
      rw [List.getLast_cons hne]
      exact List.getLast_map hne
    have hadj : adjacentGaps (0 :: (properPrefixSites (y :: ys)).map (fun z => x + z)) =
        x :: adjacentGaps (properPrefixSites (y :: ys)) := by
      simp only [properPrefixSites, List.map_cons, Nat.add_zero, adjacentGaps,
        Nat.sub_zero]
      have htranslate := adjacent_gaps_translate x (0 :: (properPrefixSites ys).map (fun z => y + z))
      simp only [List.map_cons, Nat.add_zero] at htranslate
      rw [htranslate]
    have hwrap : (x + (y + ys.sum)) -
        (x + (properPrefixSites (y :: ys)).getLast (by simp [properPrefixSites])) =
        (y + ys.sum) - (properPrefixSites (y :: ys)).getLast (by simp [properPrefixSites]) := by
      omega
    simp only [cyclicGaps, List.sum_cons, Nat.zero_add, hlast, hadj]
    rw [hwrap]
    have ih' := ih y
    simpa only [cyclicGaps, List.sum_cons, Nat.zero_add, properPrefixSites,
      List.cons_append] using
      congrArg (fun z : List ℕ => x :: z) ih'

/-- Sorting the actual proper-prefix finite set and taking its cyclic gaps
recovers the word, when every gap is positive. -/
theorem properPrefixSites_finite_gaps (x : ℕ) (xs : List ℕ)
    (hpos : ∀ z ∈ x :: xs, 0 < z) :
    finiteCyclicGapInventory (x :: xs).sum (properPrefixSites (x :: xs)).toFinset =
      Multiset.ofList (x :: xs) := by
  have horder := properPrefixSites_strict (x :: xs) hpos
  have hnodup : (properPrefixSites (x :: xs)).Nodup :=
    horder.imp (by intro a b hab; omega)
  have hsort : ((properPrefixSites (x :: xs)).toFinset).sort (· ≤ ·) =
      properPrefixSites (x :: xs) :=
    (List.toFinset_sort (· ≤ ·) hnodup).2 (horder.imp (by intro a b hab; omega))
  unfold finiteCyclicGapInventory
  rw [hsort]
  change Multiset.ofList
      (cyclicGaps (x :: xs).sum 0 ((properPrefixSites xs).map (fun y => x + y))) =
    Multiset.ofList (x :: xs)
  exact congrArg Multiset.ofList (properPrefixSites_cyclic_gaps x xs)

/-- Every proper prefix of a positive nonempty word is strictly before the
end of its one winding. -/
theorem properPrefixSites_lt_sum (g : List ℕ) (hpos : ∀ x ∈ g, 0 < x)
    (p : ℕ) (hp : p ∈ properPrefixSites g) : p < g.sum := by
  obtain ⟨j, hj, hpj⟩ := (mem_properPrefixSites_iff g p).1 hp
  have hne : g.drop j ≠ [] := by
    intro hnil
    have := List.drop_eq_nil_iff.mp hnil
    omega
  have hdrop : 0 < (g.drop j).sum := by
    apply List.sum_pos
    · intro x hx
      exact hpos x (List.mem_of_mem_drop hx)
    · exact hne
  have hsum := List.sum_take_add_sum_drop g j
  omega

/-- Reading adjacent distances and any final wrap, then taking proper
prefixes, reconstructs the original ordered physical sites. -/
theorem properPrefixSites_adjacent_inverse (c : ℕ) (cs : List ℕ) (wrap : ℕ)
    (horder : (c :: cs).Pairwise (· ≤ ·)) :
    (properPrefixSites (adjacentGaps (c :: cs) ++ [wrap])).map (fun p => c + p) =
      c :: cs := by
  induction cs generalizing c with
  | nil => simp [adjacentGaps, properPrefixSites]
  | cons d ds ih =>
    have hcd : c ≤ d := (List.pairwise_cons.mp horder).1 d (by simp)
    have htail : (d :: ds).Pairwise (· ≤ ·) := (List.pairwise_cons.mp horder).2
    have hind := ih d htail
    have hsub : c + (d - c) = d := Nat.add_sub_of_le hcd
    simp only [adjacentGaps, List.cons_append, properPrefixSites, List.map_cons,
      Nat.add_zero, List.map_map]
    congr 1
    have hfun : ((fun p : ℕ => c + p) ∘ (fun y => d - c + y)) =
        (fun p => d + p) := by
      funext p
      simp only [Function.comp_apply, ← Nat.add_assoc, hsub]
    rw [hfun]
    exact hind

/-- The sorted sites of a nonempty finite row are recovered exactly from
the proper prefixes of its cyclic-gap list. -/
theorem properPrefixSites_cyclic_inverse (W c : ℕ) (cs : List ℕ)
    (horder : (c :: cs).Pairwise (· ≤ ·)) :
    (properPrefixSites (cyclicGaps W c cs)).map (fun p => c + p) = c :: cs := by
  exact properPrefixSites_adjacent_inverse c cs _ horder

end CorralFormalization
