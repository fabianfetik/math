import CorralFormalization.Basic

namespace CorralFormalization

/-- Positive distances between consecutive listed sites. In applications the
list is strictly increasing; the definition itself uses natural subtraction. -/
def adjacentGaps : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | x :: y :: xs => (y - x) :: adjacentGaps (y :: xs)

/-- Translating every site of a list preserves its interior gaps. -/
theorem adjacent_gaps_translate (U : ℕ) (xs : List ℕ) :
    adjacentGaps (xs.map (fun x => U + x)) = adjacentGaps xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [List.map_cons, adjacentGaps, Nat.add_sub_add_left]
      have ih' : adjacentGaps ((U + y) :: ys.map (fun x => U + x)) =
          adjacentGaps (y :: ys) := by simpa only [List.map_cons] using ih
      rw [ih']

/-- Concatenating nonempty ordered site lists retains their interior gaps and
adds the single distance from the end of the first to the start of the second.
Ordering is supplied separately when these lists represent physical rows. -/
theorem adjacent_gaps_append (C D : List ℕ) (hC : C ≠ []) (hD : D ≠ []) :
    adjacentGaps (C ++ D) = adjacentGaps C ++
      [D.head hD - C.getLast hC] ++ adjacentGaps D := by
  induction C with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases D with
      | nil => contradiction
      | cons y ys => simp [adjacentGaps]
    | cons y ys =>
      have htail : y :: ys ≠ [] := by simp
      simp only [List.cons_append, adjacentGaps, List.cons_append]
      have ih' := ih htail
      simp only [List.cons_append] at ih'
      rw [ih']
      simp

/-- The physical ordering survives concatenation when the first component's
sites all lie before the cut and the second component is translated by it. -/
theorem ordered_joined_sites (U : ℕ) (C D : List ℕ)
    (hC : C.Pairwise (· < ·)) (hD : D.Pairwise (· < ·))
    (hbound : ∀ x ∈ C, x < U) :
    (C ++ D.map (fun x => U + x)).Pairwise (· < ·) := by
  rw [List.pairwise_append]
  refine ⟨hC, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact hD.imp (by intro a b hab; omega)
  · intro x hx y hy
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
    have := hbound x hx
    omega

/-- Cyclic gaps of a nonempty list of sites, with its first site explicit.
When the list is strictly increasing inside a clock of width `W`, these are
the physical positive gaps, including the final wrap. -/
def cyclicGaps (W c : ℕ) (cs : List ℕ) : List ℕ :=
  adjacentGaps (c :: cs) ++ [c + W - (c :: cs).getLast (by simp)]

/-- The concrete gap list after joining two nonempty component lists. The
two displayed cross-block distances are the two physical seams. -/
theorem cyclic_gaps_join_formula
    (U V c d : ℕ) (cs ds : List ℕ)
    (hC : (c :: cs).getLast (by simp) < U)
    (hD : (d :: ds).getLast (by simp) < V) :
    cyclicGaps (U + V) c (cs ++ (d :: ds).map (fun x => U + x)) =
      adjacentGaps (c :: cs) ++
        [(U - (c :: cs).getLast (by simp)) + d] ++
      adjacentGaps (d :: ds) ++
        [(V - (d :: ds).getLast (by simp)) + c] := by
  have hnonempty : (d :: ds).map (fun x => U + x) ≠ [] := by simp
  have happ := adjacent_gaps_append (c :: cs) ((d :: ds).map (fun x => U + x))
    (by simp) hnonempty
  have hlast : (c :: (cs ++ (d :: ds).map (fun x => U + x))).getLast (by simp) =
      U + (d :: ds).getLast (by simp) := by
    simp
    simpa only [List.map_cons] using
      (List.getLast_map (f := fun x => U + x) hnonempty)
  have hseam1 : U + d - (c :: cs).getLast (by simp) =
      (U - (c :: cs).getLast (by simp)) + d := by omega
  have hseam2 : c + (U + V) - (U + (d :: ds).getLast (by simp)) =
      (V - (d :: ds).getLast (by simp)) + c := by omega
  simp only [cyclicGaps, hlast]
  have happ' : adjacentGaps (c :: (cs ++ (d :: ds).map (fun x => U + x))) =
      adjacentGaps (c :: cs) ++ [U + d - (c :: cs).getLast (by simp)] ++
        adjacentGaps ((d :: ds).map (fun x => U + x)) := by
    simpa using happ
  rw [happ', adjacent_gaps_translate, hseam1, hseam2]

/-- The full cyclic-gap multiset of the physically concatenated ordered
lists is the union of the two local cyclic-gap multisets whenever their
first points or their tail deficits agree. The two endpoint bounds are
exactly those needed for the physical cuts. -/
theorem cyclic_gaps_join_inventory
    (U V c d : ℕ) (cs ds : List ℕ)
    (hC : (c :: cs).getLast (by simp) < U)
    (hD : (d :: ds).getLast (by simp) < V)
    (hmatch : c = d ∨ U - (c :: cs).getLast (by simp) =
      V - (d :: ds).getLast (by simp)) :
    Multiset.ofList
        (cyclicGaps (U + V) c (cs ++ (d :: ds).map (fun x => U + x))) =
      Multiset.ofList (cyclicGaps U c cs) + Multiset.ofList (cyclicGaps V d ds) := by
  let tC := U - (c :: cs).getLast (by simp)
  let tD := V - (d :: ds).getLast (by simp)
  have hwrapC : c + U - (c :: cs).getLast (by simp) = c + tC := by
    dsimp [tC]
    omega
  have hwrapD : d + V - (d :: ds).getLast (by simp) = d + tD := by
    dsimp [tD]
    omega
  have hseams : Multiset.ofList [tC + d, tD + c] =
      Multiset.ofList [c + tC, d + tD] := by
    rcases hmatch with hheads | htails
    · simpa [newSeams, oldWraps] using
        seam_inventory_restore_of_equal_heads c tC d tD hheads
    · have htails' : tC = tD := htails
      simpa [newSeams, oldWraps] using
        seam_inventory_restore_of_equal_tails c tC d tD htails'
  rw [cyclic_gaps_join_formula U V c d cs ds hC hD]
  simp only [cyclicGaps, hwrapC, hwrapD]
  change (↑(adjacentGaps (c :: cs) ++ [tC + d] ++ adjacentGaps (d :: ds) ++
      [tD + c]) : Multiset ℕ) =
    ↑(adjacentGaps (c :: cs) ++ [c + tC]) + ↑(adjacentGaps (d :: ds) ++ [d + tD])
  simp only [← Multiset.coe_add, Multiset.coe_singleton]
  have hseams' : ({tC + d} : Multiset ℕ) + {tD + c} = {c + tC} + {d + tD} := by
    simpa only [← Multiset.coe_singleton, Multiset.coe_add, List.singleton_append] using hseams
  calc
    _ = (↑(adjacentGaps (c :: cs)) : Multiset ℕ) + ↑(adjacentGaps (d :: ds)) +
        ({tC + d} + {tD + c}) := by ac_rfl
    _ = (↑(adjacentGaps (c :: cs)) : Multiset ℕ) + ↑(adjacentGaps (d :: ds)) +
        ({c + tC} + {d + tD}) := by rw [hseams']
    _ = _ := by ac_rfl

/-- The list-level physical join: two strictly ordered, nonempty components
inside their respective intervals yield an ordered list of exactly the
combined sites, and the cyclic-gap inventory is preserved under either
endpoint match. Connecting concrete finite-set rows to these ordered lists is
a separate representation step. -/
theorem ordered_physical_join_contract
    (U V c d : ℕ) (cs ds : List ℕ)
    (hCorder : (c :: cs).Pairwise (· < ·))
    (hDorder : (d :: ds).Pairwise (· < ·))
    (hCbound : ∀ x ∈ c :: cs, x < U)
    (hDbound : ∀ y ∈ d :: ds, y < V)
    (hmatch : c = d ∨ U - (c :: cs).getLast (by simp) =
      V - (d :: ds).getLast (by simp)) :
    (c :: cs ++ (d :: ds).map (fun x => U + x)).Pairwise (· < ·) ∧
    (c :: cs ++ (d :: ds).map (fun x => U + x)).toFinset =
      (c :: cs).toFinset ∪ ((d :: ds).toFinset.image (fun x => U + x)) ∧
    Multiset.ofList
        (cyclicGaps (U + V) c (cs ++ (d :: ds).map (fun x => U + x))) =
      Multiset.ofList (cyclicGaps U c cs) + Multiset.ofList (cyclicGaps V d ds) := by
  have hC : (c :: cs).getLast (by simp) < U :=
    hCbound _ (List.getLast_mem (by simp))
  have hD : (d :: ds).getLast (by simp) < V :=
    hDbound _ (List.getLast_mem (by simp))
  refine ⟨?_, ?_, cyclic_gaps_join_inventory U V c d cs ds hC hD hmatch⟩
  · exact ordered_joined_sites U (c :: cs) (d :: ds) hCorder hDorder hCbound
  · ext x
    simp
    tauto

/-- Every nonempty finite site set has a strictly increasing enumeration
whose finite-set image is exactly the original set. -/
theorem nonempty_finite_sites_have_ordered_list (S : Finset ℕ) (hne : S.Nonempty) :
    ∃ c cs, (c :: cs).Pairwise (· < ·) ∧ (c :: cs).toFinset = S := by
  obtain ⟨x, hx⟩ := hne
  have hxsort : x ∈ S.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).2 hx
  cases hlist : S.sort (· ≤ ·) with
  | nil => simp [hlist] at hxsort
  | cons c cs =>
    refine ⟨c, cs, ?_, ?_⟩
    · have hsorted : (S.sort (· ≤ ·)).Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
      rw [hlist] at hsorted
      exact hsorted
    · simpa [hlist] using Finset.sort_toFinset S (· ≤ ·)

/-- In a strictly increasing nonempty enumeration, the first and final list
elements are the minimum and maximum of the represented finite site set. -/
theorem ordered_list_extrema (c : ℕ) (cs : List ℕ)
    (horder : (c :: cs).Pairwise (· < ·)) :
    ∃ hne : (c :: cs).toFinset.Nonempty,
      (c :: cs).toFinset.min' hne = c ∧
      (c :: cs).toFinset.max' hne = (c :: cs).getLast (by simp) := by
  have hne : (c :: cs).toFinset.Nonempty := ⟨c, by simp⟩
  have hle : (c :: cs).Pairwise (· ≤ ·) := horder.imp (by intro a b hab; omega)
  have hmin : (c :: cs).toFinset.min' hne = c := by
    apply le_antisymm
    · exact Finset.min'_le _ c (by simp)
    · apply Finset.le_min' _ hne c
      intro x hx
      have hxlist : x ∈ c :: cs := by simpa using hx
      simpa using hle.rel_head hxlist
  have hmax : (c :: cs).toFinset.max' hne = (c :: cs).getLast (by simp) := by
    apply le_antisymm
    · apply Finset.max'_le _ hne
      intro x hx
      have hxlist : x ∈ c :: cs := by simpa using hx
      simpa using hle.rel_getLast hxlist
    · exact Finset.le_max' _ _
        (List.mem_toFinset.mpr (List.getLast_mem (by simp : c :: cs ≠ [])))
  exact ⟨hne, hmin, hmax⟩

/-- Cyclic-gap multiset of a finite set of physical sites, obtained by
sorting its representatives. The empty case is defined as the empty multiset;
the joining theorem below is stated only for nonempty component sets. -/
def finiteCyclicGapInventory (W : ℕ) (S : Finset ℕ) : Multiset ℕ :=
  match S.sort (· ≤ ·) with
  | [] => 0
  | c :: cs => Multiset.ofList (cyclicGaps W c cs)

/-- Concatenating two nonempty physical site sets preserves the union of their cyclic gap
multisets if their heads or tail deficits agree. -/
theorem finite_set_cyclic_gap_join
    (U V : ℕ) (C D : Finset ℕ) (hneC : C.Nonempty) (hneD : D.Nonempty)
    (hCbound : ∀ x ∈ C, x < U) (hDbound : ∀ y ∈ D, y < V)
    (hmatch : C.min' hneC = D.min' hneD ∨ U - C.max' hneC = V - D.max' hneD) :
    finiteCyclicGapInventory (U + V) (C ∪ D.image (fun y => U + y)) =
      finiteCyclicGapInventory U C + finiteCyclicGapInventory V D := by
  obtain ⟨c, cs, hCorder, hCset⟩ := nonempty_finite_sites_have_ordered_list C hneC
  obtain ⟨d, ds, hDorder, hDset⟩ := nonempty_finite_sites_have_ordered_list D hneD
  obtain ⟨_, hCmin, hCmax⟩ := ordered_list_extrema c cs hCorder
  obtain ⟨_, hDmin, hDmax⟩ := ordered_list_extrema d ds hDorder
  have hCmin' : C.min' hneC = c := by simpa [hCset] using hCmin
  have hCmax' : C.max' hneC = (c :: cs).getLast (by simp) := by
    simpa [hCset] using hCmax
  have hDmin' : D.min' hneD = d := by simpa [hDset] using hDmin
  have hDmax' : D.max' hneD = (d :: ds).getLast (by simp) := by
    simpa [hDset] using hDmax
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
  have hmatch' : c = d ∨ U - (c :: cs).getLast (by simp) =
      V - (d :: ds).getLast (by simp) := by
    simpa [hCmin', hCmax', hDmin', hDmax'] using hmatch
  obtain ⟨horder, hjoined, hgaps⟩ :=
    ordered_physical_join_contract U V c d cs ds hCorder hDorder hCbound' hDbound' hmatch'
  have hCnodup : (c :: cs).Nodup := hCorder.imp (by intro a b hab; omega)
  have hDnodup : (d :: ds).Nodup := hDorder.imp (by intro a b hab; omega)
  have hJnodup : (c :: cs ++ (d :: ds).map (fun x => U + x)).Nodup :=
    horder.imp (by intro a b hab; omega)
  have hCsort : C.sort (· ≤ ·) = c :: cs := by
    rw [← hCset]
    exact (List.toFinset_sort (· ≤ ·) hCnodup).2 (hCorder.imp (by intro a b hab; omega))
  have hDsort : D.sort (· ≤ ·) = d :: ds := by
    rw [← hDset]
    exact (List.toFinset_sort (· ≤ ·) hDnodup).2 (hDorder.imp (by intro a b hab; omega))
  have hJsort : (C ∪ D.image (fun y => U + y)).sort (· ≤ ·) =
      c :: cs ++ (d :: ds).map (fun x => U + x) := by
    rw [← hCset, ← hDset, ← hjoined]
    exact (List.toFinset_sort (· ≤ ·) hJnodup).2 (horder.imp (by intro a b hab; omega))
  simpa [finiteCyclicGapInventory, hCsort, hDsort, hJsort] using hgaps

end CorralFormalization
