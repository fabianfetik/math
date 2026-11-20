import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Counts

/-! # Join two actual disjoint components by one fresh directed edge -/

open scoped Classical
namespace EndpointFactor.OrdinaryFragments
open FragmentChecksum
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

private theorem labels_append (p q : List G) (hp : p ≠ []) (hq : q ≠ []) :
    labels (p ++ q) = labels p ++ [firstOrZero q-lastOrZero p] ++ labels q := by
  cases q with
  | nil => contradiction
  | cons b tail =>
    calc
      labels (p ++ b :: tail) = labels (p.dropLast ++ p.getLast hp :: b :: tail) := by
        congr 1
        simpa [List.append_assoc] using
          congrArg (fun xs => xs ++ b :: tail) (List.dropLast_append_getLast hp).symm
      _ = labels (p.dropLast ++ [p.getLast hp]) ++
          edgeLabels (fun a b : G => b-a) (p.getLast hp :: b :: tail) :=
        edgeLabels_append_pivot _ _ _ _
      _ = labels p ++ [firstOrZero (b :: tail)-lastOrZero p] ++ labels (b :: tail) := by
        simp [List.dropLast_append_getLast hp, edgeLabels, List.append_assoc,
          firstOrZero, lastOrZero, List.getLast?_eq_some_getLast hp, labels]

namespace Family
variable (F : Family G) (i j : F.Index) (hij : i ≠ j)

def joinColor : G := F.first j-F.last i

private theorem joined_rainbow (hij : i ≠ j) (hfresh : F.joinColor i j ∉ F.colors) :
    (labels (F.path i ++ F.path j)).Nodup := by
  rw [labels_append _ _ (F.nonempty i) (F.nonempty j)]
  change (labels (F.path i) ++ [F.joinColor i j] ++ labels (F.path j)).Nodup
  have hic : List.Disjoint (labels (F.path i)) [F.joinColor i j] := by
    apply List.disjoint_left.mpr
    intro c hc hc'
    have he : c = F.joinColor i j := by simpa using hc'
    exact hfresh (he ▸ (F.mem_colors _).mpr ⟨i, hc⟩)
  apply ((F.rainbow i).append (by simp) hic).append (F.rainbow j)
  apply List.disjoint_left.mpr
  intro c hc hc'
  rcases List.mem_append.mp hc with hc | hc
  · exact List.disjoint_left.mp (F.color_disjoint i j hij) hc hc'
  · have he : c = F.joinColor i j := by simpa using hc
    exact hfresh (he ▸ (F.mem_colors _).mpr ⟨j, hc'⟩)

private theorem joined_color_disjoint (k : F.Index) (hki : k ≠ i) (hkj : k ≠ j)
    (hfresh : F.joinColor i j ∉ F.colors) :
    List.Disjoint (labels (F.path i ++ F.path j)) (labels (F.path k)) := by
  rw [labels_append _ _ (F.nonempty i) (F.nonempty j)]
  apply List.disjoint_left.mpr
  intro c hc hk
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · exact List.disjoint_left.mp (F.color_disjoint i k hki.symm) hc hk
    · have he : c = F.joinColor i j := by simpa [joinColor, first, last] using hc
      exact hfresh (he ▸ (F.mem_colors _).mpr ⟨k, hk⟩)
  · exact List.disjoint_left.mp (F.color_disjoint j k hkj.symm) hc hk

/-- The second component is removed from the key set and its entire
physical path is appended to the first. The inserted edge has its actual
physical difference. This operation cannot hide a cycle. -/
def merge (hfresh : F.joinColor i j ∉ F.colors) : Family G where
  Index := {k : F.Index // k ≠ j}
  indexFintype := inferInstance
  path := fun k => if k.val = i then F.path i ++ F.path j else F.path k.val
  nonempty := by
    intro k
    split_ifs with hk
    · simp [F.nonempty i, F.nonempty j]
    · exact F.nonempty k.val
  simple := by
    intro k
    split_ifs with hk
    · exact (F.simple i).append (F.simple j) (F.disjoint i j hij)
    · exact F.simple k.val
  disjoint := by
    intro k l hkl
    by_cases hk : k.val = i
    · by_cases hl : l.val = i
      · exact False.elim (hkl (Subtype.ext (hk.trans hl.symm)))
      · simp only [if_pos hk, if_neg hl]
        apply List.disjoint_left.mpr
        intro g hg hl'
        rcases List.mem_append.mp hg with hg | hg
        · exact List.disjoint_left.mp (F.disjoint i l.val (Ne.symm hl)) hg hl'
        · exact List.disjoint_left.mp (F.disjoint j l.val (Ne.symm l.property)) hg hl'
    · by_cases hl : l.val = i
      · simp only [if_neg hk, if_pos hl]
        apply List.disjoint_left.mpr
        intro g hg hl'
        rcases List.mem_append.mp hl' with hl' | hl'
        · exact List.disjoint_left.mp (F.disjoint k.val i hk) hg hl'
        · exact List.disjoint_left.mp (F.disjoint k.val j k.property) hg hl'
      · simp only [if_neg hk, if_neg hl]
        exact F.disjoint k.val l.val (fun h => hkl (Subtype.ext h))
  rainbow := by
    intro k
    split_ifs with hk
    · exact F.joined_rainbow i j hij hfresh
    · exact F.rainbow k.val
  color_disjoint := by
    intro k l hkl
    by_cases hk : k.val = i
    · by_cases hl : l.val = i
      · exact False.elim (hkl (Subtype.ext (hk.trans hl.symm)))
      · simp only [if_pos hk, if_neg hl]
        exact F.joined_color_disjoint i j l.val hl l.property hfresh
    · by_cases hl : l.val = i
      · simp only [if_neg hk, if_pos hl]
        exact (F.joined_color_disjoint i j k.val hk k.property hfresh).symm
      · simp only [if_neg hk, if_neg hl]
        exact F.color_disjoint k.val l.val (fun h => hkl (Subtype.ext h))

section Inventories
variable (hfresh : F.joinColor i j ∉ F.colors)

private theorem merge_first (k : (F.merge i j hij hfresh).Index) :
    (F.merge i j hij hfresh).first k = F.first k.val := by
  change firstOrZero (if k.val = i then F.path i ++ F.path j else F.path k.val) = _
  split_ifs with hk
  · calc
      firstOrZero (F.path i ++ F.path j) = F.first i := by
        cases hp : F.path i with
        | nil => exact False.elim (F.nonempty i hp)
        | cons a tail => simp [first, firstOrZero, hp]
      _ = F.first k.val := congrArg F.first hk.symm
  · rfl

private theorem merge_last (k : (F.merge i j hij hfresh).Index) :
    (F.merge i j hij hfresh).last k = if k.val = i then F.last j else F.last k.val := by
  change lastOrZero (if k.val = i then F.path i ++ F.path j else F.path k.val) = _
  split_ifs with hk
  · simp [lastOrZero, List.getLast?_append, List.getLast?_eq_some_getLast (F.nonempty j), last]
  · rfl

@[simp] theorem merge_vertices : (F.merge i j hij hfresh).vertices = F.vertices := by
  ext g
  rw [mem_vertices, mem_vertices]
  constructor
  · rintro ⟨k, hk⟩
    change g ∈ (if k.val = i then F.path i ++ F.path j else F.path k.val) at hk
    split_ifs at hk with hki
    · rcases List.mem_append.mp hk with hk | hk
      · exact ⟨i, hk⟩
      · exact ⟨j, hk⟩
    · exact ⟨k.val, hk⟩
  · rintro ⟨k, hk⟩
    by_cases hkj : k = j
    · refine ⟨⟨i, hij⟩, ?_⟩
      change g ∈ (if i = i then F.path i ++ F.path j else F.path i)
      rw [if_pos rfl]
      exact List.mem_append_right _ (hkj ▸ hk)
    · refine ⟨⟨k, hkj⟩, ?_⟩
      change g ∈ (if k = i then F.path i ++ F.path j else F.path k)
      split_ifs with hki
      · exact List.mem_append_left _ (hki ▸ hk)
      · exact hk

@[simp] theorem merge_colors :
    (F.merge i j hij hfresh).colors = insert (F.joinColor i j) F.colors := by
  ext c
  rw [mem_colors, Finset.mem_insert, mem_colors]
  constructor
  · rintro ⟨k, hk⟩
    change c ∈ labels (if k.val = i then F.path i ++ F.path j else F.path k.val) at hk
    split_ifs at hk with hki
    · rw [labels_append _ _ (F.nonempty i) (F.nonempty j)] at hk
      rcases List.mem_append.mp hk with hk | hk
      · rcases List.mem_append.mp hk with hk | hk
        · exact Or.inr ⟨i, hk⟩
        · exact Or.inl (by simpa [joinColor, first, last] using hk)
      · exact Or.inr ⟨j, hk⟩
    · exact Or.inr ⟨k.val, hk⟩
  · rintro (rfl | ⟨k, hk⟩)
    · refine ⟨⟨i, hij⟩, ?_⟩
      simp [merge, labels_append _ _ (F.nonempty i) (F.nonempty j), joinColor, first, last]
    · by_cases hkj : k = j
      · refine ⟨⟨i, hij⟩, ?_⟩
        change c ∈ labels (if i = i then F.path i ++ F.path j else F.path i)
        rw [if_pos rfl, labels_append _ _ (F.nonempty i) (F.nonempty j)]
        exact List.mem_append_right _ (hkj ▸ hk)
      · refine ⟨⟨k, hkj⟩, ?_⟩
        change c ∈ labels (if k = i then F.path i ++ F.path j else F.path k)
        split_ifs with hki
        · rw [labels_append _ _ (F.nonempty i) (F.nonempty j)]
          exact List.mem_append_left _ (List.mem_append_left _ (hki ▸ hk))
        · exact hk

@[simp] theorem merge_starts :
    (F.merge i j hij hfresh).starts = F.starts.erase (F.first j) := by
  ext g
  rw [mem_starts, Finset.mem_erase, mem_starts]
  constructor
  · rintro ⟨k, hk⟩
    rw [F.merge_first i j hij hfresh k] at hk
    refine ⟨?_, ⟨k.val, hk⟩⟩
    intro he
    exact k.property (F.first_injective (hk.trans he))
  · rintro ⟨hne, k, hk⟩
    have hkj : k ≠ j := by intro h; exact hne (hk.symm.trans (congrArg F.first h))
    exact ⟨⟨k, hkj⟩, (F.merge_first i j hij hfresh _).trans hk⟩

@[simp] theorem merge_ends :
    (F.merge i j hij hfresh).ends = F.ends.erase (F.last i) := by
  ext g
  rw [mem_ends, Finset.mem_erase, mem_ends]
  constructor
  · rintro ⟨k, hk⟩
    rw [F.merge_last i j hij hfresh k] at hk
    split_ifs at hk with hki
    · exact ⟨fun he => hij (F.last_injective (he.symm.trans hk.symm)), ⟨j, hk⟩⟩
    · exact ⟨fun he => hki (F.last_injective (hk.trans he)), ⟨k.val, hk⟩⟩
  · rintro ⟨hne, k, hk⟩
    have hki : k ≠ i := by intro h; exact hne (hk.symm.trans (congrArg F.last h))
    by_cases hkj : k = j
    · refine ⟨⟨i, hij⟩, ?_⟩
      exact (F.merge_last i j hij hfresh (⟨i, hij⟩ : (F.merge i j hij hfresh).Index)).trans
        (by simpa [hkj] using hk)
    · refine ⟨⟨k, hkj⟩, ?_⟩
      exact (F.merge_last i j hij hfresh (⟨k, hkj⟩ : (F.merge i j hij hfresh).Index)).trans
        (by simpa [hki] using hk)

/-- Original primary donors other than the consumed one remain actual
primary endpoints. The target component is explicitly extra. -/
theorem merge_preserves_primaryEnds (B : Finset G) (hjB : F.first j ∉ B)
    {a : G} (ha : a ∈ F.primaryEnds B) (hai : a ≠ F.last i) :
    a ∈ (F.merge i j hij hfresh).primaryEnds B := by
  obtain ⟨k, hkB, hka⟩ := (F.mem_primaryEnds B a).mp ha
  have hkj : k ≠ j := by intro h; exact hjB (h ▸ hkB)
  have hki : k ≠ i := by intro h; exact hai (hka.symm.trans (congrArg F.last h))
  apply (mem_primaryEnds _ B a).mpr
  refine ⟨⟨k, hkj⟩, ?_, ?_⟩
  · have he := F.merge_first i j hij hfresh (⟨k, hkj⟩ : (F.merge i j hij hfresh).Index)
    exact he.symm ▸ hkB
  · exact (F.merge_last i j hij hfresh (⟨k, hkj⟩ : (F.merge i j hij hfresh).Index)).trans
      (by simpa [hki] using hka)

end Inventories
end Family
end
end EndpointFactor.OrdinaryFragments
