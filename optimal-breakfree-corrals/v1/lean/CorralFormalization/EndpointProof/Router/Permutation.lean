import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Common

/-!
# A fixed two-layer router joins every later cycle factor

The main theorem quantifies over the closing permutation *after* the
layers are fixed.  It selects a sublist of the switches in each layer;
it does not claim that two layers realize arbitrary prescribed pairings.
-/
namespace EndpointRouter

open Equiv Equiv.Perm

universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A transposition between distinct old cycles joins its two endpoints.
This proof also covers singleton cycles. -/
theorem mul_swap_sameCycle (f : Perm α) (a b : α)
    (hab : ¬ f.SameCycle a b) : (f * swap a b).SameCycle a b := by
  let g := f * swap a b
  by_contra hnew
  have hpow : ∀ n : ℕ, g.SameCycle a ((f ^ (n+1)) b) := by
    intro n
    induction n with
    | zero =>
      have h := (SameCycle.refl g a).apply_right
      simpa [g, mul_apply] using h
    | succ n ih =>
      have hne_a : (f ^ (n+1)) b ≠ a := by
        intro he
        apply hab
        have hh : f.SameCycle b ((f ^ (n+1)) b) := (SameCycle.refl f b).pow_right
        rw [he] at hh
        exact hh.symm
      have hne_b : (f ^ (n+1)) b ≠ b := by
        intro he
        apply hnew
        simpa [he] using ih
      have hh := ih.apply_right
      have hg : g ((f ^ (n+1)) b) = f ((f ^ (n+1)) b) := by
        dsimp [g]
        rw [swap_apply_of_ne_of_ne hne_a hne_b]
      rw [hg] at hh
      simpa [pow_succ', mul_apply, Nat.add_assoc] using hh
  have hp : 0 < orderOf f := orderOf_pos f
  have hh := hpow (orderOf f - 1)
  have he : orderOf f - 1 + 1 = orderOf f := by omega
  rw [he, pow_orderOf_eq_one, one_apply] at hh
  exact hnew hh

/-- Multiplication by a cycle-merging transposition never splits any old
cycle.  This is the invariant that makes skipped switches remain valid. -/
theorem sameCycle_mono_mul_swap (f : Perm α) (a b : α)
    (hab : ¬ f.SameCycle a b) :
    ∀ x y, f.SameCycle x y → (f * swap a b).SameCycle x y := by
  let g := f * swap a b
  have hab' : g.SameCycle a b := mul_swap_sameCycle f a b hab
  have hstep : ∀ x, g.SameCycle x (f x) := by
    intro x
    by_cases hxa : x = a
    · subst x
      have hh := hab'.trans (SameCycle.refl g b).apply_right
      simpa [g, mul_apply] using hh
    by_cases hxb : x = b
    · subst x
      have hh := hab'.symm.trans (SameCycle.refl g a).apply_right
      simpa [g, mul_apply] using hh
    · have hh := (SameCycle.refl g x).apply_right
      simpa [g, mul_apply, swap_apply_of_ne_of_ne hxa hxb] using hh
  intro x y hxy
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact SameCycle.refl g x
  | succ n ih =>
    have hh := ih.trans (hstep ((f ^ n) x))
    simpa [pow_succ', mul_apply] using hh

/-- The permutation implemented by the selected local exchanges. -/
def switchProduct (edges : List (α × α)) : Perm α :=
  (edges.map (fun e => swap e.1 e.2)).prod

omit [Fintype α] in
@[simp] theorem switchProduct_nil : switchProduct ([] : List (α × α)) = 1 := rfl

omit [Fintype α] in
@[simp] theorem switchProduct_cons (e : α × α) (es : List (α × α)) :
    switchProduct (e::es) = swap e.1 e.2 * switchProduct es := rfl

omit [Fintype α] in
theorem switchProduct_append (es fs : List (α × α)) :
    switchProduct (es++fs) = switchProduct es * switchProduct fs := by
  simp [switchProduct]

/-- A single pass through any fixed edge list selects only merging
transpositions.  Every processed edge is internal to a final cycle and
all initial same-cycle relations survive. -/
theorem select_merging_switches (edges : List (α × α)) (f : Perm α) :
    ∃ chosen : List (α × α), chosen.Sublist edges ∧
      (∀ x y, f.SameCycle x y → (f * switchProduct chosen).SameCycle x y) ∧
      (∀ e ∈ edges, (f * switchProduct chosen).SameCycle e.1 e.2) := by
  induction edges generalizing f with
  | nil =>
    refine ⟨[], List.Sublist.refl _, ?_, ?_⟩ <;> simp
  | cons e es ih =>
    by_cases he : f.SameCycle e.1 e.2
    · obtain ⟨chosen, hsub, hmono, hdone⟩ := ih f
      refine ⟨chosen, hsub.cons _, hmono, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hmono _ _ he
      · exact hdone _ hd
    · obtain ⟨chosen, hsub, hmono, hdone⟩ := ih (f * swap e.1 e.2)
      refine ⟨e::chosen, hsub.cons_cons _, ?_, ?_⟩
      · intro x y hxy
        simpa [mul_assoc] using hmono x y (sameCycle_mono_mul_swap f e.1 e.2 he x y hxy)
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · simpa [mul_assoc] using hmono _ _ (mul_swap_sameCycle f d.1 d.2 he)
        · simpa [mul_assoc] using hdone _ hd

/-- First and second layer are installed before `closing` is supplied.
Only the connectedness property of their union is needed in this
permutation theorem; physical realizability is a separate obligation. -/
theorem two_layers_router
    (first second : List (α × α))
    (hconnected : ∀ f : Perm α,
      (∀ e ∈ first ++ second, f.SameCycle e.1 e.2) →
      ∀ x y, f.SameCycle x y) :
    ∀ closing : Perm α,
      ∃ firstOn secondOn : List (α × α),
        firstOn.Sublist first ∧ secondOn.Sublist second ∧
        (closing * (switchProduct secondOn * switchProduct firstOn)).IsCycleOn Set.univ := by
  intro closing
  obtain ⟨secondOn, hs, hm, hd⟩ := select_merging_switches second closing
  obtain ⟨firstOn, hf, hm', hd'⟩ :=
    select_merging_switches first (closing * switchProduct secondOn)
  let final := closing * switchProduct secondOn * switchProduct firstOn
  have hedge : ∀ e ∈ first ++ second, final.SameCycle e.1 e.2 := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hd' e he
    · exact hm' _ _ (hd e he)
  refine ⟨firstOn, secondOn, hf, hs, ?_⟩
  rw [← mul_assoc]
  exact ⟨final.bijOn (fun _ => Iff.rfl), fun _ _ _ _ => hconnected final hedge _ _⟩

/-- The adjacent edge indexed by its smaller, zero-based track label. -/
def adjacentEdge (n : ℕ) (i : Fin (n-1)) : Fin n × Fin n :=
  (⟨i.val, by omega⟩, ⟨i.val+1, by omega⟩)

def firstLayer (n : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange (n-1)).filter (fun i => i.val % 2 == 0)).map (adjacentEdge n)

def secondLayer (n : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange (n-1)).filter (fun i => i.val % 2 != 0)).map (adjacentEdge n)

theorem adjacent_mem_layers (n : ℕ) (i : Fin (n-1)) :
    adjacentEdge n i ∈ firstLayer n ++ secondLayer n := by
  by_cases hi : i.val % 2 = 0
  · apply List.mem_append_left
    simp only [firstLayer, List.mem_map]
    exact ⟨i, by simp [hi], rfl⟩
  · apply List.mem_append_right
    simp only [secondLayer, List.mem_map]
    exact ⟨i, by simp; omega, rfl⟩


/-- Different switches within either layer have four different endpoints. -/
theorem adjacent_same_parity_disjoint (n : ℕ) (i j : Fin (n-1))
    (hij : i ≠ j) (hp : i.val % 2 = j.val % 2) :
    [(adjacentEdge n i).1, (adjacentEdge n i).2,
      (adjacentEdge n j).1, (adjacentEdge n j).2].Nodup := by
  have hval : i.val ≠ j.val := fun he => hij (Fin.ext he)
  simp only [List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true, not_or, adjacentEdge,
    Fin.mk.injEq]
  omega

theorem firstLayer_disjoint (n : ℕ) (e : Fin n × Fin n) (he : e ∈ firstLayer n)
    (d : Fin n × Fin n) (hd : d ∈ firstLayer n)
    (hne : e ≠ d) : [e.1, e.2, d.1, d.2].Nodup := by
  simp only [firstLayer, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, beq_iff_eq] at he hd
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hd
  exact adjacent_same_parity_disjoint n i j (fun h => hne (h ▸ rfl)) (hi.trans hj.symm)

theorem secondLayer_disjoint (n : ℕ) (e : Fin n × Fin n) (he : e ∈ secondLayer n)
    (d : Fin n × Fin n) (hd : d ∈ secondLayer n)
    (hne : e ≠ d) : [e.1, e.2, d.1, d.2].Nodup := by
  simp only [secondLayer, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, bne_iff_ne, ne_eq] at he hd
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hd
  apply adjacent_same_parity_disjoint n i j (fun h => hne (h ▸ rfl))
  omega

/-- Thus switch choices really are independent within a layer. -/
theorem firstLayer_swaps_commute (n : ℕ) (e : Fin n × Fin n) (he : e ∈ firstLayer n)
    (d : Fin n × Fin n) (hd : d ∈ firstLayer n) :
    Commute (swap e.1 e.2) (swap d.1 d.2) := by
  by_cases h : e = d
  · subst d; exact Commute.refl _
  · exact (disjoint_swap_swap (firstLayer_disjoint n e he d hd h)).commute

theorem secondLayer_swaps_commute (n : ℕ) (e : Fin n × Fin n) (he : e ∈ secondLayer n)
    (d : Fin n × Fin n) (hd : d ∈ secondLayer n) :
    Commute (swap e.1 e.2) (swap d.1 d.2) := by
  by_cases h : e = d
  · subst d; exact Commute.refl _
  · exact (disjoint_swap_swap (secondLayer_disjoint n e he d hd h)).commute

/-- Connectivity is proved on the actual path of labels, including n=1. -/
theorem adjacent_layers_connected (n : ℕ) (f : Perm (Fin n))
    (h : ∀ e ∈ firstLayer n ++ secondLayer n, f.SameCycle e.1 e.2) :
    ∀ x y, f.SameCycle x y := by
  have hto : ∀ k : ℕ, ∀ hk : k < n, f.SameCycle ⟨0, by omega⟩ ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact SameCycle.refl _ _
    | succ k ih =>
      intro hk
      have he := h (adjacentEdge n ⟨k, by omega⟩)
        (adjacent_mem_layers n ⟨k, by omega⟩)
      exact (ih (by omega)).trans he
  intro x y
  exact (hto x.val x.isLt).symm.trans (hto y.val y.isLt)

/-- The exact two alternating layers in the two-layer router construction.  They are fixed
once for all, and then every closing permutation admits a one-cycle
setting.  There is no prescribed-pairing assertion. -/
theorem adjacent_two_layers_router (n : ℕ) :
    ∀ closing : Perm (Fin n),
      ∃ firstOn secondOn : List (Fin n × Fin n),
        firstOn.Sublist (firstLayer n) ∧ secondOn.Sublist (secondLayer n) ∧
        (closing * (switchProduct secondOn * switchProduct firstOn)).IsCycleOn Set.univ :=
  two_layers_router (firstLayer n) (secondLayer n) (adjacent_layers_connected n)

end EndpointRouter
