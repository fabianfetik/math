import CorralFormalization.DiversityCompletion.CyclicEndpointInvariants
import Mathlib.Tactic

/-! The directed mod-three flow obstruction, for the existing endpoint-path model.
No path-flow conclusion is assumed: the edge inequality is checked on all nine
directed residue pairs and telescoped along the actual path. -/

namespace CorralFormalization.Results.DensityObstruction

open scoped BigOperators
open CorralFormalization.LatinCompletion.TerraceCompletion

def colorWeight (r : ZMod 3) : ℤ := if r = 1 then 1 else if r = 2 then -1 else 0

def vertexWeight (r : ZMod 3) : ℤ := if r = 2 then 1 else 0

def walkWeight : List (ZMod 3) → ℤ
  | [] => 0
  | [_] => 0
  | s :: t :: xs => colorWeight (t-s) + walkWeight (t::xs)

/-- The number of actual directed `s → t` transitions of the list. The
integer codomain avoids truncated subtraction in the flow identity. -/
def transitionCount (s t : ZMod 3) : List (ZMod 3) → ℤ
  | [] => 0
  | [_] => 0
  | u :: v :: xs => (if u = s ∧ v = t then 1 else 0) + transitionCount s t (v::xs)

theorem directed_edge_identity (s t : ZMod 3) :
    colorWeight (t-s) = (t.val : ℤ) - s.val +
      3 * ((if s = 2 ∧ t = 0 then 1 else 0) -
        (if s = 0 ∧ t = 2 then 1 else 0)) := by
  fin_cases s <;> fin_cases t <;> decide

/-- Exactly the printed difference `3(U₂−V₀)+1` when the endpoint classes
are one and two. Both transition counts are calculated on the actual list. -/
theorem walkWeight_flow_identity (s t : ZMod 3) (xs : List (ZMod 3)) :
    walkWeight ((s::xs) ++ [t]) = (t.val : ℤ) - s.val +
      3 * (transitionCount 2 0 ((s::xs) ++ [t]) -
        transitionCount 0 2 ((s::xs) ++ [t])) := by
  induction xs generalizing s with
  | nil => simpa [walkWeight, transitionCount] using directed_edge_identity s t
  | cons z xs ih =>
      have hstep := directed_edge_identity s z
      have htail := ih z
      simp only [List.cons_append, walkWeight, transitionCount] at htail ⊢
      linarith

theorem transitionCount_nonneg (s t : ZMod 3) (xs : List (ZMod 3)) :
    0 ≤ transitionCount s t xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          simp only [transitionCount]
          split_ifs <;> linarith

theorem two_zero_indicator_bound (s t : ZMod 3) :
    (if s = 2 ∧ t = 0 then (1:ℤ) else 0) ≤ vertexWeight s := by
  by_cases hs : s = 2 <;> by_cases ht : t = 0 <;> simp [hs, ht, vertexWeight]

/-- `U₂ ≤ a−1`: class-two vertices can be used as tails at most once each,
and the terminal vertex contributes no outgoing edge. -/
theorem transitionCount_two_zero_bound (s t : ZMod 3) (xs : List (ZMod 3)) :
    transitionCount 2 0 ((s::xs) ++ [t]) ≤
      (((((s::xs) ++ [t]).map vertexWeight).sum) - vertexWeight t) := by
  induction xs generalizing s with
  | nil => simpa [transitionCount] using two_zero_indicator_bound s t
  | cons z xs ih =>
      have hstep := two_zero_indicator_bound s z
      have htail := ih z
      simp only [List.cons_append, List.map_cons, List.sum_cons, transitionCount] at htail ⊢
      linarith

theorem directed_edge_bound (s t : ZMod 3) :
    colorWeight (t-s) ≤ (t.val : ℤ) - s.val + 3 * vertexWeight s := by
  fin_cases s <;> fin_cases t <;> decide

theorem walkWeight_bound (s t : ZMod 3) (xs : List (ZMod 3)) :
    walkWeight ((s::xs) ++ [t]) ≤ (t.val : ℤ) - s.val +
      3 * (((((s::xs) ++ [t]).map vertexWeight).sum) - vertexWeight t) := by
  have hi := walkWeight_flow_identity s t xs
  have hU := transitionCount_two_zero_bound s t xs
  have hV := transitionCount_nonneg 0 2 ((s::xs) ++ [t])
  linarith

theorem walkWeight_map_pathGaps {n : ℕ} [NeZero n]
    (ρ : ZMod n →+ ZMod 3) (xs : List (ZMod n)) :
    walkWeight (xs.map ρ) =
      ((pathGaps xs).map fun d : ℕ => colorWeight (ρ (d : ZMod n))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          simp only [List.map_cons] at ih
          simp only [List.map_cons, walkWeight, pathGaps, List.sum_cons]
          rw [ih, ZMod.natCast_zmod_val, map_sub]

theorem list_sum_eq_finset_sum {α : Type*} [DecidableEq α]
    (xs : List α) (hxs : xs.Nodup) (f : α → ℤ) :
    (xs.map f).sum = ∑ z ∈ xs.toFinset, f z := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hn := List.nodup_cons.mp hxs
      simp [List.toFinset_cons, Finset.sum_insert, hn.1, ih hn.2]

theorem sum_vertexWeight {α : Type*} [DecidableEq α]
    (W : Finset α) (ρ : α → ZMod 3) :
    (∑ z ∈ W, vertexWeight (ρ z)) = ((W.filter fun z => ρ z = 2).card : ℤ) := by
  simp only [vertexWeight]
  rw [← Finset.sum_filter]
  simp

theorem sum_colorWeight {α : Type*} [DecidableEq α]
    (D : Finset α) (ρ : α → ZMod 3) :
    (∑ z ∈ D, colorWeight (ρ z)) =
      ((D.filter fun z => ρ z = 1).card : ℤ) - (D.filter fun z => ρ z = 2).card := by
  have hpoint (z : α) : colorWeight (ρ z) =
      (if ρ z = 1 then (1:ℤ) else 0) - (if ρ z = 2 then (1:ℤ) else 0) := by
    by_cases h1 : ρ z = 1
    · simp [colorWeight, h1, show (1 : ZMod 3) ≠ 2 by decide]
    · by_cases h2 : ρ z = 2 <;> simp [colorWeight, h1, h2, show (2 : ZMod 3) ≠ 1 by decide]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  simp

theorem endpointPath_color_sum {n : ℕ} [NeZero n]
    (_W D : Finset (ZMod n)) (x y : ZMod n)
    (middle : List (ZMod n))
    (hrain : (pathGaps ((x::middle) ++ [y])).Nodup)
    (hcolors : ∀ d : ℕ, d ∈ pathGaps ((x::middle) ++ [y]) ↔
      0 < d ∧ d < n ∧ (d : ZMod n) ∈ D)
    (hzero : 0 ∉ D) (f : ZMod n → ℤ) :
    ((pathGaps ((x::middle) ++ [y])).map fun d : ℕ => f (d : ZMod n)).sum =
      ∑ d ∈ D, f d := by
  let C := (pathGaps ((x::middle) ++ [y])).toFinset
  have himage : C.image (fun d : ℕ => (d : ZMod n)) = D := by
    ext d
    constructor
    · intro hd
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      exact ((hcolors e).mp (List.mem_toFinset.mp he)).2.2
    · intro hd
      refine Finset.mem_image.mpr ⟨d.val, ?_, ZMod.natCast_zmod_val d⟩
      apply List.mem_toFinset.mpr
      apply (hcolors d.val).mpr
      refine ⟨?_, d.val_lt, ?_⟩
      · have hd0 : d ≠ 0 := by intro h; exact hzero (h ▸ hd)
        have hv0 : d.val ≠ 0 := by simpa using hd0
        omega
      · simpa using hd
  have hinj : Set.InjOn (fun d : ℕ => (d : ZMod n)) C := by
    intro d hd e he hde
    have hdlt := ((hcolors d).mp (List.mem_toFinset.mp hd)).2.1
    have helt := ((hcolors e).mp (List.mem_toFinset.mp he)).2.1
    have hv := congrArg ZMod.val hde
    simpa [ZMod.val_natCast_of_lt hdlt, ZMod.val_natCast_of_lt helt] using hv
  rw [list_sum_eq_finset_sum _ hrain]
  rw [← himage, Finset.sum_image hinj]

/-- The actual directed-flow inequality: a path from class one to class two
has at most `3a-2` more class-one than class-two edge differences, where `a`
is the number of its class-two vertices. -/
theorem endpointPath_flow_bound {n : ℕ} [NeZero n]
    (W D : Finset (ZMod n)) (x y : ZMod n) (ρ : ZMod n →+ ZMod 3)
    (hx : ρ x = 1) (hy : ρ y = 2) (hz : 0 ∉ D)
    (hp : EndpointPathClaim W D x y) :
    ((D.filter fun d => ρ d = 1).card : ℤ) - (D.filter fun d => ρ d = 2).card ≤
      3 * (W.filter fun z => ρ z = 2).card - 2 := by
  obtain ⟨middle, hsimple, hvertices, hrain, hcolors⟩ := hp
  have hW : ((x::middle) ++ [y]).toFinset = W := by
    ext z
    simp only [List.mem_toFinset]
    exact hvertices z
  have hb := walkWeight_bound (ρ x) (ρ y) (middle.map ρ)
  have hmap : ((x::middle) ++ [y]).map ρ = ((ρ x::middle.map ρ) ++ [ρ y]) := by
    simp
  rw [← hmap, walkWeight_map_pathGaps] at hb
  rw [endpointPath_color_sum W D x y middle hrain hcolors hz (fun d => colorWeight (ρ d))] at hb
  rw [List.map_map, list_sum_eq_finset_sum _ hsimple, hW] at hb
  simp only [Function.comp_apply] at hb
  rw [sum_vertexWeight, sum_colorWeight] at hb
  simp only [hx, hy] at hb
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  have hv2 : (2 : ZMod 3).val = 2 := rfl
  rw [hv1, hv2] at hb
  norm_num [vertexWeight] at hb
  linarith

end CorralFormalization.Results.DensityObstruction
