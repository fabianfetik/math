import CorralFormalization.Basic

namespace CorralFormalization

theorem interleave_perm (xs : List ℕ) (f g : ℕ → ℕ) :
    List.Perm (xs.flatMap (fun x => [f x, g x])) (xs.map f ++ xs.map g) := by
  rw [← List.flatMap_pure_eq_map f xs, ← List.flatMap_pure_eq_map g xs]
  exact (List.flatMap_append_perm xs (fun x => [f x]) (fun x => [g x])).symm

theorem append_blocks_comm {α : Type} (xs ys zs : List α) :
    List.Perm (xs ++ ys ++ zs) (ys ++ xs ++ zs) := by
  have h : List.Perm (xs ++ ys) (ys ++ xs) := List.perm_append_comm
  simpa [List.append_assoc] using h.append_right zs

theorem perm_in_context {α : Type} {xs ys : List α}
    (h : List.Perm xs ys) (pre suf : List α) :
    List.Perm (pre ++ xs ++ suf) (pre ++ ys ++ suf) := by
  simpa [List.append_assoc] using (h.append_left pre).append_right suf

theorem swap_blocks_perm {α : Type} (pre xs ys suf : List α) :
    List.Perm (pre ++ xs ++ ys ++ suf) (pre ++ ys ++ xs ++ suf) := by
  simpa [List.append_assoc] using (append_blocks_comm xs ys suf).append_left pre

theorem length_flatMap_eq_sum_lengths {α β : Type} (xs : List α) (f : α → List β) :
    (xs.flatMap f).length = (xs.map fun x => (f x).length).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons,
        List.sum_cons, ih]

theorem sum_flatMap_eq_sum_sums {α : Type} (xs : List α) (f : α → List ℕ) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.sum_append, List.map_cons,
        List.sum_cons, ih]

theorem sum_map_const_on {α : Type} (xs : List α) (f : α → ℕ)
    (c : ℕ) (hc : ∀ x ∈ xs, f x = c) :
    (xs.map f).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : f x = c := hc x (by simp)
      have hxs : ∀ y ∈ xs, f y = c := by
        intro y hy
        exact hc y (by simp [hy])
      simp [hx, ih hxs, Nat.succ_mul, Nat.add_comm]

end CorralFormalization
