import CorralFormalization.EndpointProof.Router.Switch
import CorralFormalization.EndpointProof.Router.Permutation

/-!
# Actual length-ten routes and their exact budgets

The construction joins two actual length-five segments at an intermediate
port.  The intermediate port is counted once.  The endpoints are acted on
by the product of the two installed layer permutations in the same order
as `adjacent_two_layers_router`.
-/
namespace EndpointRouter

open EndpointFactor

universe u v
variable {V : Type u} {C : Type v}

/-- Join at a common port.  The equality of the two ports is an explicit
hypothesis of the label theorem, rather than silently adding an edge. -/
def compose (P Q : Segment V) : Segment V :=
  ⟨P.first, P.interior ++ [P.last] ++ Q.interior, Q.last⟩

@[simp] theorem compose_first (P Q : Segment V) : (compose P Q).first = P.first := rfl
@[simp] theorem compose_last (P Q : Segment V) : (compose P Q).last = Q.last := rfl

theorem compose_vertices (P Q : Segment V) (h : P.last = Q.first) :
    (compose P Q).vertices = P.body ++ Q.vertices := by
  simp [compose, Segment.vertices, Segment.body, ← h, List.append_assoc]

theorem compose_colors (edge : V → V → C) (P Q : Segment V)
    (h : P.last = Q.first) :
    (compose P Q).colors edge = P.colors edge ++ Q.colors edge := by
  rw [Segment.colors, compose_vertices P Q h]
  change edgeLabels edge (P.body ++ Q.first :: (Q.interior ++ [Q.last])) = _
  rw [← h, edgeLabels_append_pivot]
  simp [Segment.colors, Segment.vertices, Segment.body, h]

theorem compose_simple_rainbow (edge : V → V → C) (P Q : Segment V)
    (h : P.last = Q.first)
    (hP : P.body.Nodup) (hQ : Q.vertices.Nodup)
    (hv : List.Disjoint P.body Q.vertices)
    (hcP : (P.colors edge).Nodup) (hcQ : (Q.colors edge).Nodup)
    (hc : List.Disjoint (P.colors edge) (Q.colors edge)) :
    (compose P Q).vertices.Nodup ∧ ((compose P Q).colors edge).Nodup := by
  rw [compose_vertices P Q h, compose_colors edge P Q h]
  exact ⟨hP.append hQ hv, hcP.append hcQ hc⟩

/-- Four new vertices in each layer plus the common intermediate port. -/
theorem compose_interior_length (P Q : Segment V)
    (hP : P.interior.length = 4) (hQ : Q.interior.length = 4) :
    (compose P Q).interior.length = 9 := by
  simp [compose, hP, hQ]

theorem compose_color_length (edge : V → V → C) (P Q : Segment V)
    (hP : P.interior.length = 4) (hQ : Q.interior.length = 4) :
    ((compose P Q).colors edge).length = 10 := by
  rw [Segment.colors_length]
  simp [Segment.body, compose_interior_length P Q hP hQ]

/-- Actual routes after the two layer settings have been supplied. -/
def routes {n : ℕ} (P Q : Fin n → Segment V) (first : Equiv.Perm (Fin n))
    (i : Fin n) : Segment V := compose (P i) (Q (first i))

theorem route_endpoints {n : ℕ} (P Q : Fin n → Segment V)
    (x m z : Fin n → V) (first second : Equiv.Perm (Fin n))
    (hPf : ∀ i, (P i).first = x i) (hPl : ∀ i, (P i).last = m (first i))
    (hQf : ∀ i, (Q i).first = m i) (hQl : ∀ i, (Q i).last = z (second i)) :
    (∀ i, (routes P Q first i).first = x i) ∧
    (∀ i, (routes P Q first i).last = z ((second * first) i)) ∧
    (∀ i, (P i).last = (Q (first i)).first) := by
  exact ⟨hPf, fun i => hQl (first i), fun i => (hPl i).trans (hQf (first i)).symm⟩

private theorem flatMap_length_uniform {K : Type*} (l : List K) (f : K → List V)
    (t : ℕ) (h : ∀ i, (f i).length = t) :
    (l.flatMap f).length = t*l.length := by
  induction l with
  | nil => simp
  | cons i l ih => simp [h, ih, Nat.mul_succ, Nat.add_comm]

/-- Count the actual finite lists, before replacing multiplicities by
cardinalities using simplicity and disjointness. -/
theorem total_route_budgets {n : ℕ} (edge : V → V → C)
    (P Q : Fin n → Segment V) (first : Equiv.Perm (Fin n))
    (hP : ∀ i, (P i).interior.length = 4)
    (hQ : ∀ i, (Q i).interior.length = 4) :
    ((List.finRange n).flatMap (fun i => (routes P Q first i).interior)).length = 9*n ∧
    ((List.finRange n).flatMap (fun i => (routes P Q first i).colors edge)).length = 10*n := by
  constructor
  · simpa only [List.length_finRange] using
      flatMap_length_uniform (List.finRange n) (fun i => (routes P Q first i).interior) 9
        (fun i => compose_interior_length _ _ (hP i) (hQ (first i)))
  · simpa only [List.length_finRange] using
      flatMap_length_uniform (List.finRange n) (fun i => (routes P Q first i).colors edge) 10
        (fun i => compose_color_length edge _ _ (hP i) (hQ (first i)))

/-- Reindexing the second layer by the first setting loses no coordinates. -/
theorem reindex_flatMap {n : ℕ} (f : Fin n → List V) (σ : Equiv.Perm (Fin n)) :
    ((List.finRange n).flatMap (fun i => f (σ i))).Perm
      ((List.finRange n).flatMap f) := by
  simpa only [List.flatMap_map] using σ.map_finRange_perm.flatMap_right f

/-- The new-vertex inventory is independent of the first-layer permutation.
This statement keeps the intermediate ports and the interiors separate. -/
theorem route_interior_inventory {n : ℕ} (P Q : Fin n → Segment V)
    (first : Equiv.Perm (Fin n)) (z : V) :
    (∃ i, z ∈ (routes P Q first i).interior) ↔
      (∃ i, z ∈ (P i).interior) ∨ (∃ i, z = (P i).last) ∨
        (∃ i, z ∈ (Q i).interior) := by
  simp only [routes, compose, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨i, (h | h) | h⟩
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr (Or.inl ⟨i, h⟩)
    · exact Or.inr (Or.inr ⟨first i, h⟩)
  · rintro (⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩)
    · exact ⟨i, Or.inl (Or.inl h)⟩
    · exact ⟨i, Or.inl (Or.inr h)⟩
    · exact ⟨first.symm i, Or.inr (by simpa using h)⟩

theorem route_color_inventory {n : ℕ} (edge : V → V → C)
    (P Q : Fin n → Segment V) (first : Equiv.Perm (Fin n))
    (h : ∀ i, (P i).last = (Q (first i)).first) (c : C) :
    (∃ i, c ∈ (routes P Q first i).colors edge) ↔
      (∃ i, c ∈ (P i).colors edge) ∨ (∃ i, c ∈ (Q i).colors edge) := by
  simp only [routes, compose_colors edge _ _ (h _), List.mem_append]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨first i, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨first.symm i, Or.inr (by simpa using hi)⟩

/-- Cardinalities require the explicitly stated global nonrepetition
hypotheses; the length budget alone does not assert those hypotheses. -/
theorem total_route_inventory_cards [DecidableEq V] [DecidableEq C] {n : ℕ}
    (edge : V → V → C) (P Q : Fin n → Segment V) (first : Equiv.Perm (Fin n))
    (hP : ∀ i, (P i).interior.length = 4)
    (hQ : ∀ i, (Q i).interior.length = 4)
    (hv : ((List.finRange n).flatMap (fun i => (routes P Q first i).interior)).Nodup)
    (hc : ((List.finRange n).flatMap (fun i => (routes P Q first i).colors edge)).Nodup) :
    ((List.finRange n).flatMap (fun i => (routes P Q first i).interior)).toFinset.card = 9*n ∧
    ((List.finRange n).flatMap (fun i => (routes P Q first i).colors edge)).toFinset.card = 10*n := by
  rw [List.toFinset_card_of_nodup hv, List.toFinset_card_of_nodup hc]
  exact total_route_budgets edge P Q first hP hQ

/-- With the actual intermediate ports supplied, the route inventory is
exactly the first-layer interiors, all intermediate ports, and the
second-layer interiors.  It therefore depends only on their inventories. -/
theorem route_interior_inventory_of_ports {n : ℕ} (P Q : Fin n → Segment V)
    (m : Fin n → V) (first : Equiv.Perm (Fin n))
    (hP : ∀ i, (P i).last = m (first i)) (z : V) :
    (∃ i, z ∈ (routes P Q first i).interior) ↔
      (∃ i, z ∈ (P i).interior) ∨ (∃ i, z = m i) ∨
        (∃ i, z ∈ (Q i).interior) := by
  rw [route_interior_inventory]
  have hm : (∃ i, z = (P i).last) ↔ ∃ i, z = m i := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨first i, hi.trans (hP i)⟩
    · rintro ⟨i,hi⟩
      exact ⟨first.symm i, by simpa [hP] using hi⟩
  rw [hm]

end EndpointRouter
