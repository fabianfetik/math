import CorralFormalization.EndpointProof.Router.LayerGeometry
import CorralFormalization.EndpointProof.Router.Composition

/-! # Later closing permutations with actual fixed local layer geometry

This assembles the local track paths and their endpoints/inventories.
Global disjointness of different installed primitives is deliberately not
assumed in `LayerGeometry`, so this module does not claim global simplicity
or rainbowness of the composed routes without that remaining supplier.
-/
namespace EndpointRouter

open EndpointFactor Equiv Equiv.Perm
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G]

namespace LayerGeometry
variable {n : ℕ} {L : MatchingLayer (Fin n)} {input output : Fin n → G}

def interiorInventory (D : LayerGeometry L input output) (z : G) : Prop :=
  (∃ e ∈ L.edges, z ∈ (D.exchange e).interior) ∨
    (∃ i, L.Isolated i ∧ z ∈ (D.idle i).interior)

def colorInventory (D : LayerGeometry L input output) (z : G) : Prop :=
  (∃ e ∈ L.edges, z ∈ (D.exchange e).colors) ∨
    (∃ i, L.Isolated i ∧ z ∈ (D.idle i).colors)

end LayerGeometry

variable {n : ℕ} {input intermediate output : Fin n → G}
variable (first : LayerGeometry (firstMatchingLayer n) input intermediate)
variable (second : LayerGeometry (secondMatchingLayer n) intermediate output)

def installedRoutes (firstOn secondOn : List (Fin n × Fin n)) : Fin n → Segment G :=
  routes (first.path firstOn) (second.path secondOn) (switchProduct firstOn)

def fixedInteriorInventory (z : G) : Prop :=
  first.interiorInventory z ∨ (∃ i, z = intermediate i) ∨ second.interiorInventory z

def fixedColorInventory (z : G) : Prop :=
  first.colorInventory z ∨ second.colorInventory z

theorem installedRoutes_join (firstOn secondOn : List (Fin n × Fin n))
    (hf : firstOn.Sublist (firstLayer n)) (hs : secondOn.Sublist (secondLayer n)) (i : Fin n) :
    (first.path firstOn i).last = (second.path secondOn (switchProduct firstOn i)).first := by
  exact ((first.endpoints firstOn hf i).2).trans
    ((second.endpoints secondOn hs (switchProduct firstOn i)).1).symm

theorem installedRoutes_endpoints (firstOn secondOn : List (Fin n × Fin n))
    (hf : firstOn.Sublist (firstLayer n)) (hs : secondOn.Sublist (secondLayer n)) (i : Fin n) :
    (installedRoutes first second firstOn secondOn i).first = input i ∧
    (installedRoutes first second firstOn secondOn i).last =
      output ((switchProduct secondOn * switchProduct firstOn) i) := by
  exact ⟨(first.endpoints firstOn hf i).1,
    (second.endpoints secondOn hs (switchProduct firstOn i)).2⟩

theorem installedRoutes_budgets (firstOn secondOn : List (Fin n × Fin n)) :
    ((List.finRange n).flatMap (fun i =>
      (installedRoutes first second firstOn secondOn i).interior)).length = 9*n ∧
    ((List.finRange n).flatMap (fun i =>
      (installedRoutes first second firstOn secondOn i).colors (fun a b : G => b-a))).length = 10*n := by
  exact total_route_budgets (fun a b : G => b-a) _ _ _
    (fun i => (first.path_valid firstOn i).1) (fun i => (second.path_valid secondOn i).1)

/-- The entire new-vertex inventory is fixed before the later closure. -/
theorem installedRoutes_interior_inventory (firstOn secondOn : List (Fin n × Fin n))
    (hf : firstOn.Sublist (firstLayer n)) (z : G) :
    (∃ i, z ∈ (installedRoutes first second firstOn secondOn i).interior) ↔
      fixedInteriorInventory first second z := by
  rw [installedRoutes,route_interior_inventory_of_ports _ _ intermediate _
    (fun i => (first.endpoints firstOn hf i).2)]
  rw [first.interior_inventory,second.interior_inventory]
  rfl

theorem installedRoutes_color_inventory (firstOn secondOn : List (Fin n × Fin n))
    (hf : firstOn.Sublist (firstLayer n)) (hs : secondOn.Sublist (secondLayer n)) (z : G) :
    (∃ i, z ∈ (installedRoutes first second firstOn secondOn i).colors (fun a b : G => b-a)) ↔
      fixedColorInventory first second z := by
  rw [installedRoutes,route_color_inventory (fun a b : G => b-a) _ _ _
    (installedRoutes_join first second firstOn secondOn hf hs)]
  rw [first.color_inventory,second.color_inventory]
  rfl

/-- A router represented by actual local tables is installed first.
For every later closing permutation, actual ten-edge routes are then
constructed with the correct one-cycle contracted endpoint permutation
and exactly the same inventories.  The missing global support-disjointness
assembly is not hidden in this statement as a path/rainbow premise. -/
theorem route_after_every_closing :
    ∀ closing : Perm (Fin n),
      ∃ firstOn secondOn : List (Fin n × Fin n),
        firstOn.Sublist (firstLayer n) ∧ secondOn.Sublist (secondLayer n) ∧
        (closing * (switchProduct secondOn * switchProduct firstOn)).IsCycleOn Set.univ ∧
        (∀ i, (installedRoutes first second firstOn secondOn i).first = input i ∧
          (installedRoutes first second firstOn secondOn i).last =
            output ((switchProduct secondOn * switchProduct firstOn) i)) ∧
        (∀ z, (∃ i, z ∈ (installedRoutes first second firstOn secondOn i).interior) ↔
          fixedInteriorInventory first second z) ∧
        (∀ z, (∃ i, z ∈ (installedRoutes first second firstOn secondOn i).colors
          (fun a b : G => b-a)) ↔ fixedColorInventory first second z) ∧
        ((List.finRange n).flatMap (fun i =>
          (installedRoutes first second firstOn secondOn i).interior)).length = 9*n ∧
        ((List.finRange n).flatMap (fun i =>
          (installedRoutes first second firstOn secondOn i).colors (fun a b : G => b-a))).length = 10*n := by
  intro closing
  obtain ⟨firstOn,secondOn,hf,hs,hcycle⟩ := adjacent_two_layers_router n closing
  exact ⟨firstOn,secondOn,hf,hs,hcycle,
    installedRoutes_endpoints first second firstOn secondOn hf hs,
    installedRoutes_interior_inventory first second firstOn secondOn hf,
    installedRoutes_color_inventory first second firstOn secondOn hf hs,
    (installedRoutes_budgets first second firstOn secondOn).1,
    (installedRoutes_budgets first second firstOn secondOn).2⟩

end
end EndpointRouter
