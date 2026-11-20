import CorralFormalization.EndpointProof.Router.GlobalGeometry.Inventory

/-! # The installed global router can be set after every later closure -/
namespace EndpointRouter
open EndpointFactor Equiv Equiv.Perm
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G]
variable {n : ℕ} {input intermediate output : Fin n → G}
variable {first : LayerGeometry (firstMatchingLayer n) input intermediate}
variable {second : LayerGeometry (secondMatchingLayer n) intermediate output}

namespace TwoLayerSupport
variable (H : TwoLayerSupport first second)
include H

theorem route_inventory_cards (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) (i : Fin n) :
    (installedRoutes first second f s i).interior.toFinset.card = 9 ∧
      ((installedRoutes first second f s i).colors (fun a b : G => b-a)).toFinset.card = 10 := by
  rw [List.toFinset_card_of_nodup (H.route_interior_nodup f s hf i),
    List.toFinset_card_of_nodup (H.route_colors_nodup f s hf hs i)]
  exact ⟨compose_interior_length _ _ (first.path_valid f i).1
      (second.path_valid s (switchProduct f i)).1,
    compose_color_length _ _ _ (first.path_valid f i).1
      (second.path_valid s (switchProduct f i)).1⟩

theorem interior_finsets_pairwise (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) :
    Pairwise (fun i j => Disjoint
      (installedRoutes first second f s i).interior.toFinset
      (installedRoutes first second f s j).interior.toFinset) := by
  intro i j hij
  exact Finset.disjoint_left.mpr fun _z hz hz' =>
    List.disjoint_left.mp (H.route_interiors_pairwise f s hf hij)
      (List.mem_toFinset.mp hz) (List.mem_toFinset.mp hz')

theorem color_finsets_pairwise (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) :
    Pairwise (fun i j => Disjoint
      ((installedRoutes first second f s i).colors (fun a b : G => b-a)).toFinset
      ((installedRoutes first second f s j).colors (fun a b : G => b-a)).toFinset) := by
  intro i j hij
  exact Finset.disjoint_left.mpr fun _z hz hz' =>
    List.disjoint_left.mp (H.route_colors_pairwise f s hf hs hij)
      (List.mem_toFinset.mp hz) (List.mem_toFinset.mp hz')

/-- Fixed actual tables and raw numerical support certificates are chosen
before the universally quantified closing permutation.  All simplicity,
rainbow and cardinality clauses in the conclusion are proved here. -/
theorem route_after_every_closing_global :
    ∀ closing : Perm (Fin n),
      ∃ f s : List (Fin n × Fin n),
        f.Sublist (firstLayer n) ∧ s.Sublist (secondLayer n) ∧
        (closing * (switchProduct s * switchProduct f)).IsCycleOn Set.univ ∧
        (∀ i, (installedRoutes first second f s i).first = input i ∧
          (installedRoutes first second f s i).last =
            output ((switchProduct s * switchProduct f) i)) ∧
        (∀ i, (installedRoutes first second f s i).vertices.Nodup ∧
          ((installedRoutes first second f s i).colors (fun a b : G => b-a)).Nodup ∧
          ∀ c ∈ (installedRoutes first second f s i).colors (fun a b : G => b-a), c ≠ 0) ∧
        ((List.finRange n).flatMap (fun i =>
          (installedRoutes first second f s i).vertices)).Nodup ∧
        ((List.finRange n).flatMap (fun i =>
          (installedRoutes first second f s i).colors (fun a b : G => b-a))).Nodup ∧
        routeInteriorFinset first second f s = fixedInteriorFinset first second ∧
        routeColorFinset first second f s = fixedColorFinset first second ∧
        (routeInteriorFinset first second f s).card = 9*n ∧
        (routeColorFinset first second f s).card = 10*n := by
  intro closing
  obtain ⟨f,s,hf,hs,hcycle⟩ := adjacent_two_layers_router n closing
  exact ⟨f,s,hf,hs,hcycle,
    installedRoutes_endpoints first second f s hf hs,
    fun i => ⟨H.route_vertices_nodup f s hf hs i, H.route_colors_nodup f s hf hs i,
      H.route_colors_nonzero f s hf hs i⟩,
    H.total_vertices_nodup f s hf hs,
    H.total_colors_nodup f s hf hs,
    routeInteriorFinset_eq_fixed first second f s hf,
    routeColorFinset_eq_fixed first second f s hf hs,
    (H.inventory_cards f s hf hs).1,
    (H.inventory_cards f s hf hs).2⟩

/-- The two fixed inventories avoid the numerical forbidden set.  A point
label is forced nonzero exactly when zero is included in that forbidden set;
nonzero colours already follow without this extra premise. -/
theorem fixed_interiors_nonzero (F : Finset G)
    (hF : ∀ u, Disjoint (twoLayerUnitSupport first second u) F)
    (hmF : ∀ i, intermediate i ∉ F) (hzero : (0 : G) ∈ F) :
    0 ∉ fixedInteriorFinset first second := by
  intro hz
  exact Finset.disjoint_left.mp (H.fixed_interiors_avoid F hF hmF) hz hzero

end TwoLayerSupport
end
end EndpointRouter
