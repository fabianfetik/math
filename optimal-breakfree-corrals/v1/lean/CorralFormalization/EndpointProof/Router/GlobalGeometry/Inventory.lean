import CorralFormalization.EndpointProof.Router.GlobalGeometry.Routes

namespace EndpointRouter
open EndpointFactor Equiv Equiv.Perm
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G]
variable {n : ℕ} {input intermediate output : Fin n → G}
variable (first : LayerGeometry (firstMatchingLayer n) input intermediate)
variable (second : LayerGeometry (secondMatchingLayer n) intermediate output)

def routeInteriorFinset (f s : List (Fin n × Fin n)) : Finset G :=
  ((List.finRange n).flatMap (fun i => (installedRoutes first second f s i).interior)).toFinset

def routeColorFinset (f s : List (Fin n × Fin n)) : Finset G :=
  ((List.finRange n).flatMap (fun i =>
    (installedRoutes first second f s i).colors (fun a b : G => b-a))).toFinset

@[simp] theorem mem_routeInteriorFinset (f s : List (Fin n × Fin n)) (z : G) :
    z ∈ routeInteriorFinset first second f s ↔
      ∃ i, z ∈ (installedRoutes first second f s i).interior := by
  simp [routeInteriorFinset]

@[simp] theorem mem_routeColorFinset (f s : List (Fin n × Fin n)) (z : G) :
    z ∈ routeColorFinset first second f s ↔
      ∃ i, z ∈ (installedRoutes first second f s i).colors (fun a b : G => b-a) := by
  simp [routeColorFinset]

/-- Concrete fixed finite sets, defined before a later closing permutation. -/
def fixedInteriorFinset : Finset G := routeInteriorFinset first second [] []
def fixedColorFinset : Finset G := routeColorFinset first second [] []

theorem routeInteriorFinset_eq_fixed (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) :
    routeInteriorFinset first second f s = fixedInteriorFinset first second := by
  apply Finset.ext
  intro z
  rw [mem_routeInteriorFinset, installedRoutes_interior_inventory first second f s hf,
    fixedInteriorFinset, mem_routeInteriorFinset,
    installedRoutes_interior_inventory first second [] [] (List.nil_sublist _)]

theorem routeColorFinset_eq_fixed (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) :
    routeColorFinset first second f s = fixedColorFinset first second := by
  apply Finset.ext
  intro z
  rw [mem_routeColorFinset, installedRoutes_color_inventory first second f s hf hs,
    fixedColorFinset, mem_routeColorFinset,
    installedRoutes_color_inventory first second [] [] (List.nil_sublist _) (List.nil_sublist _)]

namespace TwoLayerSupport
variable {first second} (H : TwoLayerSupport first second)
include H

theorem total_vertices_nodup (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) :
    ((List.finRange n).flatMap (fun i =>
      (installedRoutes first second f s i).vertices)).Nodup := by
  apply List.nodup_flatMap.mpr
  exact ⟨fun i _ => H.route_vertices_nodup f s hf hs i,
    (List.nodup_finRange n).imp (fun hij => H.route_vertices_pairwise f s hf hs hij)⟩

theorem total_interiors_nodup (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) :
    ((List.finRange n).flatMap (fun i =>
      (installedRoutes first second f s i).interior)).Nodup := by
  apply List.nodup_flatMap.mpr
  exact ⟨fun i _ => H.route_interior_nodup f s hf i,
    (List.nodup_finRange n).imp (fun hij => H.route_interiors_pairwise f s hf hij)⟩

theorem total_colors_nodup (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) :
    ((List.finRange n).flatMap (fun i =>
      (installedRoutes first second f s i).colors (fun a b : G => b-a))).Nodup := by
  apply List.nodup_flatMap.mpr
  exact ⟨fun i _ => H.route_colors_nodup f s hf hs i,
    (List.nodup_finRange n).imp (fun hij => H.route_colors_pairwise f s hf hs hij)⟩

/-- The paper's budgets are actual cardinalities, with all multiplicities removed. -/
theorem inventory_cards (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) (hs : s.Sublist (secondLayer n)) :
    (routeInteriorFinset first second f s).card = 9*n ∧
      (routeColorFinset first second f s).card = 10*n := by
  exact total_route_inventory_cards (fun a b : G => b-a) _ _ _
    (fun i => (first.path_valid f i).1) (fun i => (second.path_valid s i).1)
    (H.total_interiors_nodup f s hf) (H.total_colors_nodup f s hf hs)

theorem fixed_inventory_cards :
    (fixedInteriorFinset first second).card = 9*n ∧
      (fixedColorFinset first second).card = 10*n :=
  H.inventory_cards [] [] (List.nil_sublist _) (List.nil_sublist _)

theorem fixed_colors_nonzero : 0 ∉ fixedColorFinset first second := by
  rw [fixedColorFinset, mem_routeColorFinset]
  rintro ⟨i, hi⟩
  exact H.route_colors_nonzero [] [] (List.nil_sublist _) (List.nil_sublist _) i 0 hi rfl

theorem route_interiors_avoid (F : Finset G)
    (hF : ∀ u, Disjoint (twoLayerUnitSupport first second u) F)
    (hmF : ∀ i, intermediate i ∉ F)
    (f s : List (Fin n × Fin n)) (hf : f.Sublist (firstLayer n)) :
    ∀ i z, z ∈ (installedRoutes first second f s i).interior → z ∉ F := by
  intro i z hz hzF
  rw [installedRoutes_interior_eq first second f s hf i] at hz
  simp only [List.mem_append, List.mem_singleton] at hz
  rcases hz with (hz | hz) | hz
  · exact Finset.disjoint_left.mp (hF (.inl ((firstMatchingLayer n).unitOf i)))
      (first.path_interior_support f i hz) hzF
  · subst z
    exact hmF _ hzF
  · exact Finset.disjoint_left.mp (hF (.inr ((secondMatchingLayer n).unitOf (switchProduct f i))))
      (second.path_interior_support s _ hz) hzF

theorem route_colors_avoid (F : Finset G)
    (hF : ∀ u, Disjoint (twoLayerUnitSupport first second u) F)
    (f s : List (Fin n × Fin n)) (hf : f.Sublist (firstLayer n))
    (hs : s.Sublist (secondLayer n)) :
    ∀ i c, c ∈ (installedRoutes first second f s i).colors (fun a b : G => b-a) → c ∉ F := by
  intro i c hc hcF
  rw [installedRoutes_colors_eq first second f s hf hs i] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact Finset.disjoint_left.mp (hF (.inl ((firstMatchingLayer n).unitOf i)))
      (first.path_color_support f i hc) hcF
  · exact Finset.disjoint_left.mp (hF (.inr ((secondMatchingLayer n).unitOf (switchProduct f i))))
      (second.path_color_support s _ hc) hcF

theorem fixed_interiors_avoid (F : Finset G)
    (hF : ∀ u, Disjoint (twoLayerUnitSupport first second u) F)
    (hmF : ∀ i, intermediate i ∉ F) :
    Disjoint (fixedInteriorFinset first second) F := by
  apply Finset.disjoint_left.mpr
  intro z hz hzF
  obtain ⟨i, hi⟩ := (mem_routeInteriorFinset first second [] [] z).mp hz
  exact H.route_interiors_avoid F hF hmF [] [] (List.nil_sublist _) i z hi hzF

theorem fixed_colors_avoid (F : Finset G)
    (hF : ∀ u, Disjoint (twoLayerUnitSupport first second u) F) :
    Disjoint (fixedColorFinset first second) F := by
  apply Finset.disjoint_left.mpr
  intro z hz hzF
  obtain ⟨i, hi⟩ := (mem_routeColorFinset first second [] [] z).mp hz
  exact H.route_colors_avoid F hF [] [] (List.nil_sublist _) (List.nil_sublist _) i z hi hzF

end TwoLayerSupport
end
end EndpointRouter
