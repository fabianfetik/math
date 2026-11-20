import CorralFormalization.EndpointProof.Router.GlobalGeometry.Reservoir
import CorralFormalization.EndpointProof.Router.Installation.TwoLayerInstallation

/-! # From the paper event to globally valid, later-settable actual routes

The sample is fixed before the forbidden set and the external ports.  The
intermediate ports, actual local tables and common inventories are fixed before
the universally quantified closing permutation.  No global path validity or
rainbow premise is supplied by the caller.
-/
namespace EndpointRouter
open EndpointFactor EndpointLayeredSample Equiv Equiv.Perm
open scoped Classical
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [Fintype G]

/-- For a positive number of tracks, the original numerical ledger
`|F|+22n`, the proved reservoir event and disjoint ordered external ports suffice.

All settings have globally disjoint actual point lists and colour lists and the
same two finite inventories.  Every later closing admits a setting whose actual
endpoint permutation closes into one cycle. -/
theorem ReservoirEvent.install_global_router {n : ℕ} (u : ℝ) (ω : Bool × G → Bool)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (h : ReservoirEvent u (routerTrialBudget u (Fintype.card G)) ω)
    (htracks : 0 < n)
    (F : Finset G) (input output : Fin n → G)
    (hin : Function.Injective input) (hout : Function.Injective output)
    (hcross : ∀ i j, input i ≠ output j)
    (hledger : ((F.card + 22*n : ℕ) : ℝ) ≤ explicitRouterDensity u * (Fintype.card G : ℝ)/4) :
    ∃ middle : Fin n → G,
      ∃ first : LayerGeometry (firstMatchingLayer n) input middle,
        ∃ second : LayerGeometry (secondMatchingLayer n) middle output,
          TwoLayerSupport first second ∧
          TwoLayerGood (vertexReservoir ω) (colorReservoir ω) first second ∧
          (∀ i, middle i ∈ vertexReservoir ω ∧ middle i ∉ F) ∧
          (fixedInteriorFinset first second).card = 9*n ∧
          (fixedColorFinset first second).card = 10*n ∧
          (∀ z ∈ fixedInteriorFinset first second, z ∈ vertexReservoir ω) ∧
          (∀ c ∈ fixedColorFinset first second, c ∈ colorReservoir ω) ∧
          Disjoint (fixedInteriorFinset first second) F ∧
          Disjoint (fixedColorFinset first second) F ∧
          0 ∉ fixedColorFinset first second ∧
          (∀ f s : List (Fin n × Fin n),
            f.Sublist (firstLayer n) → s.Sublist (secondLayer n) →
              ((List.finRange n).flatMap (fun i =>
                (installedRoutes first second f s i).vertices)).Nodup ∧
              ((List.finRange n).flatMap (fun i =>
                (installedRoutes first second f s i).colors (fun a b : G => b-a))).Nodup ∧
              routeInteriorFinset first second f s = fixedInteriorFinset first second ∧
              routeColorFinset first second f s = fixedColorFinset first second ∧
              (routeInteriorFinset first second f s).card = 9*n ∧
              (routeColorFinset first second f s).card = 10*n ∧
              ∀ i, (installedRoutes first second f s i).vertices.Nodup ∧
                ((installedRoutes first second f s i).colors (fun a b : G => b-a)).Nodup ∧
                ∀ c ∈ (installedRoutes first second f s i).colors (fun a b : G => b-a), c ≠ 0) ∧
          (∀ closing : Perm (Fin n),
            ∃ f s : List (Fin n × Fin n),
              f.Sublist (firstLayer n) ∧ s.Sublist (secondLayer n) ∧
              (closing * (switchProduct s * switchProduct f)).IsCycleOn Set.univ ∧
              ∀ i, (installedRoutes first second f s i).first = input i ∧
                (installedRoutes first second f s i).last =
                  output ((switchProduct s * switchProduct f) i)) := by
  obtain ⟨middle,first,second,H,hgood,hmid,hF⟩ :=
    h.install_explicit_geometry_positive u ω hu hu1 htracks F input output hin hout hcross hledger
  refine ⟨middle,first,second,H,hgood,hmid,
    H.fixed_inventory_cards.1,H.fixed_inventory_cards.2,
    hgood.fixed_interiors_mem (fun i => (hmid i).1),hgood.fixed_colors_mem,
    H.fixed_interiors_avoid F hF (fun i => (hmid i).2),
    H.fixed_colors_avoid F hF,H.fixed_colors_nonzero,?_,?_⟩
  · intro f s hf hs
    exact ⟨H.total_vertices_nodup f s hf hs,H.total_colors_nodup f s hf hs,
      routeInteriorFinset_eq_fixed first second f s hf,
      routeColorFinset_eq_fixed first second f s hf hs,
      (H.inventory_cards f s hf hs).1,(H.inventory_cards f s hf hs).2,
      fun i => ⟨H.route_vertices_nodup f s hf hs i,H.route_colors_nodup f s hf hs i,
        H.route_colors_nonzero f s hf hs i⟩⟩
  · intro closing
    obtain ⟨f,s,hf,hs,hcycle⟩ := adjacent_two_layers_router n closing
    exact ⟨f,s,hf,hs,hcycle,installedRoutes_endpoints first second f s hf hs⟩

end
end EndpointRouter
