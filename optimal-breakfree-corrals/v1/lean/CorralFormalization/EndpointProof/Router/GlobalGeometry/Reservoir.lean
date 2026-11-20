import CorralFormalization.EndpointProof.Router.GlobalGeometry.Closing
import CorralFormalization.EndpointProof.Router.Installation.Installed

/-! # Actual route coordinates stay in the installer's reservoirs

The transfer is through the exact primitive in each used table slot.  Numerical
support membership alone is insufficient here, since it forgets the channel.
-/
namespace EndpointRouter
open EndpointFactor Equiv Equiv.Perm
open scoped Classical
noncomputable section
universe u v
variable {G : Type v} [AddCommGroup G]

namespace Switch
theorem path_interior_mem (S : Switch G) (cross track : Bool) {z : G}
    (hz : z ∈ (S.path cross track).interior) : z ∈ S.interior := by
  apply (S.interior_inventory cross z).mp
  cases track
  · exact Or.inl hz
  · exact Or.inr hz

theorem path_color_mem (S : Switch G) (cross track : Bool) {z : G}
    (hz : z ∈ (S.path cross track).colors (fun a b : G => b-a)) : z ∈ S.colors := by
  apply (S.color_inventory cross z).mp
  cases track
  · exact Or.inl hz
  · exact Or.inr hz
end Switch

namespace LayerGeometry
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {L : MatchingLayer α} {input output : α → G}
variable (D : LayerGeometry L input output)

theorem path_interior_unitPrimitive (chosen : List (α × α)) (i : α) {z : G}
    (hz : z ∈ (D.path chosen i).interior) :
    z ∈ (D.unitPrimitive (L.unitOf i)).interior := by
  by_cases hi : L.Isolated i
  · rw [MatchingLayer.unitOf, dif_pos hi, unitPrimitive, Primitive.interior]
    simpa only [D.path_isolated chosen i hi, Idle.path, Idle.interior] using hz
  · rw [MatchingLayer.unitOf, dif_neg hi, unitPrimitive, Primitive.interior]
    simp only [path, dif_neg hi] at hz
    exact Switch.path_interior_mem _ _ _ hz

theorem path_color_unitPrimitive (chosen : List (α × α)) (i : α) {z : G}
    (hz : z ∈ (D.path chosen i).colors (fun a b : G => b-a)) :
    z ∈ (D.unitPrimitive (L.unitOf i)).colors := by
  by_cases hi : L.Isolated i
  · rw [MatchingLayer.unitOf, dif_pos hi, unitPrimitive, Primitive.colors]
    simpa only [D.path_isolated chosen i hi, Idle.colors] using hz
  · rw [MatchingLayer.unitOf, dif_neg hi, unitPrimitive, Primitive.colors]
    simp only [path, dif_neg hi] at hz
    exact Switch.path_color_mem _ _ _ hz

theorem path_interior_reservoir {RV RC : Set G}
    (hgood : ∀ u, (D.unitPrimitive u).Good RV RC (L.unitQuery input output u))
    (chosen : List (α × α)) (i : α) {z : G}
    (hz : z ∈ (D.path chosen i).interior) : z ∈ RV :=
  (hgood (L.unitOf i)).interior_mem (D.path_interior_unitPrimitive chosen i hz)

theorem path_color_reservoir {RV RC : Set G}
    (hgood : ∀ u, (D.unitPrimitive u).Good RV RC (L.unitQuery input output u))
    (chosen : List (α × α)) (i : α) {z : G}
    (hz : z ∈ (D.path chosen i).colors (fun a b : G => b-a)) : z ∈ RC :=
  (hgood (L.unitOf i)).color_mem (D.path_color_unitPrimitive chosen i hz)

end LayerGeometry

variable {n : ℕ} {input intermediate output : Fin n → G}
variable {first : LayerGeometry (firstMatchingLayer n) input intermediate}
variable {second : LayerGeometry (secondMatchingLayer n) intermediate output}

namespace TwoLayerGood

theorem route_interiors_mem {RV RC : Set G} (h : TwoLayerGood RV RC first second)
    (hm : ∀ i, intermediate i ∈ RV) (f s : List (Fin n × Fin n))
    (hf : f.Sublist (firstLayer n)) :
    ∀ i z, z ∈ (installedRoutes first second f s i).interior → z ∈ RV := by
  intro i z hz
  rw [installedRoutes_interior_eq first second f s hf i] at hz
  simp only [List.mem_append, List.mem_singleton] at hz
  rcases hz with (hz | hz) | hz
  · exact first.path_interior_reservoir h.1 f i hz
  · exact hz ▸ hm _
  · exact second.path_interior_reservoir h.2 s _ hz

theorem route_colors_mem {RV RC : Set G} (h : TwoLayerGood RV RC first second)
    (f s : List (Fin n × Fin n)) (hf : f.Sublist (firstLayer n))
    (hs : s.Sublist (secondLayer n)) :
    ∀ i c, c ∈ (installedRoutes first second f s i).colors (fun a b : G => b-a) → c ∈ RC := by
  intro i c hc
  rw [installedRoutes_colors_eq first second f s hf hs i] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact first.path_color_reservoir h.1 f i hc
  · exact second.path_color_reservoir h.2 s _ hc

theorem fixed_interiors_mem {RV RC : Set G} (h : TwoLayerGood RV RC first second)
    (hm : ∀ i, intermediate i ∈ RV) :
    ∀ z ∈ fixedInteriorFinset first second, z ∈ RV := by
  intro z hz
  obtain ⟨i, hi⟩ := (mem_routeInteriorFinset first second [] [] z).mp hz
  exact h.route_interiors_mem hm [] [] (List.nil_sublist _) i z hi

theorem fixed_colors_mem {RV RC : Set G} (h : TwoLayerGood RV RC first second) :
    ∀ c ∈ fixedColorFinset first second, c ∈ RC := by
  intro c hc
  obtain ⟨i, hi⟩ := (mem_routeColorFinset first second [] [] c).mp hc
  exact h.route_colors_mem [] [] (List.nil_sublist _) (List.nil_sublist _) i c hi

end TwoLayerGood
end
end EndpointRouter
